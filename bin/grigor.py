import sys
import lark
from lark import Lark, Transformer, Token, Tree
from typing import Dict, Union, List, Optional

# ----------------------------------------------------------------------
# 1. LARK GRAMMAR FOR GRIGOR
# ----------------------------------------------------------------------
# This grammar covers terms, types, declarations, and modules.
# It's a concrete syntax following the specification.
# We use `?` for optional parts, `*` for repetitions, and `|` for alternatives.
# Some parts are simplified for parsing; the full grammar would be larger.

GRIGOR_GRAMMAR = r"""
    // --- Token imports (must be first) ---
    %import common.WS
    %import common.CPP_COMMENT
    %ignore WS
    %ignore CPP_COMMENT

    // Custom string pattern for file paths
    STRING: /"[^"]*"/

    start: top_decl*

    // Top-level declarations
    ?top_decl: inductive_decl
             | fixpoint_decl
             | axiom_decl
             | theorem_decl
             | definition_decl
             | module_decl
             | module_type_decl
             | include_decl
             | import_decl

    // Inductive types
    inductive_decl: "Inductive" IDENT (binder)* ":" term ":=" ( "|" IDENT ":" term )* "."
    // Example: Inductive nat : Set := | zero : nat | succ : nat -> nat.

    // Fixpoint (recursive function)
    fixpoint_decl: "Fixpoint" IDENT binder+ "{" "struct" IDENT "}" ":" term ":=" term "."
    // Example: Fixpoint plus (n m : nat) {struct n} : nat := ...

    // Axiom
    axiom_decl: "Axiom" IDENT ":" term "."

    // Theorem
    theorem_decl: "Theorem" IDENT ":" term ":=" term "."

    // Definition
    definition_decl: "Definition" IDENT binder* ":" term ":=" term "."

    // Module and module types (simplified)
    module_decl: "Module" IDENT (binder)* (":" module_type)? ":=" module_expr "."
    module_type_decl: "Module" "Type" IDENT (binder)* ":=" module_type_body "."
    module_type_body: "sig" declaration* "end"   // we reuse top_decl inside sig
    module_expr: IDENT                                         -> module_ref
               | IDENT "(" module_arg ("," module_arg)* ")"   -> module_apply
               | "struct" declaration* "end"                   -> module_struct
    module_type: IDENT
               | "functor" "(" binder ("," binder)* ")" "=>" module_type
               | "sig" declaration* "end"
               | module_type "with" IDENT ":=" term
    include_decl: "Include" module_expr "."
    import_decl: "Import" import_source "."?
    
    import_source: STRING | module_expr

    ?declaration: top_decl

    module_arg: term   // for simplicity, treat as term; in reality can be module or term

    // Binders
    binder: simple_binder
          | typed_binder
          | implicit_binder
    
    simple_binder: IDENT
    typed_binder: IDENT ":" term
                | "(" IDENT+ ":" term ")"
    implicit_binder: "{" IDENT "}"

    // Terms and types (unified)
    // Precedence (lowest to highest):
    // forall, fun, ->, application, atoms
    // We'll use a few levels.
    ?term: forall_term
         | fun_term
         | arrow_term

    ?arrow_term: app_term ("->" arrow_term)?
    ?app_term: atom_term+

    sort: "Prop"               -> prop_sort
        | "Set"               -> set_sort
        | "Type"              -> type_sort
        | "Type" "(" IDENT ")" -> type_idx_sort

    ?atom_term: "(" term ")"
              | sort
              | "let" IDENT binder* ":=" term "in" term
              | "match" term ("as" IDENT)? ("in" term)? ("return" term)? "with" ("|" pattern "=>" term)+ "end"
              | "fix" IDENT binder+ "{" "struct" IDENT "}" ":=" term
              | "cofix" IDENT binder+ ":=" term
              | "(" term "," term ")"
              | "fst" term
              | "snd" term
              | "pack" term term
              | "unpack" term "as" "(" IDENT "," IDENT ")" "in" term
              | "explode" term term
              | IDENT   // variable or constant (including refl, J, etc.)

    ?forall_term: "forall" binder+ "," term
    ?fun_term: "fun" binder+ "=>" term

    // Pattern for match
    pattern: IDENT                    // variable
           | "(" IDENT "," IDENT ")"  // pair
           | IDENT pattern+           // constructor pattern

    // Identifier
    IDENT: /[a-zA-Z_][a-zA-Z0-9_]*/
"""

# ----------------------------------------------------------------------
# 2. AST BUILDER (Transformer)
# ----------------------------------------------------------------------
# Transforms parse tree into a simpler Python representation.
# We'll define a small set of AST nodes as dicts or tuples.

class ASTBuilder(Transformer):
    def start(self, items):
        return items  # list of top-level decls

    def IDENT(self, tok):
        return ("ident", str(tok))

    def term(self, children):
        # If only one child, return it; otherwise list?
        # In Lark, rule `?term: ...` inlines alternatives, so term() receives the result of the chosen alternative directly.
        # But if we have multiple children from an alternative, we need to handle them.
        # We'll define each alternative as a method.
        return children[0] if children else None

    # Universe sorts (via grammar aliases)
    def prop_sort(self, _): return ("sort", "Prop")
    def set_sort(self, _): return ("sort", "Set")
    def type_sort(self, _): return ("sort", "Type", None)
    def type_idx_sort(self, children): return ("sort", "Type", children[0])

    # forall
    def forall_term(self, children):
        binders = []
        i = 0
        while i < len(children) and self._is_binder(children[i]):
            binders.append(children[i])
            i += 1
        binders = self._expand_binders(binders)
        body = children[-1]
        return ("forall", binders, body)

    # fun
    def fun_term(self, children):
        binders = []
        i = 0
        while i < len(children) and self._is_binder(children[i]):
            binders.append(children[i])
            i += 1
        binders = self._expand_binders(binders)
        body = children[-1]
        return ("fun", binders, body)

    # arrow: "?" rule is only called when both sides are present;
    # anonymous "->" is filtered so children = [left, right]
    def arrow_term(self, children):
        return ("arrow", children[0], children[1])

    # application
    def app_term(self, children):
        # left-associative accumulation
        result = children[0]
        for t in children[1:]:
            result = ("app", result, t)
        return result

    # binder
    def binder(self, children):
        # Dispatch to the sub-rule's handler
        return children[0]
    
    def simple_binder(self, children):
        # Single IDENT, untyped
        name = children[0][1]  # children[0] is ('ident', name)
        return ("binder", name, None)
    
    def typed_binder(self, children):
        # IDENT ":" term or (IDENT+ ":" term)
        # All children except the last are identifiers, last is type
        idents = []
        for child in children[:-1]:
            if isinstance(child, tuple) and child[0] == 'ident':
                idents.append(child[1])
        typ = children[-1]
        
        if len(idents) == 1:
            return ("binder", idents[0], typ)
        else:
            return ("binder_group", idents, typ)
    
    def implicit_binder(self, children):
        # {IDENT}
        name = children[0][1]  # children[0] is ('ident', name)
        return ("binder", name, None)  # For now, treat implicit same as untyped
        return None

    # match
    def match_expr(self, children):
        # children: term, (as ident)?, (in term)?, (return term)?, (with pattern=>term+)
        # For simplicity, we'll just capture the raw tree
        return ("match", children)

    # patterns: ignore for now, pass as is
    def pattern(self, children):
        return children

    # Let
    def let_expr(self, children):
        # let IDENT binder* := term in term
        name = children[0][1]
        # binders after name: children[1] if present, else empty
        binders = []
        i = 1
        while i < len(children) and isinstance(children[i], dict):
            binders.append(children[i])
            i += 1
        # after binders, should be ":=" term "in" term
        # tricky because of optional binder list; we'll assume fixed structure: name, binder*, := term in term
        # We'll rely on lark's grammar to parse correctly.
        # For simplicity, we won't implement detailed let; we'll just store children list.
        return ("let", children)

    def _is_binder(self, x):
        return isinstance(x, tuple) and len(x) >= 1 and x[0] in ('binder', 'binder_group')
    
    def _expand_binders(self, binders):
        """Expand binder_group items into individual binders"""
        expanded = []
        for b in binders:
            if b[0] == 'binder_group':
                # binder_group: (identifier_list, type)
                for ident in b[1]:
                    expanded.append(('binder', ident, b[2]))
            else:
                expanded.append(b)
        return expanded

    # inductive declaration
    def inductive_decl(self, children):
        name = children[0][1]
        params = []
        i = 1
        while i < len(children) and self._is_binder(children[i]):
            params.append(children[i])
            i += 1
        # i now points to term (the type/arity); anonymous ":" and ":=" are filtered
        ind_type = children[i]
        i += 1
        # remaining items are alternating ctor_name, ctor_type pairs ("|" filtered out)
        ctor_items = children[i:]
        constructors = [
            ("constructor", ctor_items[j][1], ctor_items[j+1])
            for j in range(0, len(ctor_items), 2)
        ]
        return ("inductive", name, params, ind_type, constructors)

    # fixpoint
    def fixpoint_decl(self, children):
        # after filtering: [name, *binders, struct_IDENT, type, body]
        name = children[0][1]
        binders = []
        i = 1
        while i < len(children) and self._is_binder(children[i]):
            binders.append(children[i])
            i += 1
        struct = children[i][1]    # struct IDENT (anonymous "{", "struct", "}" filtered)
        typ = children[i+1]
        body = children[i+2]
        return ("fixpoint", name, binders, struct, typ, body)

    # theorem, axiom, definition
    def theorem_decl(self, children):
        # after filtering: [name, *binders, type, body]
        return ("theorem", children[0][1], children[-2], children[-1])
    def axiom_decl(self, children):
        # after filtering: [name, type]
        return ("axiom", children[0][1], children[1])
    def definition_decl(self, children):
        # after filtering: [name, *binders, type, body]
        return ("definition", children[0][1], children[-2], children[-1])

    # modules (simplified)
    def module_decl(self, children):
        # after filtering: [name, *binders, [module_type], module_expr]
        name = children[0][1]
        binders = []
        i = 1
        while i < len(children) and self._is_binder(children[i]):
            binders.append(children[i])
            i += 1
        body = children[-1]
        mtype = children[i] if i < len(children) - 1 else None
        return ("module", name, binders, mtype, body)

    def module_type_decl(self, children):
        name = children[0][1]
        binders = children[1:-1]  # simplified
        body = children[-1]
        return ("module_type", name, binders, body)

    def struct_body(self, children):
        return ("struct", children)

    def include_decl(self, children):
        return ("include", children[0])

    def import_decl(self, children):
        # children[0] is the import_source result
        source = children[0]
        if isinstance(source, str):
            # It's a file path (STRING)
            return ("import_string", source)
        else:
            # It's a module_expr
            return ("import", source)

    def import_source(self, children):
        # children[0] is either a STRING Token or a module_expr
        if isinstance(children[0], Token):
            # STRING Token: extract value and remove quotes
            string_val = children[0].value
            path = string_val[1:-1]  # remove quotes
            return path
        else:
            # module_expr
            return children[0]

    def module_ref(self, children):
        return ("module_ref", children[0][1])

    def module_apply(self, children):
        return ("module_apply", children[0][1], children[1:])

    def module_struct(self, children):
        return ("module_struct", children)

    # Default for other rules
    def __default__(self, data, children, meta):
        return Tree(data, children)


# ----------------------------------------------------------------------
# 3. REFEREE (TYPE CHECKER) — Simplified
# ----------------------------------------------------------------------
# This referee does basic type checking for a dependent type theory subset:
# - Universes Prop, Set, Type(i)
# - Dependent products (forall) and lambdas
# - Application
# - Variables
# - Inductive types as constants (no match checking yet)
# - Environment with module namespaces
# It is not complete, but demonstrates the structure.

class TypeChecker:
    def __init__(self):
        self.env = {}  # global env: name -> type (and possibly body for definitions)
        self.modules = {}  # module name -> env

    def check_decl(self, decl):
        """Process a top-level declaration and update env."""
        kind = decl[0]
        if kind == "axiom":
            name, typ = decl[1], decl[2]
            self.env[name] = typ
        elif kind == "theorem" or kind == "definition":
            name, typ, body = decl[1], decl[2], decl[3]
            # For simplicity, assume type is correct
            self.env[name] = typ
        elif kind == "inductive":
            # Add type constructor and constructors with their types
            name, params, ind_type, ctors = decl[1], decl[2], decl[3], decl[4]
            # ind_type is the sort of the inductive (e.g., Set, Prop)
            # We add the inductive as a type with arity params -> ind_type
            # and each constructor as a function.
            # For simplicity, we ignore params for now.
            self.env[name] = ind_type  # as a type constant
            for ctor in ctors:
                # ctor is ("constructor", name_str, type_term)
                ctor_name = ctor[1]
                ctor_type = ctor[2]
                self.env[ctor_name] = ctor_type
        elif kind == "fixpoint":
            name, binders, struct, typ, body = decl[1:]
            self.env[name] = typ
        elif kind == "module":
            name, binders, mtype, body = decl[1:]
            sub_checker = TypeChecker()
            if isinstance(body, tuple) and body[0] == "module_struct":
                for subdecl in body[1]:
                    sub_checker.check_decl(subdecl)
            self.modules[name] = sub_checker.env
            self.env[name] = ("module", sub_checker.env)
        elif kind == "module_type":
            name = decl[1]
            self.env[name] = ("module_type", name)
        # Include and import not implemented

    def infer(self, term, ctx=None):
        """Simple type inference. Returns type or raises error."""
        if ctx is None:
            ctx = {}
        if term[0] == "ident":
            name = term[1]
            # look in context, then global env
            if name in ctx:
                return ctx[name]
            if name in self.env:
                return self.env[name]
            raise TypeError(f"Unbound variable: {name}")
        elif term[0] == "sort":
            # Universe hierarchy: Prop : Type(0), Set : Type(0), Type(i) : Type(i+1)
            kind = term[1]
            if kind == "Prop" or kind == "Set":
                return ("sort", "Type", None)  # Type(0)
            elif kind == "Type":
                idx = term[2]
                if idx is None:
                    return ("sort", "Type", 1)  # Type(0) : Type(1)
                return ("sort", "Type", idx+1)
            else:
                raise TypeError("Invalid sort")
        elif term[0] == "forall":
            binders = term[1]
            body = term[2]
            # Build pi type: for each binder, compute type of binder (if annotated) else infer from later?
            # For simplicity, require full annotations in forall.
            # In dependent product, the return type can depend on the binder.
            # We'll simplify: treat all binders as having their type; body is a type.
            # Return sort of the whole product: if body is a sort, product is that sort.
            body_type = self.infer(body, ctx)
            if body_type[0] != "sort":
                raise TypeError("forall body must be a sort")
            return body_type  # simplified: all pi types share the same sort as body
        elif term[0] == "fun":
            binders = term[1]
            body = term[2]
            # For lambda, we need to check that body type matches the binder types.
            # We'll just construct a function type: (x:A) -> B where B is body type.
            # We need binder types. They must be annotated (since we cannot infer).
            # For simplicity, assume all binders are annotated.
            ctx2 = ctx.copy()
            for b in binders:
                if b[2] is None:
                    raise TypeError("Lambda binder without type annotation not supported")
                b_type = b[2]
                # Evaluate the type to ensure it's a sort?
                # We'll just add the variable with its type to context.
                ctx2[b[1]] = b_type
            body_type = self.infer(body, ctx2)
            # Construct the overall function type
            result_type = body_type
            # Build nested forall type from binders + result
            for b in reversed(binders):
                result_type = ("forall", [b], result_type)
            return result_type
        elif term[0] == "app":
            func = term[1]
            arg = term[2]
            func_type = self.infer(func, ctx)
            # func_type should be a forall (or arrow)
            if func_type[0] != "forall" and func_type[0] != "arrow":
                raise TypeError("Applying a non-function")
            # For simplicity, we only handle non-dependent arrow (where binder type is same as domain)
            # In dependent case, we would need substitution.
            # We'll extract the binder's type and return the codomain.
            if func_type[0] == "arrow":
                domain = func_type[1]
                codomain = func_type[2]
            else:
                # forall with one binder? Might have multiple.
                binders = func_type[1]
                if len(binders) != 1:
                    raise TypeError("Multiple binders not supported in app")
                domain = binders[0][2]  # binder type
                codomain = func_type[2]  # body
            arg_type = self.infer(arg, ctx)
            if not self.convertible(domain, arg_type):
                raise TypeError(f"Type mismatch: expected {domain}, got {arg_type}")
            return codomain  # naive: no substitution
        elif term[0] == "arrow":
            # Non-dependent function type A -> B; type is sort of B
            right_type = self.infer(term[2], ctx)
            if right_type[0] != "sort":
                raise TypeError("arrow codomain must be a sort")
            return right_type
        elif term[0] == "let":
            raise NotImplementedError("Let not supported yet")
        elif term[0] == "match":
            raise NotImplementedError("Match not supported yet")
        else:
            raise NotImplementedError(f"Term not supported: {term}")

    def convertible(self, t1, t2):
        """Check if two types are equal (simple structural equality)."""
        # In a real checker, this would consider definitional equality.
        return t1 == t2


# ----------------------------------------------------------------------
# 4. FILE LOADER
# ----------------------------------------------------------------------
import os

def load_and_check(filepath, checker=None, loaded=None):
    """Parse and type-check a .rig source file. Recursively handles imports. Returns True on success."""
    if loaded is None:
        loaded = set()
    if checker is None:
        checker = TypeChecker()
    
    # Normalize path to avoid duplicates
    abs_path = os.path.abspath(filepath)
    if abs_path in loaded:
        return True  # already loaded
    loaded.add(abs_path)
    
    parser = Lark(GRIGOR_GRAMMAR, parser="lalr", transformer=ASTBuilder())
    try:
        with open(abs_path) as f:
            src = f.read()
    except OSError as e:
        print(f"error: {e}")
        return False
    try:
        tree = parser.parse(src)
    except Exception as e:
        print(f"parse error in {filepath}:\n  {e}")
        return False
    
    # First pass: process all imports recursively
    for decl in tree:
        if decl[0] == "import_string":
            import_path = decl[1]
            # Resolve relative to the current file's directory
            import_full_path = os.path.join(os.path.dirname(abs_path), import_path)
            if not load_and_check(import_full_path, checker, loaded):
                return False
    
    # Second pass: type-check all non-import declarations
    for decl in tree:
        if decl[0] == "import_string":
            continue  # skip imports on second pass
        try:
            checker.check_decl(decl)
        except Exception as e:
            print(f"type error in {filepath} ({decl}):\n  {e}")
            return False
    print(f"OK  {filepath}  ({len(tree)} declaration(s))")
    return True


# ----------------------------------------------------------------------
# 5. MAIN (PARSER + REFEREE DEMO)
# ----------------------------------------------------------------------
def main():
    if len(sys.argv) >= 2:
        ok = load_and_check(sys.argv[1])
        sys.exit(0 if ok else 1)

    # Build parser
    parser = Lark(GRIGOR_GRAMMAR, parser="lalr", transformer=ASTBuilder())
    # Example input (a simple module)
    test_input = """
    Module Type NAT_ARITH := sig
      Axiom zero : Prop.
    end.

    Module PeanoArith : NAT_ARITH := struct
      Axiom zero : Prop.
    end.
    """
    # Parse
    try:
        tree = parser.parse(test_input)
        print("Parse successful!")
        print("AST:", tree.pretty() if hasattr(tree, 'pretty') else tree)
    except Exception as e:
        import traceback
        traceback.print_exc()
        print("Parse error:", e)
        return

    # Use referee
    checker = TypeChecker()
    # Go through top-level declarations and check
    for decl in tree:
        print("Processing decl:", decl)
        checker.check_decl(decl)
    print("Environment:", checker.env)

    # Simple type inference test
    # We'll manually create terms because we haven't implemented full AST processing for complex inputs.
    # But we can demonstrate with internal representation.
    print("\nTesting type inference:")
    # Example: type of Prop -> Prop
    t1 = ("arrow", ("sort", "Prop"), ("sort", "Prop"))
    try:
        inferred = checker.infer(t1)
        print(f"Type of Prop -> Prop: {inferred}")
    except Exception as e:
        print("Error:", e)

if __name__ == "__main__":
    main()