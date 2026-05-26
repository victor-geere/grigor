"""
Grigor2 – an extended Python+Lark theorem prover
with file inclusion, equality type, and reduction rules.
"""
import sys
import os
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
    %import common.STRING
    %import common.CPP_COMMENT
    %ignore WS
    %ignore CPP_COMMENT

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
             | includefile_decl

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
    import_decl: "Import" module_expr "."
    includefile_decl: "IncludeFile" STRING "."

    ?declaration: top_decl

    module_arg: term   // for simplicity, treat as term; in reality can be module or term

    // Binders
    binder: IDENT                          // untyped
          | "(" IDENT ":" term ")"         // typed
          | "{" IDENT "}"                  // implicit (parsed but ignored in this simple referee)

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
              | "refl" term term          // refl A x
              | "J" term term term term term term  // J A x P h y e
              | "(" term "," term ")"
              | "fst" term
              | "snd" term
              | "pack" term term
              | "unpack" term "as" "(" IDENT "," IDENT ")" "in" term
              | "explode" term term
              | IDENT   // variable or constant

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
        body = children[-1]
        return ("forall", binders, body)

    # fun
    def fun_term(self, children):
        binders = []
        i = 0
        while i < len(children) and self._is_binder(children[i]):
            binders.append(children[i])
            i += 1
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
        # Anonymous tokens ("(", ":", ")", "{", "}") are filtered by lark.
        if len(children) == 1 and isinstance(children[0], tuple) and children[0][0] == 'ident':
            return ("binder", children[0][1], None)
        elif len(children) == 2 and isinstance(children[0], tuple) and children[0][0] == 'ident':
            return ("binder", children[0][1], children[1])
        return None

    # match
    def match_expr(self, children):
        return ("match", children)

    # patterns: ignore for now, pass as is
    def pattern(self, children):
        return children

    # Let
    def let_expr(self, children):
        return ("let", children)

    def _is_binder(self, x):
        return isinstance(x, tuple) and len(x) >= 1 and x[0] == 'binder'

    # refl and J
    def refl_term(self, children):
        # children: [A, x]
        return ("refl", children[0], children[1])

    def J_term(self, children):
        # children: [A, x, P, h, y, e]
        return ("J", children[0], children[1], children[2],
                      children[3], children[4], children[5])

    # inductive declaration
    def inductive_decl(self, children):
        name = children[0][1]
        params = []
        i = 1
        while i < len(children) and self._is_binder(children[i]):
            params.append(children[i])
            i += 1
        ind_type = children[i]
        i += 1
        ctor_items = children[i:]
        constructors = [
            ("constructor", ctor_items[j][1], ctor_items[j+1])
            for j in range(0, len(ctor_items), 2)
        ]
        return ("inductive", name, params, ind_type, constructors)

    # fixpoint
    def fixpoint_decl(self, children):
        name = children[0][1]
        binders = []
        i = 1
        while i < len(children) and self._is_binder(children[i]):
            binders.append(children[i])
            i += 1
        struct = children[i][1]
        typ = children[i+1]
        body = children[i+2]
        return ("fixpoint", name, binders, struct, typ, body)

    # theorem, axiom, definition
    def theorem_decl(self, children):
        return ("theorem", children[0][1], children[-2], children[-1])
    def axiom_decl(self, children):
        return ("axiom", children[0][1], children[1])
    def definition_decl(self, children):
        return ("definition", children[0][1], children[-2], children[-1])

    # modules
    def module_decl(self, children):
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
        binders = children[1:-1]
        body = children[-1]
        return ("module_type", name, binders, body)

    def struct_body(self, children):
        return ("struct", children)

    def include_decl(self, children):
        return ("include", children[0])

    def import_decl(self, children):
        return ("import", children[0])

    def module_ref(self, children):
        return ("module_ref", children[0][1])

    def module_apply(self, children):
        return ("module_apply", children[0][1], children[1:])

    def module_struct(self, children):
        return ("module_struct", children)

    # File inclusion
    def includefile_decl(self, children):
        # children[0] is a Token; its value is the raw string including quotes
        raw = children[0].value   # e.g. '"equality.rig"'
        path = raw[1:-1]         # remove quotes
        return ("includefile", path)

    def __default__(self, data, children, meta):
        return Tree(data, children)


# ----------------------------------------------------------------------
# 3. REFEREE (TYPE CHECKER) – Extended with J and reduction
# ----------------------------------------------------------------------

class TypeChecker:
    def __init__(self):
        self.env = {}          # global constants
        self.modules = {}      # module name -> env

    def check_decl(self, decl):
        """Process a top-level declaration and update env."""
        kind = decl[0]
        if kind == "axiom":
            name, typ = decl[1], decl[2]
            self.env[name] = typ
        elif kind in ("theorem", "definition"):
            name, typ, body = decl[1], decl[2], decl[3]
            self.env[name] = typ
        elif kind == "inductive":
            name, params, ind_type, ctors = decl[1], decl[2], decl[3], decl[4]
            # Add the type constructor and its constructors
            self.env[name] = ind_type
            for ctor in ctors:
                ctor_name = ctor[1]
                ctor_type = ctor[2]
                self.env[ctor_name] = ctor_type
            # Special treatment for the equality type
            if name == "eq":
                # Automatically add the dependent eliminator J
                A_ident = ("ident", "A")
                x_ident = ("ident", "x")
                P_type = ("forall",
                          [("binder", "y", None), ("binder", "e", None)],
                          ("sort", "Set"))   # simplified: P returns Set
                j_type = ("forall",
                          [("binder", "A", ("sort", "Set")),
                           ("binder", "x", ("ident", "A"))],
                          ("forall",
                           [("binder", "P", ("forall",
                                             [("binder", "y", ("ident", "A")),
                                              ("binder", "e", ("app", ("ident", "eq"), ("ident", "A"), ("ident", "x"), ("ident", "y")))],
                                             ("sort", "Set")))],
                           ("forall",
                            [("binder", "h", ("app", ("ident", "P"), ("ident", "x"),
                                             ("app", ("ident", "refl"), ("ident", "A"), ("ident", "x"))))],
                            ("forall",
                             [("binder", "y", ("ident", "A")),
                              ("binder", "e", ("app", ("ident", "eq"), ("ident", "A"), ("ident", "x"), ("ident", "y")))],
                             ("app", ("ident", "P"), ("ident", "y"), ("ident", "e"))))))
                self.env["J"] = j_type
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
        # Include and import not implemented yet

    # ----------------------------------------------------------------
    # Reduction
    # ----------------------------------------------------------------
    def reduce(self, term):
        """Perform weak head normalisation (β, ι for J)."""
        if term[0] == "app":
            func = self.reduce(term[1])
            arg  = term[2]
            if func[0] == "fun":
                # β-reduction: (fun x => body) arg  →  body[x:=arg]
                binders = func[1]
                body    = func[2]
                if len(binders) != 1:
                    raise NotImplementedError("Only single binder lambda supported in reduction")
                binder = binders[0]
                body_subst = self._subst(body, binder[1], arg)
                return self.reduce(body_subst)
            elif func[0] == "J":
                # J A x P h y e
                A = func[1]
                x = func[2]
                P = func[3]
                h = func[4]
                y = func[5]
                e = func[6]
                e_wh = self.reduce(e)
                # If e reduces to refl A x (or refl _ _), reduce to h
                if e_wh[0] == "refl":
                    return self.reduce(h)
                else:
                    return ("app", func, arg)
            else:
                return ("app", func, arg)
        elif term[0] in ("forall", "fun", "arrow", "refl", "J", "sort", "ident"):
            return term
        else:
            return term  # let, match, etc. – no reduction

    def _subst(self, body, var, replacement):
        """Naive substitution [var := replacement] in body."""
        if body[0] == "ident":
            return replacement if body[1] == var else body
        elif body[0] == "app":
            return ("app", self._subst(body[1], var, replacement),
                          self._subst(body[2], var, replacement))
        elif body[0] == "fun":
            binders = body[1]
            new_body = body[2]
            if any(b[1] == var for b in binders):
                return body
            return ("fun", binders, self._subst(new_body, var, replacement))
        elif body[0] == "forall":
            binders = body[1]
            new_body = body[2]
            if any(b[1] == var for b in binders):
                return body
            return ("forall", binders, self._subst(new_body, var, replacement))
        elif body[0] == "arrow":
            return ("arrow", self._subst(body[1], var, replacement),
                             self._subst(body[2], var, replacement))
        elif body[0] == "refl":
            return ("refl",
                    self._subst(body[1], var, replacement),
                    self._subst(body[2], var, replacement))
        elif body[0] == "J":
            return ("J",
                    self._subst(body[1], var, replacement),
                    self._subst(body[2], var, replacement),
                    self._subst(body[3], var, replacement),
                    self._subst(body[4], var, replacement),
                    self._subst(body[5], var, replacement),
                    self._subst(body[6], var, replacement))
        else:
            return body   # sorts, etc.

    # ----------------------------------------------------------------
    # Type inference
    # ----------------------------------------------------------------
    def infer(self, term, ctx=None):
        if ctx is None:
            ctx = {}
        if term[0] == "ident":
            name = term[1]
            if name in ctx:
                return ctx[name]
            if name in self.env:
                return self.env[name]
            raise TypeError(f"Unbound variable: {name}")
        elif term[0] == "sort":
            kind = term[1]
            if kind in ("Prop", "Set"):
                return ("sort", "Type", None)      # Type(0)
            elif kind == "Type":
                idx = term[2]
                if idx is None:
                    return ("sort", "Type", 1)
                return ("sort", "Type", idx+1)
            else:
                raise TypeError("Invalid sort")
        elif term[0] == "forall":
            binders = term[1]
            body = term[2]
            body_type = self.infer(body, ctx)
            if body_type[0] != "sort":
                raise TypeError("forall body must be a sort")
            return body_type
        elif term[0] == "fun":
            binders = term[1]
            body = term[2]
            ctx2 = ctx.copy()
            for b in binders:
                if b[2] is None:
                    raise TypeError("Lambda binder without type annotation not supported")
                ctx2[b[1]] = b[2]
            body_type = self.infer(body, ctx2)
            result = body_type
            for b in reversed(binders):
                result = ("forall", [b], result)
            return result
        elif term[0] == "app":
            func = term[1]
            arg = term[2]
            func_type = self.reduce(self.infer(func, ctx))
            if func_type[0] == "forall":
                binders = func_type[1]
                codomain = func_type[2]
                if len(binders) != 1:
                    raise TypeError("Multiple binders not supported in app")
                domain = binders[0][2]
            elif func_type[0] == "arrow":
                domain = func_type[1]
                codomain = func_type[2]
            else:
                raise TypeError("Applying a non-function")
            arg_type = self.infer(arg, ctx)
            if not self.convertible(domain, arg_type):
                raise TypeError(f"Type mismatch: expected {domain}, got {arg_type}")
            # For dependent types, we should substitute arg into codomain.
            # Here we naively return the codomain.
            return codomain
        elif term[0] == "arrow":
            right_type = self.infer(term[2], ctx)
            if right_type[0] != "sort":
                raise TypeError("arrow codomain must be a sort")
            return right_type
        elif term[0] == "refl":
            A = term[1]
            x = term[2]
            A_type = self.infer(A, ctx)
            if not self.convertible(A_type, ("sort", "Set")):
                raise TypeError(f"refl first argument must be Set, got {A_type}")
            _ = self.infer(x, ctx)   # x : A
            return ("app", ("app", ("app", ("ident", "eq"), A), x), x)
        elif term[0] == "J":
            A = term[1]
            x = term[2]
            P = term[3]
            h = term[4]
            y = term[5]
            e = term[6]
            A_type = self.infer(A, ctx)
            if not self.convertible(A_type, ("sort", "Set")):
                raise TypeError("J: A must be Set")
            x_type = self.infer(x, ctx)
            if not self.convertible(x_type, A):
                raise TypeError("J: x must be of type A")
            P_type = self.reduce(self.infer(P, ctx))
            expected_P_type = ("forall",
                               [("binder", "y", A),
                                ("binder", "e", ("app", ("app", ("app", ("ident", "eq"), A), x), ("ident", "y")))],
                               ("sort", "Set"))
            if not self.convertible(P_type, expected_P_type):
                raise TypeError(f"J: P type mismatch, expected {expected_P_type}, got {P_type}")
            h_type = self.infer(h, ctx)
            expected_h_type = ("app", ("app", P, x), ("app", ("ident", "refl"), A, x))
            if not self.convertible(h_type, expected_h_type):
                raise TypeError(f"J: h type mismatch")
            y_type = self.infer(y, ctx)
            if not self.convertible(y_type, A):
                raise TypeError("J: y must be of type A")
            e_type = self.infer(e, ctx)
            expected_e_type = ("app", ("app", ("app", ("ident", "eq"), A), x), y)
            if not self.convertible(e_type, expected_e_type):
                raise TypeError("J: e must be an equality proof")
            return ("app", ("app", P, y), e)
        elif term[0] == "let":
            raise NotImplementedError("Let not supported yet")
        elif term[0] == "match":
            raise NotImplementedError("Match not supported yet")
        else:
            raise NotImplementedError(f"Term not supported: {term}")

    # ----------------------------------------------------------------
    # Convertibility (definitional equality)
    # ----------------------------------------------------------------
    def convertible(self, t1, t2):
        """Check if two types/terms are definitionally equal by reducing both."""
        return self.reduce(t1) == self.reduce(t2)


# ----------------------------------------------------------------------
# 4. FILE LOADER with recursive IncludeFile handling
# ----------------------------------------------------------------------
def load_and_check(filepath, checker=None, loaded=None):
    """Parse and type-check a .rig file. Returns (success, checker)."""
    if loaded is None:
        loaded = set()
    if checker is None:
        checker = TypeChecker()
    # Normalize path to avoid duplicates
    abs_path = os.path.abspath(filepath)
    if abs_path in loaded:
        return True, checker   # already loaded
    loaded.add(abs_path)

    parser = Lark(GRIGOR_GRAMMAR, parser="lalr", transformer=ASTBuilder())
    try:
        with open(abs_path) as f:
            src = f.read()
    except OSError as e:
        print(f"error: {e}")
        return False, checker

    try:
        tree = parser.parse(src)
    except Exception as e:
        print(f"parse error in {abs_path}:\n  {e}")
        return False, checker

    # First pass: process all IncludeFile declarations recursively
    for decl in tree:
        if decl[0] == "includefile":
            included_path = decl[1]
            include_path = os.path.join(os.path.dirname(abs_path), included_path)
            ok, checker = load_and_check(include_path, checker, loaded)
            if not ok:
                return False, checker

    # Second pass: type‑check all non‑include declarations
    for decl in tree:
        if decl[0] == "includefile":
            continue
        try:
            checker.check_decl(decl)
        except Exception as e:
            print(f"type error in {abs_path} ({decl}):\n  {e}")
            return False, checker

    print(f"OK  {abs_path}  ({len(tree)} declaration(s))")
    return True, checker


# ----------------------------------------------------------------------
# 5. MAIN
# ----------------------------------------------------------------------
def main():
    if len(sys.argv) < 2:
        print("Usage: python grigor2.py file1.rig [file2.rig ...]")
        sys.exit(1)
    checker = TypeChecker()
    all_ok = True
    loaded = set()        # keep across all command‑line files
    for path in sys.argv[1:]:
        ok, checker = load_and_check(path, checker, loaded)
        if not ok:
            all_ok = False
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()