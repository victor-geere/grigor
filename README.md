# Grigor — A Fully Explicit Dependently Typed Proof Language

Grigor is a proof language based on the Calculus of Inductive Constructions (CIC). It is designed for expressing mathematical theorems and their proofs as explicit, machine-checkable terms. Every proof is a lambda term verified by a type checker; there are no tactics, no automation, and no hidden implicit arguments. The language uses only printable ASCII characters (US-101 keyboard), making it accessible anywhere.

## Table of Contents

1. [Lexical conventions](#1-lexical-conventions)
2. [Grammar](#2-grammar)
3. [Universes](#3-universes)
4. [Typing rules](#4-typing-rules)
5. [Induction and case analysis](#5-induction-and-case-analysis)
6. [The module system](#6-the-module-system)
7. [Standard library](#7-standard-library)
8. [Examples](#8-examples)
9. [Running the checker](#9-running-the-checker)
10. [Why "Grigor"?](#10-why-grigor)

---

## 1. Lexical conventions

- **Identifiers** consist of a letter or underscore followed by any mix of letters, digits, and underscores: `/[a-zA-Z_][a-zA-Z0-9_]*/`
- **Reserved words:** `Prop`, `Set`, `Type`, `fun`, `forall`, `match`, `with`, `end`, `as`, `in`, `return`, `fix`, `cofix`, `let`, `refl`, `J`, `fst`, `snd`, `pack`, `unpack`, `explode`, `Inductive`, `Fixpoint`, `Axiom`, `Theorem`, `Definition`, `Module`, `Include`, `Import`, `struct`, `sig`, `functor`
- **Comments:** `// line comment` (rest of line is ignored)
- **Punctuation:** `.` terminates every top-level declaration, `:=` introduces a body, `:` introduces a type annotation

---

## 2. Grammar

### 2.1 Terms and types

```
term ::= forall binder+ , term           -- dependent product
       | fun binder+ => term             -- lambda abstraction
       | app_term -> term                -- non-dependent function type (right-associative)
       | app_term                        -- application (left-associative)

app_term ::= atom+                       -- juxtaposition = application

atom ::= ( term )                        -- grouping
       | Prop | Set | Type               -- universes
       | Type ( ident )                  -- indexed universe
       | ident                           -- variable or constant
       | ( term , term )                 -- dependent pair introduction
       | fst atom                        -- first projection
       | snd atom                        -- second projection
       | pack atom atom                  -- existential introduction
       | refl atom                       -- reflexivity proof
       | J atom atom atom atom atom      -- equality eliminator
       | explode atom atom               -- ex falso
       | fun binder+ => term             -- lambda (as atom only inside parens)
       | forall binder+ , term           -- product (as atom only inside parens)
       | let ident binder* := term in term
       | match term (as ident)? (in term)? (return term)?
           with ( | pattern => term )+ end
       | fix ident binder+ { struct ident } := term
       | cofix ident binder+ := term
       | unpack term as ( ident , ident ) in term
```

### 2.2 Binders

```
binder ::= ident                    -- untyped variable
         | ( ident : term )         -- typed variable
         | { ident }                -- implicit (marked but not inferred)
```

### 2.3 Patterns

```
pattern ::= ident                   -- variable / wildcard
          | ( ident , ident )       -- pair pattern
          | ident pattern+          -- constructor applied to sub-patterns
```

### 2.4 Top-level declarations

Every declaration ends with a `.`

```
decl ::= Inductive ident binder* : term := ( | ident : term )* .
       | Fixpoint ident binder+ { struct ident } : term := term .
       | Axiom ident : term .
       | Theorem ident : term := term .
       | Definition ident binder* : term := term .
       | Module ident binder* ( : module_type )? := module_expr .
       | Module Type ident binder* := sig decl* end .
       | Include module_expr .
       | Import module_expr .
```

### 2.5 Module expressions and types

```
module_expr ::= ident                                   -- module reference
              | ident ( module_arg (, module_arg)* )    -- functor application
              | struct decl* end                         -- inline structure

module_type ::= ident                                   -- named signature
              | functor ( binder (, binder)* ) => module_type
              | sig decl* end                            -- inline signature
              | module_type with ident := term           -- signature refinement

module_arg ::= term
```

---

## 3. Universes

Grigor has a cumulative hierarchy of universes:

| Universe  | Type of        |
|-----------|----------------|
| `Prop`    | Propositions — proof-irrelevant |
| `Set`     | Small data types (nat, bool, list …) |
| `Type`    | Large types |
| `Type(i)` | Level-indexed universe, `Type(i) : Type(i+1)` |

Subtyping: `Prop ≤ Set ≤ Type ≤ Type(1) ≤ …`

**`Prop`** — The type of propositions. A proof of proposition `A` is simply a term of type `A`. There is no distinction between a proposition and the type of its proofs.

**`Set`** — The type of small, computational data types. Values of `Set` types can be used in extraction.

**`Type(i)`** — Used for type constructors and large structures. `Type` without an index is shorthand for an unconstrained level.

---

## 4. Typing rules

The typing judgement `Γ ⊢ t : A` reads "term `t` has type `A` under context `Γ`".

### 4.1 Variable
```
x : A ∈ Γ
────────── (Var)
Γ ⊢ x : A
```

### 4.2 Dependent product (forall)
```
Γ ⊢ A : s₁    Γ, x : A ⊢ B : s₂
──────────────────────────────── (Prod)
Γ ⊢ forall (x : A), B : s₃

s₃ = Prop  if s₂ = Prop,  else max(s₁, s₂)
```

### 4.3 Lambda
```
Γ, x : A ⊢ t : B
──────────────────────────────────── (Lam)
Γ ⊢ fun (x : A) => t : forall (x : A), B
```

### 4.4 Application
```
Γ ⊢ f : forall (x : A), B    Γ ⊢ u : A
──────────────────────────────────────── (App)
Γ ⊢ f u : B[u/x]
```

### 4.5 Let
```
Γ ⊢ u : A    Γ, x := u : A ⊢ t : B
──────────────────────────────────── (Let)
Γ ⊢ let x := u in t : B
```

### 4.6 Inductive definitions

An inductive declaration `Inductive I binder* : arity := | c₁ : T₁ | …` must satisfy **strict positivity**. It adds `I` and each constructor `cᵢ` to the global environment with their declared types.

The match eliminator has type:
```
match t as x in I params return P x with
| c₁ a₁ … => b₁  ...
end  :  P t
```
where `P` is a function from `I params` to some sort `s`, and each branch body `bᵢ` has type `P (cᵢ aᵢ …)`.

### 4.7 Fixpoint

`Fixpoint f binder+ { struct x } : B := t` is well-typed when:

- `f : forall binder+, B` is in scope inside `t`
- Every recursive call `f v …` in `t` applies `f` to a structurally smaller subterm of `x`

`cofix` is the co-recursive dual; it requires that recursive calls are always guarded by a constructor.

### 4.8 Equality

Equality is the built-in inductive family:
```
Inductive eq (A : Type) (x : A) : A -> Prop :=
  | refl : eq A x x.
```

The term `refl t` constructs a proof that `t` equals itself. The eliminator `J` allows rewriting along equalities:
```
J : forall (A : Type) (x : A)
      (P : forall (y : A), eq A x y -> Prop),
      P x (refl x) ->
      forall (y : A) (e : eq A x y), P y e
```

### 4.9 Definitional equality

Types are compared up to **definitional equality**, which includes:

| Rule  | Reduction |
|-------|-----------|
| β     | `(fun (x : A) => t) u  ↝  t[u/x]` |
| ι     | `match cᵢ args … with … | cᵢ pat => b | … end  ↝  b[args/pat]` |
| δ     | unfold a named `Definition` or `let` |
| η     | `fun (x : A) => f x  ↝  f`  (when `x` not free in `f`) |

---

## 5. Induction and case analysis

The `match` construct supports **dependent** case analysis:

```
match t as x in I params return P x with
| c₁ a₁ a₂ => b₁
| c₂ a₃    => b₂
end
```

- `as x` binds the scrutinee `t` to `x` in the return clause
- `in I params` names the inductive family and its parameters
- `return P x` specifies the return type; `P` must have type `I params -> s`
- Each branch binds the constructor arguments and must produce a term of type `P (cᵢ …)`
- The type of the whole expression is `P t`

---

## 6. The module system

### 6.1 Module definitions

```
Module Name binder* : Sig := struct
  decl*
end.
```

- `Name` is the module identifier
- Binders introduce module-level parameters (functors)
- `: Sig` is optional; if given, the body must satisfy the signature
- The body is a `module_expr`: a reference, a functor application, or an inline `struct … end`

### 6.2 Module types (signatures)

```
Module Type SigName binder* := sig
  decl*
end.
```

A signature lists the declarations that a conforming module must provide. Declarations inside `sig … end` use the same syntax as top-level declarations.

### 6.3 Functor application

```
Module M := F(A)(B).
```

Applies functor `F` to arguments `A` and `B`, yielding a new module with the instantiated definitions.

### 6.4 `Include` and `Import`

```
Include M.    // copies all declarations from M into the current scope
Import M.     // makes M's names directly visible without the M. prefix
```

### 6.5 Signature refinement (`with`)

```
module_type with X := some_term
```

Replaces all occurrences of `X` in `module_type` with `some_term`, producing a more specific signature.

---

## 7. Standard library

The built-in environment provides only the primitives listed below. Everything else must be defined by the user.

| Name      | Type                                   | Description |
|-----------|----------------------------------------|-------------|
| `Prop`    | `Type`                                 | Universe of propositions |
| `Set`     | `Type`                                 | Universe of small types |
| `Type`    | `Type`                                 | Universe of large types |
| `eq`      | `forall (A : Type) (x : A), A -> Prop` | Propositional equality |
| `refl`    | `forall (A : Type) (x : A), eq A x x` | Reflexivity constructor |
| `J`       | (see §4.8)                             | Equality eliminator |
| `False`   | `Prop`                                 | Empty proposition |
| `explode` | `forall (A : Prop), False -> A`        | Ex falso quodlibet |

---

## 8. Examples

### 8.1 Natural numbers and addition

```grigor
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint plus (n : nat) (m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem plus_O_n : forall (n : nat), plus O n = n :=
  fun (n : nat) => refl n.
```

### 8.2 Lists

```grigor
Inductive list (A : Type) : Type :=
  | nil  : list A
  | cons : A -> list A -> list A.

Fixpoint append (A : Type) (l : list A) (m : list A) {struct l} : list A :=
  match l with
  | nil       => m
  | cons a l' => cons A a (append A l' m)
  end.
```

### 8.3 Modules — a minimal arithmetic signature

```grigor
Module Type NAT_ARITH := sig
  Axiom zero : Prop.
end.

Module PeanoArith : NAT_ARITH := struct
  Axiom zero : Prop.
end.
```

### 8.4 Dependent pairs

```grigor
// pack t u  builds a Σ-type value  (t, u)
// unpack p as (a, b) in ...  destructs it

Definition swap (A : Type) (B : Type) (p : A) : B :=
  unpack p as (a, b) in pack b a.
```

---

## 9. Running the checker

The reference implementation requires Python 3 and the `lark` parsing library.

```bash
cd bin
python3 grigor.py
```

To check a Grigor source file, invoke the parser with your file as input (see `bin/grigor.py` for the entry point). The checker reads declarations top-to-bottom, builds the global environment, and type-checks every theorem. If a proof term does not match its declared type the checker prints an error and stops.

**Dependencies** (see `bin/requirements.txt`):
```
lark
```

Install with:
```bash
python3 -m venv bin/.venv
source bin/.venv/bin/activate
pip install -r bin/requirements.txt
```

---

## 10. Why "Grigor"?

The name blends the personal name *Grigor* with *rigour*. It reflects the language's uncompromising demand for exactness: every proof must be a fully-formed term, and the checker is an unforgiving referee.
