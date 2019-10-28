# LoVe Lecture 1: Definitions and Lemma Statements

We introduce the basics of Lean and proof assistants, without trying to carry out actual proofs yet

We focus on specifying objects and statements of their intended properties


## Proof Assistants

Also called _interactive theorem provers_

They

* check and help develop formal proofs
* can be used to prove big theorems, not only logic puzzles
* can be tedious to use
* are highly addictive (think video games)


## Success Stories

Mathematics:

* the Mizar Math Library (in Mizar)
* the four-color theorem (in Coq)
* the odd-order theorem (in Coq)
* the Kepler conjecture (in HOL Light and Isabelle/HOL)
* the homotopy type theory libraries (in Agda, Coq, and Lean)
* the Lorenz attractor (in Isabelle/HOL)

Computer science:

* hardware and systems (e.g., floating-point arithmetic, microkernels, hardware memory models)
* process calculi and programming language theory (e.g., semantics, software memory models, type systems, binder syntax)
* program analysis (e.g., compilers, interpreters, static analyzers)
* security (e.g., cryptographic protocols, cryptography, information flow)


## Kinds of Proofs

_Formal proof_ = proof expressed in a logical formalism, often developed using a proof assistant

_Informal proof_ = pen-and-paper (or LaTeX) proof

_Rigorous proof_ = thorough informal proof

> Too many proofs look more like LSD trips than coherent mathematical arguments


## Logical Foundations

Three main (families of) logical foundations:

* set theory
* simple type theory (= higher-order logic)
* **dependent type theory**


## A Selection of Proof Assistants

Classified by logical foundations:

* set theory: Isabelle/ZF, Metamath, Mizar
* simple type theory: HOL4, HOL Light, Isabelle/HOL
* dependent type theory: Agda, Coq, **Lean**, Matita, PVS

Hard to classify: ACL2 (Lisp-like first-order logic)

Pioneering system: AUTOMATH (by Nicolaas de Bruijn)


## Lean

A new proof assistant developed primarily by [Leonardo de Moura](https://www.microsoft.com/en-us/research/people/leonardo/) (Microsoft Research) since 2013

Its mathematical library, `mathlib`, is developed under the leadership of [Jeremy Avigad](http://www.andrew.cmu.edu/user/avigad/) (Carnegie Mellon University)

* we use **version 3.4.1** (likely the last release before Lean 4)
* we use its basic libraries and `mathlib`
* Lean is a research project, with some rough edges

Strengths:

* highly expressive logic based on a dependent type theory called the _calculus of_ (_inductive_) _constructions_, abbreviated _CIC_ or _CoC_
* extended with classical axioms and quotient types
* metaprogramming framework (to program custom proof automation)
* modern user interface
* documentation
* open source

Lean at VU Amsterdam:

* [Lean Forward](https://lean-forward.github.io) project (2019–2023)


## About This Course

[Web site](https://lean-forward.github.io/logical-verification/2019/index.html)

[Installation instructions](https://lean-forward.github.io/logical-verification/2019/index.html#installation)

[Repository](https://github.com/blanchette/logical_verification_2019) (for [lecture notes](https://github.com/blanchette/logical_verification_2019/blob/master/logical_verification_in_lean.pdf), "slides", exercises, and homework)


## A View of Lean

In a first approximation:

> Lean = typed functional programming + logic

In this lecture, we cover inductive types, recursive functions, and lemma statements

If you are not familiar with typed functional programming (e.g., Haskell, ML, OCaml, Scala), we recommend that you study a tutorial, such as [_Learn You a Haskell for Great Good!_](http://learnyouahaskell.com/chapters)


## Types and Terms

Similar to simply typed λ-calculus or typed functional programming languages (ML, OCaml, Haskell)

Types `σ`, `τ`:

* type variables `α`
* basic types `T`
* complex types `T σ1 … σN`

Some type constructors `T` are written infix, e.g., `→` (function type)

Function arrow is right-associative: `σ1 → σ2 → σ3 → τ` = `σ1 → (σ2 → (σ3 → τ))`

In Lean, type variables must be bound using `Π` or its alias `∀`, e.g., `Πα, α → α`

Terms `t`, `u`:

* variables `x`
* applications `t u`
* λ-abstractions `λx, t`

**Currying**: functions can be

* fully applied (e.g., `f x y z` if `f` is ternary)
* partially applied (e.g., `f x y`; `f x`)
* left unapplied (`f`)

Application is left-associative: `f x y z` = `((f x) y) z`


## Type Inference and Type Checking

Type checking and type inference are decidable problems, but this property is quickly lost if features such as overloading or subtyping are added

The type inference algorithm, based on unification, is due to Hindley and Milner

Type judgment: `Γ ⊢ t : σ`, meaning `t` has type `σ` in context `Γ`

    —————————— Cst   if c is declared with type σ
    Γ ⊢ c : σ

    Γ ⊢ t : σ → τ    Γ ⊢ u : σ
    ——————————————————————————— App
    Γ ⊢ t u : τ

    Γ, x : σ ⊢ t : τ
    ———————————————————————— Lam
    Γ ⊢ (λx : σ, t) : σ → τ

    —————————— Var   if x : σ occurs in Γ
    Γ ⊢ x : σ

Horizontal bars denote derivation rules in a [formal system](https://en.wikipedia.org/wiki/Formal_system)

Type annotations `t : σ` can be used to guide type inference

_Higher-order types_: types containing left-nested `→` arrows, e.g., `(σ → σ) → σ`, corresponding to functions passed as arguments


## Type Definitions

An _inductive type_ (also called _inductive datatype_, _algebraic datatype_, or just _datatype_) is a type that consists all the values that can be built using a finite number of applications of its _constructors_, and only those

Definition of type `nat` (= `ℕ`) of natural numbers (in Peano-style unary notation):

    inductive nat : Type
    | zero : nat
    | succ : nat → nat

A type `aexp` of arithmetic expressions:

    inductive aexp
    | num : ℤ → aexp
    | var : string → aexp
    | add : aexp → aexp → aexp
    | sub : aexp → aexp → aexp
    | mul : aexp → aexp → aexp
    | div : aexp → aexp → aexp


## Function Definitions

The syntax for defining a function operating on an inductive type is very compact: We define a single function and use _pattern matching_ to extract the arguments to the constructors

Examples:

    def add : ℕ → ℕ → ℕ
    | m nat.zero     := m
    | m (nat.succ n) := nat.succ (add m n)

    def eval (env : string → ℤ) : aexp → ℤ
    | (aexp.num i)    := i
    | (aexp.var x)    := env x
    | (aexp.add e₁ e₂) := eval e₁ + eval e₂
    | (aexp.sub e₁ e₂) := eval e₁ - eval e₂
    | (aexp.mul e₁ e₂) := eval e₁ * eval e₂
    | (aexp.div e₁ e₂) := eval e₁ / eval e₂

We can have pattern matching without recursion (e.g., in the `num` and `var` cases)

We can have also have recursion without pattern matching

_Primitive recursion_ is when we peel off exactly one constructor from the value on which we recurse

Lean only accepts the function definitions for which it can prove termination


## Lemma Statements

Examples:

    lemma add_comm (m n : ℕ) :
      add m n = add n m :=
    sorry

    lemma add_assoc (l m n : ℕ) :
      add (add l m) n = add l (add m n) :=
    sorry


## Demo

[`love01_definitions_and_lemma_statements_demo.lean`](../lean/love01_definitions_and_lemma_statements_demo.lean)
