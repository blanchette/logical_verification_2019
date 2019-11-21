# LoVe Lecture 3: Structured Proofs and Proof Terms

When developing a proof, often it makes sense to work forward: to start with what we already know and proceed step by step towards our goal

Structured proofs are a style that supports this reasoning

Structured proofs are syntactic sugar sprinkled on top of Lean's proof terms: All proofs, whether tactical or structured, are reduced internally to proof terms


## Structured Proofs

### Lemma Name

The simplest kind of structured proof is the name of a lemma, possibly with arguments

### `assume`

* `assume` _name1_ ... _nameN_

Moves variables or assumptions from the goal into the local context

Can be seen as a structured version of the `intros` tactic

### `have`

* `have` _name_ `:` _proposition_ `:=` _proof_

Proves an intermediate lemma statement, which can refer to the local context

Often we put a `_` placeholder for _proposition_, when it can be inferred from the proof

### `let`

* `let` _name_ `:` _type_ `:=` _term_ `in`

Introduces a new local definition

It is similar to `have` but for computable data

Folding or unfolding a `let` corresponds to ζ-conversion

### `show` _proposition_

* `show` _proposition_`,` `from` _structured-proof_
* `show` _proposition_`,` `begin` _tactics_ `end`
* `show` _proposition_`,` `by` _tactic_

Repeats the goal to prove

Useful for documentation purposes or to rephrase the goal in an equal form up to computation


## Calculational Proofs

In informal mathematics, we often use transitive chains of equalities, inequalities, or equivalences (e.g., `a ≥ b ≥ c`)

In Lean, such calculational proofs are supported by `calc`

It provides a nice syntax and takes care of transitivity

Syntax:

> `calc` _expr0_ _op1_ _expr1_ `:` _proof1_
>
> `...` _op2_ _expr2_ `:` _proof2_
>
>  ⋮
>
> `...` _opN_ _exprN_ `:` _proofN_

The horizontal dots (`...`) are part of the syntax


## Induction by Pattern Matching

As alternative to the `induction` tactic, induction can also be done by pattern matching:

 * the induction hypothesis is then available under the name of the lemma we are proving

 * well-foundedness of the argument is often proved automatically

A few hints on how to carry out proofs by induction:

 * perform induction following the structure of the definition of one of the functions appearing in the goal

 * if the base case (e.g., `0`, `[]`) of an induction is difficult, this is a sign the wrong variable was chosen or some lemmas are missing


## Dependent Types

Dependent types are the definining feature of the _dependent type theory_ family of logics

Consider a function `pick` that take a natural number (`ℕ` = {0, 1, 2, ...}) and that returns a natural number between 0 and `x`

Conceptually, `pick` has a dependent type, namely `(x : ℕ) → {y : ℕ // y ≤ x}`

(The `{` ... `//` ... `}` syntax denotes a subtype; we will come back to these later)

We can think of this type as a `ℕ`-indexed family, where each member's type may depend on the index: `pick x : {y : ℕ // y ≤ x}`

But a type may also depend on another type, e.g., `list` (or `λα, list α`) and `λα, α → α`

A term may depend on a type, e.g., `λα, λx : α, x` (a polymorphic identity function)

Of course, a term may also depend on a term

Unless otherwise specified, _dependent type_ often means a type depending on a *term*, like the above; this is what we mean when we say that simple type theory does not support dependent types

In summary, there are four cases for `λx, t` in the calculus of inductive constructions:

Body (`t`) |              | Argument (`x`) | Description
---------- | ------------ | -------------- | -----------
A term     | depending on | a term         | Simply typed λ-abstraction
A type     | depending on | a term         | Dependent type (stricto senso)
A term     | depending on | a type         | Polymorphic term
A type     | depending on | a type         | Type constructor

The last three rows correspond to the three axes of Barendregt's [λ-cube](https://en.wikipedia.org/wiki/Lambda_cube)

Revised typing rules:

    Γ ⊢ t : (x : σ) → τ[x]    Γ ⊢ u : σ
    ———————————————————————————————————— App'
    Γ ⊢ t u : τ[u]

    Γ, x : σ ⊢ t : τ[x]
    ———————————————————————————————— Lam'
    Γ ⊢ (λx : σ, t) : (x : σ) → τ[x]

These two rules degenerate to `App` and `Lam` if `x` does not occur in `τ[x]`

Example of `App'`:

    ⊢ pick : (x : ℕ) → {y : ℕ // y ≤ x}    ⊢ 5 : ℕ
    ——————————————————————————————————————————————— App'
    ⊢ pick 5 : {y : ℕ // y ≤ 5}

Example of `Lam'`:

    α : Type, x : α ⊢ x : α
    ——————————————————————————————— Lam or Lam'
    α : Type ⊢ (λx : α, x) : α → α
    ————————————————————————————————————————————— Lam'
    ⊢ (λα : Type, λx : α, x) : (α : Type) → α → α


**Regrettably**, the intuitive syntax `(x : σ) → τ` is not available in Lean; instead, we must write `Πx : σ, τ` or `∀x : σ, τ` to specify a dependent type

Aliases:

> `σ → τ` := `Π_ : σ, τ`
>
> `∀` := `Π`


## Curry–Howard(–De Bruijn) Correspondence

`→` is used both as the implication symbol and as the type constructor of functions

Similarly, `∀` is used both as a quantifier and to specify dependent types

It turns out that not only the two pairs of concepts look the same, they are the same, by the PAT principle:

* **PAT = propositions as types**
* **PAT = proofs as terms**

Also called Curry–Howard correspondence

De Bruijn, Curry, Howard, and possibly others independently noticed that in dependent type theory:

* propositions are isomorphic to types
* proofs are isomorphic to terms

Hence, we _identify_ proofs and terms as well as propositions and types

Let us go through the _dramatis personae_ slowly

Types:

* `σ → τ` is the type of (total) functions from `σ` to `τ`
* `Πx : σ, τ[x]` is the dependent type from `x : σ` to `τ[x]`

Propositions:

* `φ → ψ` can be read as "`φ` implies `ψ`", or as the type of functions mapping proofs of `φ` to proofs of `ψ`
* `∀x : σ, ψ[x]` can be read as "for all `x`, `ψ[x]`", or as the type of functions mapping values `x` of type `σ` to proofs of `ψ[x]`
* `∀h : φ, ψ[h]` is the type of functions mapping proofs `h` of `φ` to proofs of `ψ[h]`

Terms:

* declared constants are terms
* `t u` is the application of function `t` to value `u`
* `λx, t[x]` is a function mapping `x` to `t[x]`

Proofs:

* a lemma name is a term
* `l a`, which instantiates the leading parameter or quantifier of lemma `l` with value `a`, is a proof term
* `l l'`, which discharges the leading assumption of `l` with lemma `l'`, is a proof term; this is called _modus ponens_
* given `h[n] : φ[n]`, we have that `λn : σ, h[n]` is a proof term for `∀n : σ, φ[n]`
* given `h[h'] : φ[h']`, we have that `λh' : ψ, h[h']` is a proof term for `∀h' : ψ, φ[h']`

By the Curry–Howard correspondence, a proof by induction is the same as a recursively specified proof term; this explains why, in a proof by pattern matching, the induction hypothesis is named after the lemma

In the same way, well-founded (or strong) induction is the same as well-founded recursion; Lean's termination checker is used to prove well-foundedness of the proof by induction

`def` and `lemma` are almost the same, but `lemma` considers the proof term (or whatever defined term) opaque, whereas `def` keeps it transparent

Since proofs are irrelevant to Lean’s logic, there is no need to store them or unfold them later

A similar difference is visible between `let` and `have`


## Demo

[`love03_structured_proofs_and_proof_terms_demo.lean`](../lean/love03_structured_proofs_and_proof_terms_demo.lean)
