# LoVe Lecture 10: Denotational Semantics

We review a third way to specify the semantics of a programming language: denotational semantics

Denotational semantics attempts to directly specify the semantics of programs


## Motivation

A _denotational semantics_ defines the meaning of each program as a mathematical object:

    ⟦ ⟧ : syntax → semantics

A key property of denotational semantics is _compositionality_: The meaning of a compound statement should be defined in terms of the meaning of its components

This disqualifies

    ⟦c⟧ = {st | (c, st.1) ⟹ st.2}

because operational semantics are not defined in a compositional way

In short, we want:

    ⟦c ; c'⟧              = … ⟦c⟧ … ⟦c'⟧ …
    ⟦if b then c else c'⟧ = … ⟦c⟧ … ⟦c'⟧ …
    ⟦while b do c⟧        = … ⟦c⟧ …

An evaluation function on arithmetic expressions (`eval : aexp → ((string → ℤ) → ℤ)`) is a denotational semantics; now we want the same for imperative programs

We can represent the semantics of an imperative program as a function from initial state to final state or more generally as a relation between initial state and final state

From the operational semantics we can derive a relation of type `state × state → Prop`

We represent this as a mathematical object by collecting the pairs in a set

For `skip`, `:=`, `;`, and `ite`, the denotational semantics is easy:

    def den : program → set (state × state)
    | skip          := Id state
    | (assign n a)  := {x | x.2 = x.1{n ↦ a x.1}}
    | (seq S₁ S₂)   := den S₁ ◯ den S₂
    | (ite b S₁ S₂) := (den S₁ ⇃ b) ∪ (den S₂ ⇃ λs, ¬ b s)

We write `⟦S⟧` for `den S`

For `while`, we would like to write:

    | (while b S)   := ((den S ◯ den (while b S)) ⇃ b) ∪ (Id state ⇃ λs, ¬ b s)

but this is not well founded due to the unmodified recursive call to `while b S`

What we are looking for is a solution for `X` in the equation

    X = ((den S ◯ X) ◯ c) ∪ (Id state ◯ λs, ¬ c s))

In other words, we are looking for a fixpoint

The rest of this lecture is concerned with building a fixpoint operator `lfp` that will allow us to define the while case as well:

    | (while b p) := lfp (λX, ((den p ◯ X) ◯ b) ∪ (Id state ◯ λs, ¬ b s))


## Fixpoints

A _fixpoint_ (or _fixed point_) of `f` is a solution for `X` in the equation

    X = f X

In general, fixpoints may not exist at all (cf. `f = nat.succ`) or there may be many different fixpoints (cf. `f = id`)

But under some conditions on `f`, a (unique) _least fixpoint_ and a _greatest fixpoint_ are guaranteed to exist

Consider this _fixpoint equation_:

    X = (λ(p : ℕ → Prop) (n : ℕ), n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ p m) X
      = λn : ℕ, n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ X m

where `X : ℕ → Prop` and `f = λ(p : ℕ → Prop) (n : ℕ), n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ p m`

The above example admits only one fixpoint; the fixpoint equation uniquely specifies `X` as the set of even numbers

In general, the least and greatest fixpoint may be different:

    X = id X
      = X

Here, the least fixpoint is `(λ_, False)` and the greatest fixpoint is `(λ_, True)`

Conventionally, `False < True`, and thus `(λ_, False) < (λ_, True)`

Similarly, `∅ < @set.univ α` if `α` is inhabited

**Key observation**: Inductive predicates correspond to least fixpoints, but they are built into Lean's logic (the calculus of inductive constructions)

We used this observation when we defined the operational semantics as an inductive data type


## Least Fixpoints

For the semantics of programming languages:

* `X` will have type `set (state × state)` (or e.g. `state → state → Prop`), representing relations between states

* `f` will correspond to either taking one extra iteration of the loop (if the condition `b` is true) or the identity (if `b` is false)

_Kleene fixpoint theorem_: `f^0(∅) ∪ f^1(∅) ∪ f^2(∅) ∪ ... = lfp f`

The **least fixpoint** corresponds to **finite executions** of a program, which is all we care about


## Monotone Functions

Let `α` and `β` be types with partial order `≤`

A function `f : α → β` is _monotone_ if

    a ≤ b → f a ≤ f b    for all a, b

Many operations on sets (e.g. `∪`), relations (e.g. `◯`), and functions (e.g. `const`) are monotone

The set of monotone functions is also well behaved: The identity function is monotone, the composition of monotone functions is again monotone, etc.

All monotone functions `f : α → α`, where `α` is a **complete lattice**, admit least and greatest fixpoints

### Example for a nonmonotone function on sets

          ⎧  s ∪ {a}     if a ∉ s
    f s = ⎨
          ⎩  ∅           otherwise

so `∅ ⊆ {a}`, but `f ∅ = {a} ⊈ ∅ = f {a}`


## Complete Lattices

To define the (least) fixpoints on sets, we only need one operation: intersection `⋂`

*Complete lattices* capture this concept abstractly

A complete lattice `α` is an ordered type for which each `set α` has an infimum

A complete lattice consists of: a partial order `≤ : α → α → Prop` (i.e. reflexive, transitive, and antisymmetric), and an operator `⨅ : set α → α`, called *infimum*, or *greatest lower bound* (*glb*)

`⨅s` satisfies (and is unique such that):

* `⨅s` is a lower bound of `s`:

      `⨅s ≤ b`  for all `b ∈ s`

* `⨅s` is the greatest lower bound:

      `b ≤ ⨅s`  for all `b`, s.t. `∀x∈s, b ≤ x`

**Warning:** `⨅s` is not necessarily an element of `s`

`set α` is an instance w.r.t. `⊆` and `⋂` for all types `α`

`Prop` is an instance w.r.t. `→` and `∀`, i.e. `⨅s := ∀p ∈ s, p`

We define:

    lfp f  :=  ⨅{x | f x ≤ x}

_Knaster-Tarski theorem_: for any monotone function `f`:

* `lfp f` is a fixpoint: `lfp f = f (lfp f)`

* `lfp f` is smaller than any other fixpoint: `X = f X → lfp f ≤ X`

### Finite Example

                X            ⨅{}           = ?
              /   \          ⨅{X}          = ?
             A     B         ⨅{A, B}       = ?
              \   /          ⨅{X, A}       = ?
                Y            ⨅{X, A, B, Y} = ?

### Other Examples

    enat := ℕ ∪ {∞}
    ereal := ℝ ∪ {- ∞, ∞}
    …

For `α` a complete lattice, then also `β → α` is a complete lattice

For `α`, `β` complete lattices, then also `α × β` is a complete lattice

### Non-Examples

* `ℕ`, `ℤ`, `ℚ`, `ℝ`: no infimum for `∅`, `⨅ℕ`, etc.

* `erat := ℚ ∪ {- ∞, ∞}`, for example `⨅{q | 2 < q * q} = sqrt 2` is not in `ℚ`


## Demo

[`love10_denotational_semantics_demo.lean`](../lean/love10_denotational_semantics_demo.lean)
