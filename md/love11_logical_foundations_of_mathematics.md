# LoVe Lecture 11: Logical Foundations of Mathematics

We dive deeper into the logical foundations of Lean


## Type universes

Not only terms have a type, but also types have a type

For example, according the the Curry-Howard correspondence (PAT principle):

    @and.intro : ∀a b, a → b → a ∧ b

In this sense, `∀a b, a → b → a ∧ b` is a type, which in turn is of type `Prop`:

    ∀a b, a → b → a ∧ b : Prop

What is the type of `Prop`?
`Prop` has the same type as virtually all other types we
have constructed so far, namely `Type`:

    Prop : Type
    ℕ : Type

What is the type of `Type`?

The typing `Type : Type` would lead to a contradiction,
called Girard's paradox, resembling Russel's paradox

    Type : Type 1
    Type 1 : Type 2
    Type 2 : Type 3
    ⋮

Aliases:

* In fact, `Type` is an abbreviation for `Type 0`

* We can also write `Sort 0` for `Prop` and `Sort (u + 1)` for `Type u`

Terminology:

* `Sort u`, `Type u` and `Prop` are called (*type*) *universes*

* The `u` in the expression `Sort u` is a *universe level*

The hierarchy is captured by the following typing judgment:

    —————————————————————————————————— Sort
    Γ ⊢ Sort u : Sort (u + 1)


## The Peculiarities of Prop

`Prop` is different from the other type universes!

### Impredicativity

The function type `σ → τ` is put into the larger one of the
type universes that `σ` and `τ` live in :

    Γ ⊢ σ : Type u    Γ ⊢ τ : Type v
    —————————————————————————————————— Pi₀
    Γ ⊢ σ → τ : Type (max u v)

For dependent types this generalizes to:

    Γ ⊢ σ : Type u    Γ, x : σ ⊢ τ[x] : Type v
    —————————————————————————————————————————————— Pi₁
    Γ ⊢ (Пx : σ, τ[x]) : Type (max u v)

This behavior of the universes `Type v` is called *predicativity*

To force expressions such as `∀p : Prop, p → p`
(which is the same as `Пp : Prop, p → p`)
to be of type `Prop` anyway, we have as special typing rule for `Prop`:

    Γ ⊢ σ : Sort u    x : σ ⊢ τ[x] : Prop
    ———————————————————————————————————————— Pi₂
    Γ ⊢ Пx : σ, τ[x] : Prop

This behavior of `Prop` is called *impredicativity*

The rules `Pi₀`, `Pi₁`, and `Pi₂` can be generalized into one rule:

    Γ ⊢ σ : Sort u    Γ, x : σ ⊢ τ[x] : Sort v
    ————————————————————————————————————————— Pi
    Γ ⊢ Пx : σ, τ[x] : Sort (imax u v)

where

    imax u 0 = 0
    imax u v = max u v   if v ≠ 0

In other systems, such as Agda, all type universes are predicative

### Proof Irrelevance

A second difference between `Prop` and `Type u` is *proof irrelevance*:

    ∀(p : Prop) (h₁ h₂ : p), h₁ = h₂

This is called _proof irrelevance_ and makes reasoning about dependent types easier

When viewing a proposition as a type and a proof as an element of that
type, proof irrelevance means that a proposition is either an empty type or has
exactly one inhabitant

Proof irrelevance can be proved `by refl`

In contrast:

* Agda and Coq are _proof relevant_ by default (but are compatible with proof irrelevance)

* Homotopy type theory and other _constructive_ or _intuitionistic_ type theories build on data in equality proofs and therefore are incompatible with proof irrelevance

### Large and Small Elimination

A further difference between `Prop` and `Type u` is that `Prop` does not allow
*large elimination*, meaning that it impossible to extract data from a proof of
a proposition

This is necessary to allow proof irrelevance


## The Axiom of Choice

Consider the following inductive predicate:

    inductive nonempty (α : Sort u) : Prop
    | intro (val : α) : nonempty

The predicate states that `α` has at least one element

To prove `nonempty α`, we must provide an element of `α` to the `intro` rule:

    lemma nat.nonempty :
      nonempty ℕ :=
    nonempty.intro 0

Since `nonempty` lives in `Prop`, large elimination is not available, and
thus we cannot extract the element that was used from a proof of
`nonempty α`

The axiom of choice allows us to obtain some element of type `α` if we can
show `nonempty α`:

    axiom classical.choice {α : Sort u} :
      nonempty α → α

It will just give us an arbitrary element of `α`; we have no way of knowing whether this is the element that was used to prove `nonempty α`

The constant `classical.choice` is noncomputable,
one of the reasons why some logicians prefer to work without this axiom

This principle is not built into the
Lean kernel; it is only an axiom in Lean's core library, giving users the
freedom to work with or without it


## Subtypes

Subtyping is a mechanism to create new types from existing ones

Given a predicate on the elements of the original type,
the new type contains only those elements of the original type
that fulfill this property

**Example 1.** Subtype of full binary trees:

    def full_btree (α : Type) : Type :=
    { t : btree α // is_full t }


**Example 2.** Subtype of lists of a given length:

    def vector (α : Type u) (n : ℕ) : Type :=
    { l : list α // l.length = n }


## Quotient Types

Quotients are a powerful construction in mathematics used to construct `ℤ`, `ℚ`, `ℝ`, and many other types

Just like subtypes, quotient types construct a new type
from an existing type

Unlike a subtype, a quotient type contains all of the
elements of the underlying type, but some elements that were different in the
underlying type are considered equal in the quotient type

To define a quotient type, we need to provide a type that it is derived from
and a equivalence relation on it that determines which elements are considered equal

**Example:** The integers `ℤ`

Quotient over pairs of natural numbers `ℕ × ℕ`

A pair `(m, n)` of natural numbers represents the integer `m - n`
* Nonnegative integers `m` can be represented by `(m, 0)`
* Negative integers `-n` can be represented by `(0, n)`
* Many representations of the same integer, e.g., `(2, 1)`,
`(3, 2)`, and `(4, 3)` all represent the integer `1`

Which equivalence relation can we use?
* We want two pairs `(k, l)` and `(m, n)` to
be equal when `k - l` and `m - n` yield the same integer
* The condition `k - l = m - n` does not work because the negation on `ℕ` does
not behave like the negation on integers, e.g., `0 - 1 = 0`
* Instead, we use the condition `k + n = m + l`, which contains only addition


## Demo

[`love11_logical_foundations_of_mathematics_demo.lean`](../lean/love11_logical_foundations_of_mathematics_demo.lean)
