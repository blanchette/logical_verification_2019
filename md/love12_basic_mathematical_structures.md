# LoVe Lecture 12: Basic Mathematical Structures

Today we introduce definitions and proofs about basic mathematical structures


## Type Classes

A type class is a collection of abstract constants and their properties 

A type can be declared an instance of a type class by providing concrete definitions for the constants and proving that the properties hold

We have seen some examples of type classes already:
* `is_associative` / `is_commutative`
* `lawful_monad`
* `complete_lattice`
* `setoid`

The syntax to define a type class is

    class name_of_type_class (α : Type) :=
    (constant₁ : type_of_constant₁)
    (constant₂ : type_of_constant₂)
    ⋮
    (property₁ : statement_of_property₁)
    (property₂ : statement_of_property₂)
    ⋮

To instantiate a type class, we write

    instance : name_of_type_class name_of_type :=
    { constant₁ := definition_of_constant₁,
      constant₂ := definition_of_constant₂,
      ⋮
      property₁ := proof_of_property₁,
      property₂ := proof_of_property₂,
      ⋮                                }

## Groups

Mathematicians would define a group as follows:

> A group is a set `G` with a binary operator `• : G ⨉ G → G` fulfilling the following properties, called group axioms:
> * Associativity: For all `a, b, c ∈ G`, we have `(a • b) • c = a • (b • c)`
> * Identity element: There exists an element `e ∈ G` such that for all `a ∈ G`, we have `e • a = a`
> * Inverse element: For each `a ∈ G`, there exists an inverse element `inv(a) ∈ G` such that `inv(a) • a = e`

Examples of groups are:
* `ℤ` with `+`
* `ℝ` with `+`
* `ℝ \ {0}` with `*`

In Lean, a type class for groups can be defined as:

    class group (α : Type) :=
    (mul          : α → α → α)
    (mul_assoc    : ∀a b c, mul (mul a b) c = mul a (mul b c))
    (one          : α)
    (one_mul      : ∀a, mul one a = a)
    (inv          : α → α)
    (mul_left_inv : ∀a, mul (inv a) a = one)

In mathlib, however, group is part of a larger hierarchy of algebraic structures:

Type class               | Properties
------------------------ | ------------
`semigroup`              | associativity
`monoid`                 | `semigroup` with neutral element
`left_cancel_semigroup`  | `semigroup` with `x * a = x * b → a = b`
`right_cancel_semigroup` | `semigroup` with `a * x = b * x → a = b`
`group`                  | `monoid` with inverse elements

Most of these structures have commutative versions: `comm_semigroup`, `comm_monoid`, `comm_group`

The _multiplicative_ structures (over `*`, `1`, `⁻¹`) are copied to produce _additive_ versions (over `+`, `0`, `-`): `add_semigroup`, `add_monoid`, `add_group` `add_comm_semigroup`, …


## Fields

Mathematicians would define a field as follows:

> A field is a set `F` such that
>* `F` forms a commutative group under an operator `+`, called
>  addition, with identity element `0`
>* `F\{0}` forms a commutative group under an operator `*`, called multiplication
>* Multiplication distributes over addition, i.e.,
>  `a * (b + c) = a * b + a * c` for all `a, b, c ∈ F`

In mathlib, fields are also part of a larger hierarchy:

Structure        |  Properties                                                | Examples 
-----------------|------------------------------------------------------------|---------------------
`semiring`       | `monoid` and `add_comm_monoid` with distributivity         | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`comm_semiring`  | `semiring` with commutativity of `*`                       | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`ring`           | `monoid` and `add_comm_group` with distributivity          | `ℝ`, `ℚ`, `ℤ`
`comm_ring`      | `ring` with commutativity of `*`                           | `ℝ`, `ℚ`, `ℤ`
`division_ring`  | `ring` with multiplicative inverse `⁻¹`                    | `ℝ`, `ℚ`        
`field`          | `division_ring` with commutativity of `*`                  | `ℝ`, `ℚ`     
`discrete_field` | `field` with decidable equality and `∀n, n / 0 = 0`        | `ℝ`, `ℚ`     


## Coercions

When dealing with different numbers form `ℕ`, `ℤ`, `ℚ`, and `ℝ` at the same time, we might want to cast from one type to another

Lean has a mechanism to automatically introduce coercions, represented by `coe` or `↑`

The coercion operator can be set up to provide implicit coercions between arbitrary types

Many coercions are already in place, including the following:
* `coe : ℕ → α` casts `ℕ` into another semiring `α`
* `coe : ℤ → α` casts `ℤ` into another ring `α`
* `coe : ℚ → α` casts `ℚ` into another division ring `α`


## Lists, Multisets, and Finite Sets

For finite collections of elements different structures are available:
* Lists: number of occurrences and order matter
* Multisets: number of occurrences matters, order doesn't
* Finsets: number of occurrences and order don't matter

## Demo

[`love12_basic_mathematical_structures_demo.lean`](../lean/love12_basic_mathematical_structures_demo.lean)
