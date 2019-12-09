# LoVe Lecture 13: Rational and Real Numbers

Today we will go through the construction of `ℚ` and `ℝ` as quotient types

A general recipe to construct new types with specific properties is as follows:

1. Create a new type that can represent all elements, but not necessarily in a unique manner

2. Quotient this representation, equating elements that should be considered
  equal

3. Define operators on the quotient type by lifting functions from the base
  type, and prove that they respect the quotient relation

We have used this approach before to construct `ℤ`; it can be used to
construct `ℚ` and `ℝ` as well

## Rational Numbers

**Step 1.** A rational number is a number that can be expressed as a fraction
`n/d` of integers `n` and `d ≠ 0`:

    structure fraction :=
    (num           : ℤ)
    (denom         : ℤ)
    (denom_ne_zero : denom ≠ 0)


The number `n` is called the numerator, and the number `d` is
called the denominator

The representation of a rational number as a fraction
is not unique, e.g., `1/2 = 2/4 = -1/-2

**Step 2.** Two fractions `n₁/d₁` and `n₂/d₂` represent the same rational
number if the ratio between numerator and denominator are the same, i.e., 
`n₁ * d₂ = n₂ * d₁`

This will be our equivalence relation `≈` on fractions

**Step 3.** Define `0 := 0 / 1`, `1 := 1 / 1`, and addition, multiplication, etc:

    n₁ / d₁ + n₂ / d₂      :=  (n₁ * d₂ + n₂ * d₁) / (d₁ * d₂)
    (n₁ / d₁) * (n₂ / d₂)  :=  (n₁ * n₂) / (d₁ * d₂)

Then show that they respect the relation `≈`


**Alternative definitions of `ℚ`:**

* Like above, but with an additional property
`cop : coprime num denom`, which states that that numerator
and denominator do not have a common divisor (except `1` and `-1`):

      structure rat :=
      (num : ℤ)
      (denom : ℕ)
      (pos : 0 < denom)
      (cop : coprime num denom)

    This is the definition used in `mathlib`

    Advantages: no quotient required; more efficient computation; more theorems are definitional equalities

    Disadvantage: more complicated function definitions

* Define all elements syntactically, including the desired operations:

      inductive pre_rat : Type
      | zero : pre_rat
      | one : pre_rat
      | add : pre_rat → pre_rat → pre_rat
      | sub : pre_rat → pre_rat → pre_rat
      | mul : pre_rat → pre_rat → pre_rat
      | div : pre_rat → pre_rat → pre_rat

  Define `≈` to enforce congruence rules the field axioms:

      inductive equiv : pre_rat → pre_rat → Prop
      | add_congr {a b c d : pre_rat} :
          equiv a b → equiv c d → equiv (add a c) (add b d)
      | add_assoc {a b c : pre_rat} :
          equiv (add a (add b c)) (add (add a b) c)
      | zero_add {a : pre_rat} : equiv (add zero a) a
      | add_comm {a b : pre_rat} : equiv (add a b) (add b a)
      | etc : equiv sorry sorry

  Advantages: does not require `ℤ`; easy to prove the `field` axioms; general recipe reusable for other algebraic constructions (e.g. free monoids, free groups)
  
  Disadvantage: the definition of orders and lemmas about them are more complicated


## Real Numbers


There are sequences of rational numbers that seem to converge because the
numbers in the sequence get closer and closer to each other, and yet do not
converge to a rational number

Example: Let `aₙ` be the largest number with `n` digits after the decimal point
such that `aₙ² < 2`

    a₀ = 1
    a₁ = 1.4
    a₂ = 1.41
    a₃ = 1.414
    a₄ = 1.4142
    a₅ = 1.41421
    a₆ = 1.414213
    a₇ = 1.4142135
    a₈ = 1.41421356
  
This sequence
seems to converge because each `aₙ` is at most
`10⁻ⁿ` away from any of the following numbers

But the limit is `√2`, which is not a rational number

In that sense, the rational numbers are **incomplete**, and the reals are their
**completion**

To construct the reals, we need to fill in the gaps that are
revealed by these sequences that seem to converge, but do not


> A sequence `a₀, a₁, ...` of rational numbers is _Cauchy_ if
> for any `ε > 0`, there exists an `N ∈ ℕ`
> such that for all `m ≥ N`, we have
> `|a`<sub>`N`</sub>` - aₘ| < ε`.

In
other words, no matter how small we choose `ε`, we can always find a
point in the sequence from which all following numbers do not deviate more
than `ε`

In Lean:

    def is_cau_seq (f : ℕ → ℚ) : Prop :=
    ∀ε > 0, ∃N, ∀m ≥ N, abs (f N - f m) < ε

We define a type of Cauchy sequences as a subtype:

    def cau_seq : Type :=
    {f : ℕ → ℚ // is_cau_seq f}

Idea: Cauchy sequences represent real numbers

* `aₙ = 1/n` represents the real number `0`
* `1, 1.4, 1.41, ...` represents the real number `√2`
* `aₙ = 0` also represents the real number `0`

Since different Cauchy sequences can represent the same real number, we
need to take the quotient over sequences representing the same real number

Formally, two sequences represent the same real number when their difference
converges to zero:

    instance equiv : setoid cau_seq :=
    { r := λf g, ∀ε > 0, ∃N, ∀m ≥ N, abs (f.val m - g.val m) < ε,
      iseqv := sorry }

The real numbers are the quotient:

    def my_real : Type :=
    quotient cau_seq.equiv


### Alternative Definitions of the Real Numbers

* Dedekind cuts: `r : ℝ` is represented essentially as `{x : ℚ | x < r}`

* Binary sequences `ℕ → bool` for the interval [0, 1]


## Demo

[`love13_rational_and_real_numbers_demo.lean`](../lean/love13_rational_and_real_numbers_demo.lean)
