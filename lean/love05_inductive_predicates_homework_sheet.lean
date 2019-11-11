/- LoVe Homework 5: Inductive Predicates -/

import .lovelib

namespace LoVe


/- Question 1: Lambda-Terms -/

/- Recall the following type of λ-terms from question 3 of exercise 4. -/

inductive lam : Type
| var : string → lam
| abs : string → lam → lam
| app : lam → lam → lam

export lam (var abs app)

/- 1.1. Define an inductive predicate `is_abs` that returns true if and only if
its argument has an `abs` constructor at the top level. -/

-- enter your definition here

/- 1.2. Define an inductive predicate `is_βnf` that determines whether a lambda
term is in β-normal form (https://en.wikipedia.org/wiki/Beta_normal_form).

Hint: Use `is_abs` somewhere. -/

-- enter your definition here


/- Question 2: Transitive Closure -/

/- In mathematics, the transitive closure `R+` of a binary relation `R` over a
set `A` can be defined as the smallest solution satisfying the following rules:

    (base) for all a, b ∈ A, if a R b, then a R+ b;
    (step) for all a, b, c ∈ A, if a R b and b R+ c, then a R+ c.

In Lean, we can define this concept as follows, by identifying the set `A` with
the type `α`: -/

inductive tc₁ {α : Type} (r : α → α → Prop) : α → α → Prop
| base : ∀a b, r a b → tc₁ a b
| step : ∀a b c, r a b → tc₁ b c → tc₁ a c

/- 2.1. Rule `(step)` makes it convenient to extend transitive chains by adding
links to the left. Another way to define the transitive closure `R+` would use
the following rule instead of `(step)`, with a preference for the right:

    (pets) for all a, b, c ∈ A, if a R+ b and b R c, then a R+ c.

Define a predicate `tc₂` that embodies this alternative definition. -/

-- enter your definition here

/- 2.2. Yet another definition of the transitive closure `R+` would use the
following symmetric rule instead of `(step)` or `(pets)`:

    (trans) for all a, b, c ∈ A, if a R+ b and b R+ c, then a R+ c.

Define a predicate `tc₃` that embodies this alternative definition. -/

-- enter your definition here

/- 2.3. Prove that `(step)` also holds as a lemma about `tc₃`. -/

lemma tc₃_step {α : Type} (r : α → α → Prop) (a b c : α) (rab : r a b)
    (tbc : tc₃ r b c) :
  tc₃ r a c :=
sorry

/- 2.4 (**optional**). Prove by rule induction on the `tc₁ r a b` premise below
that `(pets)` also holds as a lemma about `tc₁` as defined above.  -/

lemma tc₁_pets {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b, tc₁ r a b → r b c → tc₁ r a c :=
sorry

/- 2.5 (**optional**). Prove by rule induction that `(trans)` also holds as a
lemma about `tc₁`. -/

lemma tc₁_trans {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b : α, tc₁ r a b → tc₁ r b c → tc₁ r a c :=
sorry

end LoVe
