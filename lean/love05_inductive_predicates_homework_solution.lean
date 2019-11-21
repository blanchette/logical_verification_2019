/- LoVe Homework 5: Inductive Predicates -/

import .lovelib

namespace LoVe


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

/- 2.4 (**optional**). Prove by rule induction on the `tc₁ r a b` premise below
that `(pets)` also holds as a lemma about `tc₁` as defined above.  -/

lemma tc₁_pets {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b, tc₁ r a b → r b c → tc₁ r a c :=
begin
  intros a b tab rbc,
  induction tab,
  case tc₁.base : x y rxy ryc {
    exact tc₁.step _ _ _ rxy (tc₁.base _ _ ryc) },
  case tc₁.step : x y z rxy tyz tyc_of_rzc rzc {
    exact tc₁.step _ _ _ rxy (tyc_of_rzc rzc) }
end

/- 2.5 (**optional**). Prove by rule induction that `(trans)` also holds as a
lemma about `tc₁`. -/

lemma tc₁_trans {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b : α, tc₁ r a b → tc₁ r b c → tc₁ r a c :=
begin
  intros a b tab tbc,
  induction tab,
  case tc₁.base : x y rxy tyc {
    exact tc₁.step _ _ _ rxy tyc },
  case tc₁.step : x y z rxy tyz tyc_of_tzc tzc {
    exact tc₁.step _ _ _ rxy (tyc_of_tzc tzc) }
end

end LoVe
