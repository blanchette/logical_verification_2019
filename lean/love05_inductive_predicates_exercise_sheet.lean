/- LoVe Exercise 5: Inductive Predicates -/

import .love05_inductive_predicates_demo

namespace LoVe


/- Question 1: Even and Odd -/

/- The `even` predicate is true for even numbers and false for odd numbers. -/

#check even

/- 1.1. Prove that 0, 2, 4, and 6 are even. -/

-- enter your answer here

/- We define `odd` as the negation of `even`: -/

def odd (n : ℕ) : Prop :=
  ¬ even n

/- 1.2. Prove that 1 is odd and register this fact as a `simp` rule.

Hint: `cases` is useful to reason about hypotheses of the form `even …`. -/

@[simp] lemma odd_1 :
  odd 1 :=
sorry

/- 1.3. Prove that 3, 5, and 7 are odd. -/

-- enter your answer here

/- 1.4. Complete the following proof by structural induction.

Hint: You can rely implicitly on computation for the induction step. -/

lemma even_two_times :
  ∀m : ℕ, even (2 * m)
:= sorry

/- 1.5. Complete the following proof by rule induction.

Hint: You can use the `cases` tactic (or `match … with`) to destruct an
existential quantifier and extract the witness. -/

lemma even_imp_exists_two_times :
  ∀n : ℕ, even n → ∃m, n = 2 * m
| _ even.zero            := exists.intro 0 (by simp)
| _ (even.add_two n hen) :=
sorry

/- 1.6. Using `even_two_times` and `even_imp_exists_two_times`, prove the
following equivalence. -/

lemma even_iff_exists_two_times (n : ℕ) :
  even n ↔ ∃m, n = 2 * m :=
sorry


/- Question 2: Binary Trees -/

/- 2.1. Prove the converse of `is_full_mirror`. You may exploit already proved
lemmas (e.g., `is_full_mirror`, `mirror_mirror`). -/

lemma mirror_is_full {α : Type} :
  ∀t : btree α, is_full (mirror t) → is_full t :=
sorry

/- 2.2. Define a function that counts the number of constructors (`empty` or
`node`) in a tree. -/

def count {α : Type} : btree α → ℕ
:= sorry

end LoVe
