/- LoVe Exercise 5: Inductive Predicates -/

import .love05_inductive_predicates_demo

namespace LoVe


/- Question 1: Even and Odd -/

/- The `even` predicate is true for even numbers and false for odd numbers. -/

#check even

/- 1.1. Prove that 0, 2, 4, and 6 are even. -/

lemma even_0 : even 0 := even.zero
lemma even_2 : even 2 := even.add_two _ even_0
lemma even_4 : even 4 := even.add_two _ even_2
lemma even_6 : even 6 := even.add_two _ even_4

/- We define `odd` as the negation of `even`: -/

def odd (n : ℕ) : Prop :=
  ¬ even n

/- 1.2. Prove that 1 is odd and register this fact as a `simp` rule.

Hint: `cases` is useful to reason about hypotheses of the form `even …`. -/

@[simp] lemma odd_1 :
  odd 1 :=
by intro h; cases h

/- 1.3. Prove that 3, 5, and 7 are odd. -/

example : odd 3 := by intro h; cases h; cases h_a
example : odd 5 := by intro h; cases h; cases h_a; cases h_a_a
example : odd 7 := by intro h; cases h; cases h_a; cases h_a_a; cases h_a_a_a

/- 1.4. Complete the following proof by structural induction.

Hint: You can rely implicitly on computation for the induction step. -/

lemma even_two_times :
  ∀m : ℕ, even (2 * m)
| 0       := even.zero
| (m + 1) :=
  begin
    apply even.add_two,
    apply even_two_times
  end

/- 1.5. Complete the following proof by rule induction.

Hint: You can use the `cases` tactic (or `match … with`) to destruct an
existential quantifier and extract the witness. -/

lemma even_imp_exists_two_times :
  ∀n : ℕ, even n → ∃m, n = 2 * m
| _ even.zero            := exists.intro 0 (by simp)
| _ (even.add_two n hen) :=
  begin
    cases even_imp_exists_two_times n hen,
    use w + 1,
    rw h,
    linarith
  end

/- 1.6. Using `even_two_times` and `even_imp_exists_two_times`, prove the
following equivalence. -/

lemma even_iff_exists_two_times (n : ℕ) :
  even n ↔ ∃m, n = 2 * m :=
begin
  apply iff.intro,
  { apply even_imp_exists_two_times },
  { intro h,
    cases h,
    simp *,
    apply even_two_times }
end


/- Question 2: Binary Trees -/

/- 2.1. Prove the converse of `is_full_mirror`. You may exploit already proved
lemmas (e.g., `is_full_mirror`, `mirror_mirror`). -/

lemma mirror_is_full {α : Type} :
  ∀t : btree α, is_full (mirror t) → is_full t :=
begin
  intros t fmt,
  have fmmt : is_full (mirror (mirror t)) := is_full_mirror _ fmt,
  rw mirror_mirror at fmmt,
  assumption
end

/- 2.2. Define a function that counts the number of constructors (`empty` or
`node`) in a tree. -/

def count {α : Type} : btree α → ℕ
| empty        := 1
| (node _ l r) := count l + count r + 1

end LoVe
