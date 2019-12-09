/- LoVe Exercise 13: Rational and Real Numbers -/

import .love05_inductive_predicates_demo
import .love13_rational_and_real_numbers_demo

namespace LoVe

set_option pp.beta true


/- Question 1: Rationals -/

/- 1.1. Prove the following lemma.

Hint: The lemma `fraction.mk.inj_eq` might be useful. -/

#check fraction.mk.inj_eq

lemma fraction.ext (a b : fraction) (h : fraction.num a = fraction.num b)
    (h': fraction.denom a = fraction.denom b) :
  a = b :=
sorry

/- 1.2. Extending the `fraction.has_mul` instance from the lecture, declare
`fraction` an instance of `semigroup`.

Hint: Use the lemma `fraction.ext` above, and possibly `fraction.mul_num`, and
`fraction.mul_denom`. -/

#check fraction.ext
#check fraction.mul_num
#check fraction.mul_denom

instance fraction.semigroup : semigroup fraction :=
{ mul_assoc :=
    sorry,
  ..fraction.has_mul }

/- 1.3. Extending the `myℚ.has_mul` instance from the lecture, declare `myℚ` an
instance of `semigroup`.

Hint: The lemma `quotient.induction_on₃` might be useful. -/

#check quotient.induction_on₃

instance myℚ.semigroup : semigroup myℚ :=
{ mul_assoc :=
    sorry,
  ..myℚ.has_mul }


/- Question 2: Structural Induction on Paper -/

/- This and the next question will exercise your understanding of induction,
especially if you need to perform induction proofs on a whiteboard (or on paper
at the exam).

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `linarith`
need not be justified if you think they are obvious (to humans), but you should
say which key lemmas they follow from. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

/- 2.1. Recall the following inductive datatype for binary trees from lecture 4:

    inductive btree (α : Type) : Type
    | empty {} : btree
    | node     : α → btree → btree → btree

We defined a function `mirror` on these binary trees as follows:

    def mirror {α : Type} : btree α → btree α
    | empty        := empty
    | (node a l r) := node a (mirror r) (mirror l)

Prove the following lemma by structural induction, as a paper proof:

    lemma mirror_mirror {α : Type} :
      ∀t : btree α, mirror (mirror t) = t -/

-- enter your "paper" proof here

/- 2.2. Prove the same lemma in Lean and compare it with your paper proof. -/

lemma mirror_mirror₂ {α : Type} :
  ∀t : btree α, mirror (mirror t) = t :=
sorry


/- Question 3: Rule Induction on Paper -/

/- 3.1. Recall the following inductive predicate from lecture 5:

    inductive even : ℕ → Prop
    | zero    : even 0
    | add_two : ∀n, even n → even (n + 2)

Prove the following lemma by rule induction, as a paper proof, following the
guidelines given at the beginning of question 2. This is a good exercise to
develop a deeper understanding of how rule induction works (and is good
practice for the final exam).

    lemma exists_of_even (n : ℕ) (h : even n) :
      ∃k : ℕ, n = 2 * k -/

-- enter your "paper" proof here

/- 3.2. Prove the same lemma in Lean and compare it with your paper proof. -/

lemma exists_of_even (n : ℕ) (h : even n) :
  ∃k : ℕ, n = 2 * k :=
sorry

end LoVe
