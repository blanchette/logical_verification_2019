/- LoVe Homework 4: Functional Programming -/

import .love04_functional_programming_demo

namespace LoVe


/- Question 1: Reverse of a List -/

/- Recall the `reverse` operation and the `reverse_append` lemma from the
lecture. -/

#check reverse
#check reverse_append

/- 1.1. Prove the following distributive property, using a calculational proof
for the inductive step. -/

lemma reverse_append₂ {α : Type} :
  ∀xs ys : list α, reverse (xs ++ ys) = reverse ys ++ reverse xs
:= sorry

/- 1.2. Prove the induction step in the proof below using the calculational
style, following this proof sketch:

      reverse (reverse (x :: xs))
    =     { by definition of `reverse` }
      reverse (reverse xs ++ [x])
    =     { using the lemma `reverse_append` }
      reverse [x] ++ reverse (reverse xs)
    =     { by the induction hypothesis }
      reverse [x] ++ xs
    =     { by definition of `++` and `reverse` }
      [x] ++ xs
    =     { by computation }
      x :: xs -/

lemma reverse_reverse₂ {α : Type} :
  ∀xs : list α, reverse (reverse xs) = xs
| []        := by refl
| (x :: xs) :=
sorry


/- Question 2: Gauss's Summation Formula -/

-- `sum_upto f n = f 0 + f 1 + ⋯ + f n`
def sum_upto (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| (m + 1) := sum_upto m + f (m + 1)

/- 2.1. Prove the following lemma, discovered by Carl Friedrich Gauss as a
pupil.

Hints: The `mul_add` and `add_mul` lemmas and the `ac_refl` tactics might be
useful to reason about multiplication. -/

#check mul_add
#check add_mul

lemma sum_upto_eq :
  ∀m : ℕ, 2 * sum_upto (λi, i) m = m * (m + 1)
:= sorry

/- 2.2. Prove the following property of `sum_upto`. -/

lemma sum_upto_mul (a : ℕ) (f : ℕ → ℕ) :
  ∀(n : ℕ), sum_upto (λi, a * f i) n = a * sum_upto f n
:= sorry

end LoVe
