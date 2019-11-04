/- LoVe Exercise 3: Structured Proofs and Proof Terms -/

import .lovelib

namespace LoVe


/- Question 1: Chain of Equalities -/

/- 1.1. Write the following proof using `calc`.

    (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: You might need `rw`, `simp`, `ac_refl`, and the lemmas `mul_add`,
`add_mul`, and `two_mul`. -/

lemma binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
sorry

/- 1.2. Prove the same argument again, this time as a structured proof. Try to
reuse as much of the above proof idea as possible. -/

lemma binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
sorry

/- 1.3 (**optional**). Prove the same lemma again, this time using tactics. -/

lemma binomial_square₃ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
begin
  sorry
end


/- Question 2: Connectives and Quantifiers -/

/- 2.1. Supply structured proofs of the following lemmas. -/

lemma I (a : Prop) :
  a → a :=
sorry

lemma K (a b : Prop) :
  a → b → b :=
sorry

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
sorry

lemma proj_1st (a : Prop) :
  a → a → a :=
sorry

-- please give a different answer than for `proj_1st`
lemma proj_2nd (a : Prop) :
  a → a → a :=
sorry

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
sorry

/- 2.2. Supply a structured proof of the contraposition rule. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
sorry

end LoVe
