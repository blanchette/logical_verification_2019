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
calc (a + b) * (a + b) = a * (a + b) + b * (a + b) :
  by simp [add_mul]
... = a * a + a * b + b * a + b * b :
  by simp [mul_add]
... = a * a + a * b + a * b + b * b :
  by ac_refl
... = a * a + 2 * a * b + b * b :
  by simp [two_mul, add_mul]; ac_refl

/- 1.2. Prove the same argument again, this time as a structured proof. Try to
reuse as much of the above proof idea as possible. -/

lemma binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
have h1 : (a + b) * (a + b) = a * (a + b) + b * (a + b) :=
  by simp [add_mul],
have h2 : a * (a + b) + b * (a + b) = a * a + a * b + b * a + b * b :=
  by simp [mul_add],
have h3 : a * a + a * b + b * a + b * b = a * a + a * b + a * b + b * b :=
  by ac_refl,
have h4 : a * a + a * b + a * b + b * b = a * a + 2 * a * b + b * b :=
  by simp [two_mul, add_mul]; ac_refl,
show _,
  by rw [h1, h2, h3, h4]

/- 1.3 (**optional**). Prove the same lemma again, this time using tactics. -/

lemma binomial_square₃ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
begin
  simp [add_mul, mul_add, two_mul],
  ac_refl
end


/- Question 2: Connectives and Quantifiers -/

/- 2.1. Supply structured proofs of the following lemmas. -/

lemma I (a : Prop) :
  a → a :=
assume ha,
show a, from ha

lemma K (a b : Prop) :
  a → b → b :=
assume ha hb,
show b, from hb

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
assume hg hb ha,
show c, from hg ha hb

lemma proj_1st (a : Prop) :
  a → a → a :=
assume ha ha',
show a, from ha

-- please give a different answer than for `proj_1st`
lemma proj_2nd (a : Prop) :
  a → a → a :=
assume ha ha',
show a, from ha'

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
assume hg ha hf hb,
have hc : c := hf ha,
show c, from hc

/- 2.2. Supply a structured proof of the contraposition rule. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
assume hab hnb ha,
have hb : b := hab ha,
show false, from hnb hb

end LoVe
