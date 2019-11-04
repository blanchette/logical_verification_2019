/- LoVe Homework 3: Structured Proofs and Proof Terms -/

import .love02_tactical_proofs_exercise_sheet

namespace LoVe


/- Question 1: Logical Connectives and Quantifiers -/

/- 1.1. Supply a structured proof of the distributivity of `∀` over `∧`. -/

#check forall_and

lemma forall_and₂ {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
sorry

/- 1.2. We have proved or stated three of the six possible implications between
`excluded_middle`, `peirce`, and `double_negation`. Prove the three missing
implications using proof terms, exploiting the three theorems we already
have. -/

#check peirce_of_em
#check dn_of_peirce
#check sorry_lemmas.em_of_dn

lemma peirce_of_dn :
  double_negation → peirce :=
sorry

lemma em_of_peirce :
  peirce → excluded_middle :=
sorry

lemma dn_of_em :
  excluded_middle → double_negation :=
sorry


/- Question 2: Logic Puzzles -/

/- 2.1. Prove the following lemma using tactics. -/

lemma weak_peirce :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
sorry

/- 2.2 (**optional**). Prove the same lemma again, this time by providing a
proof term.

Hint: There is an easy way. -/

lemma weak_peirce₂ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
sorry

/- 2.3 (**optional**). Prove the same lemma again, this time by providing a
structured proof. -/

lemma weak_peirce₃ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
sorry

end LoVe
