/- LoVe Homework 3: Structured Proofs and Proof Terms -/

import .love02_tactical_proofs_exercise_sheet

namespace LoVe


/- Question 2: Logic Puzzles -/

/- 2.2 (**optional**). Prove the same lemma again, this time by providing a
proof term.

Hint: There is an easy way. -/

lemma weak_peirce₂ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
λ(a b : Prop) (habaab : (((a → b) → a) → a) → b),
  habaab (λ(habaa : (a → b) → a),
    habaa (λ(ha : a), habaab (λ(haba : (a → b) → a), ha)))

/- The easy way is `#print weak_peirce`. There is an even easier way: to use
`weak_peirce` as the proof of `weak_peirce₂`. -/

/- 2.3 (**optional**). Prove the same lemma again, this time by providing a
structured proof. -/

lemma weak_peirce₃ :
  ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
assume (a b : Prop) (habaab : (((a → b) → a) → a) → b),
show b, from habaab
  (assume (habaa : (a → b) → a),
   show a, from habaa
     (assume (ha : a),
      show b, from habaab
        (assume (haba : (a → b) → a),
         show a, from ha)))

end LoVe
