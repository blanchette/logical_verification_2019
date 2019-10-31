/- LoVe Homework 2: Tactical Proofs -/

import .love02_tactical_proofs_exercise

namespace LoVe


/- Question 1: Connectives and Quantifiers -/

/- 1.1. Complete the following proofs using basic tactics. -/

lemma B (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
sorry

lemma S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
sorry

lemma more_nonsense (a b c d : Prop) :
  ((a → b) → c → d) → c → b → d :=
sorry

lemma even_more_nonsense (a b c : Prop) :
  (a → b) → (a → c) → a → b → c :=
sorry

/- 1.2. Prove the following lemma. -/

lemma weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b :=
sorry


/- Question 2 (**optional**): Logical Connectives -/

/- 2.1 (**optional**). Prove the following property about double negation.

Hint: You will need to apply the elimination rule for `false` at a key point in
the proof. -/

lemma herman (p : Prop) : ¬¬ (¬¬ p → p) :=
sorry

/- 2.2 (**optional**). Prove the missing link in our chain of classical axiom
implications.

Hint: You will need to apply the double negation hypothesis for `p ∨ ¬ p`. You
will also need the left and right introduction rules for `or` at some point. -/

#check excluded_middle
#check peirce
#check double_negation

lemma em_of_dn : double_negation → excluded_middle :=
sorry

/- 2.3 (**optional**). We have proved three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check peirce_of_em
#check dn_of_peirce
#check em_of_dn

-- enter your solution here

end LoVe
