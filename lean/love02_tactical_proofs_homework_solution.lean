/- LoVe Homework 2: Tactical Proofs -/

import .love02_tactical_proofs_exercise

namespace LoVe


/- Question 2 (**optional**): Logical Connectives -/

/- 2.1 (**optional**). Prove the following property about double negation.

Hint: You will need to apply the elimination rule for `false` at a key point in
the proof. -/

lemma herman (p : Prop) : ¬¬ (¬¬ p → p) :=
begin
  intro hnnnpp,
  apply hnnnpp,
  intro hnnp,
  apply false.elim,
  apply hnnp,
  intro hp,
  apply hnnnpp,
  intro hnnp,
  exact hp
end

/- 2.2 (**optional**). Prove the missing link in our chain of classical axiom
implications.

Hint: You will need to apply the double negation hypothesis for `p ∨ ¬ p`. You
will also need the left and right introduction rules for `or` at some point. -/

#check excluded_middle
#check peirce
#check double_negation

lemma em_of_dn : double_negation → excluded_middle :=
begin
  simp [double_negation, excluded_middle],
  intros hdoubleneg p,
  apply hdoubleneg,
  intro hnponp,
  apply hnponp,
  apply or.intro_right,
  intro hnp,
  apply hnponp,
  apply or.intro_left,
  assumption
end

/- 2.3 (**optional**). We have proved three of the six possible implications
between `excluded_middle`, `peirce`, and `double_negation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check peirce_of_em
#check dn_of_peirce
#check em_of_dn

lemma dn_imp_peirce : double_negation → peirce :=
begin
  intro h,
  apply peirce_of_em,
  apply em_of_dn,
  exact h
end

lemma peirce_imp_em : peirce → excluded_middle :=
begin
  intro h,
  apply em_of_dn,
  apply dn_of_peirce,
  exact h
end

lemma em_imp_dn : excluded_middle → double_negation :=
begin
  intro h,
  apply dn_of_peirce,
  apply peirce_of_em,
  exact h
end

end LoVe
