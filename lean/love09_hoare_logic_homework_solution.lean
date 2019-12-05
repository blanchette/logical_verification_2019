/- LoVe Homework 9: Hoare Logic -/

import .love08_operational_semantics_exercise_sheet
import .love09_hoare_logic_demo

namespace LoVe


/- Question 1: Hoare Logic for Dijkstra's Guarded Command Language -/

/- Recall the definition of GCL from exercise 8: -/

#check gcl

namespace gcl

#check big_step

/- The definition of Hoare triples for partial correctness is unsurprising: -/

def partial_hoare (P : state → Prop) (S : gcl state) (Q : state → Prop) :
  Prop :=
∀s t, P s → (S, s) ~~> t → Q t

local notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` :=
partial_hoare P S Q

namespace partial_hoare

variables {P : state → Prop} {S : gcl state}

/- 1.7 **optional**. Prove the rule you stated for `loop`.

Hint: This one is difficult and requires some generalization, as explained in
Section 5.8 ("Induction Pitfalls") of the lecture notes. -/

lemma loop_intro (h : {* P *} S {* P *}) :
  {* P *} loop S {* P *} :=
begin
  intros s t hs,
  generalize eq : (loop S, s) = ps,
  intro hst,
  induction hst generalizing s;
    cases eq,
  { assumption },
  { clear eq, rename hst_s s, rename hst_t t, rename hst_u u,
    apply hst_ih_hrest t,
    apply h s,
    repeat { assumption },
    { refl } }
end

end partial_hoare

end gcl

end LoVe
