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

variables {P P' P₁ P₂ P₃ Q Q' : state → Prop} {x : string} {a : state → ℕ}
variables {S S₀ S₁ S₂ : gcl state} {Ss : list (gcl state)}

/- 1.1. Prove the consequence rule. -/

lemma consequence (h : {* P *} S {* Q *}) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
  {* P' *} S {* Q' *} :=
sorry

/- 1.2. Prove the rule for `assign`. -/

lemma assign_intro (P : state → Prop) :
  {* λs : state, P (s{x ↦ a s}) *} assign x a {* P *} :=
sorry

/- 1.3. Prove the rule for `assert`. -/

lemma assert_intro :
  {* λs, Q s → P s *} assert Q {* P *} :=
sorry

/- 1.4. Prove the rule for `seq`. -/

lemma seq_intro (h₁ : {* P₁ *} S₁ {* P₂ *}) (h₂ : {* P₂ *} S₂ {* P₃ *}) :
  {* P₁ *} seq S₁ S₂ {* P₃ *} :=
sorry

/- 1.5. Prove the rule for `choice`. -/

lemma choice_intro
    (h : ∀i (hi : i < list.length Ss),
       {* λs, P s *} list.nth_le Ss i hi {* Q *}) :
  {* P *} choice Ss {* Q *} :=
sorry

/- 1.6. State the rule for `loop`.

    lemma loop_intro … :
      {* … *} loop p {* … *} :=
    … -/

/- 1.7 **optional**. Prove the rule you stated for `loop`.

Hint: This one is difficult and requires some generalization, as explained in
Section 5.8 ("Induction Pitfalls") of the lecture notes. -/

-- enter your answer to question 1.6 here
-- enter your answer to question 1.7 here

end partial_hoare

end gcl


/- Question 2: Factorial -/

section FACT

/- The following WHILE program is intended to compute the factorial of `n`,
leaving the result in `r`. -/

def FACT : program :=
assign "r" (λs, 1) ;;
while (λs, s "n" ≠ 0)
  (assign "r" (λs, s "r" * s "n") ;;
   assign "n" (λs, s "n" - 1))

/- 2.1. Define the factorial function. -/

def fact : ℕ → ℕ
:= sorry

/- 2.2. Prove the correctness of `FACT` using `vcg`. -/

lemma FACT_correct (n : ℕ) :
  {* λs, s "n" = n *} FACT {* λs, s "r" = fact n *} :=
sorry

end FACT

end LoVe
