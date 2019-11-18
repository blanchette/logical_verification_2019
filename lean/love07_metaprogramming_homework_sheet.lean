/- LoVe Homework 7: Metaprogramming -/

import .lovelib

namespace LoVe

open expr
open tactic
open declaration


/- Question 1: A `safe` Tactic -/

/- We develop a tactic that applies all safe introduction and elimination rules
for the connectives and quantifiers exhaustively. A rule is said to be _safe_ if
it always gives rise to provable subgoals. In addition, we will require that
safe rules do not introduce metavariables (which can easily be instantiated
accidentally with the wrong terms.)

We proceed in three steps. -/

/- 1.1. Develop a `safe_intros` tactic that applies the introduction rules for
`true`, `¬`, `∧`, `↔`, and `→`/`∀`. The tactic generalizes `intro_ands` from the
exercise.

**Hint**: You can use `tactic.intro` or `tactic.intro1` for some of these.

**Hint**: You can use the `<|>` operator between the rules/tactics for different
symbols. -/

meta def safe_intros : tactic unit :=
sorry

example {a b c d : Prop} :
  a → ¬ b ∧ (c ↔ d) :=
begin
  safe_intros,
  /- The proof state should be roughly as follows:

  a b c d : Prop,
  a_1 : a,
  a_2 : b
  ⊢ false

  a b c d : Prop,
  a_1 : a,
  a_2 : c
  ⊢ d

  a b c d : Prop,
  a_1 : a,
  a_2 : d
  ⊢ c -/
  repeat { sorry }
end

/- 1.2. Develop a `safe_destructs` tactic that eliminates `false`, `∧`, `∨`,
`↔`, and `∃`. The tactic generalizes `destruct_ands` from the exercise. -/

meta def safe_destructs : tactic unit :=
sorry

example {a b c d e f : Prop} {p : ℕ → Prop}
    (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
    (hex : ∃x, p x) :
  false :=
begin
  safe_destructs,
  /- The proof state should be roughly as follows:

  2 goals
  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  hand_left : a,
  hor : c,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  hand_left : a,
  hor : d,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false -/
  repeat { sorry }
end

/- 1.3. Implement a `safe` tactic that first performs introduction, then
elimination, and finally proves all the subgoals that can be discharged directly
by `assumption`. The tactic generalizes `destro_and` from the exercise.

**Hint**: The `try` tactic combinator might be useful. -/

meta def safe : tactic unit :=
sorry

example {a b c d e f : Prop} {p : ℕ → Prop}
    (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
    (hex : ∃x, p x) :
  a → ¬ b ∧ (c ↔ d) :=
begin
  safe,
  /- The proof state should be roughly as follows:

  3 goals
  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  a_1 : a,
  a_2 : b,
  hand_left : a,
  hor : c,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  a_1 : a,
  a_2 : b,
  hand_left : a,
  hor : d,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ false

  a b c d e f : Prop,
  p : ℕ → Prop,
  hneg : ¬a,
  himp : b → e,
  a_1 : a,
  a_2 : c,
  hand_left : a,
  hor : c,
  hiff_mp : e → f,
  hiff_mpr : f → e,
  hex_w : ℕ,
  hex_h : p hex_w,
  hand_right_left : b,
  hand_right_right : c
  ⊢ d -/
  repeat { sorry }
end


/- Question 2 **optional**: An `auto` Tactic -/

/- 2.1 **optional**. Develop an Isabelle-style `auto` tactic.

This tactic would apply all safe introduction and elimination rules. In
addition, it would try unsafe rules (such as `or.intro_left` and `false.elim`)
but backtrack at some point (or try several possibilities in parallel).
Iterative deepening may be a valid approach, or best-first search, or
breadth-first search. The tactic should also attempt to apply assumptions whose
conclusion matches the goal, but backtrack if necessary.

See also "Automatic Proof and Disproof in Isabelle/HOL"
(https://www.cs.vu.nl/~jbe248/frocos2011-dis-proof.pdf) by Blanchette, Bulwahn,
and Nipkow, and the references they give. -/

/- 2.2 **optional**. Test your tactic on some benchmarks.

You can try your tactic on logic puzzles of the kinds we proved in exercise 2
and homework 2. Please include these below. -/

end LoVe
