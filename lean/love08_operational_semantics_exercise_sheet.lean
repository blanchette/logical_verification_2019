/- LoVe Exercise 8: Operational Semantics -/

import .love08_operational_semantics_demo

namespace LoVe


/- Question 1: Program Equivalence -/

/- For this question, we introduce the notation of program equivalence
`p₁ ≈ p₂`. -/

def program_equiv (S₁ S₂ : program) : Prop :=
∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

local infix ` ≈ ` := program_equiv

/- Program equivalence is a equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

@[refl] lemma program_equiv.refl {S} :
  S ≈ S :=
assume s t,
show (S, s) ⟹ t ↔ (S, s) ⟹ t,
  by refl

@[symm] lemma program_equiv.symm {S₁ S₂}:
  S₁ ≈ S₂ → S₂ ≈ S₁ :=
assume h s t,
show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t,
  from iff.symm (h s t)

@[trans] lemma program_equiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ≈ S₂) (h₂₃ : S₂ ≈ S₃) :
  S₁ ≈ S₃ :=
assume s t,
show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t,
  from iff.trans (h₁₂ s t) (h₂₃ s t)


/- 1.1. Prove the following program equivalences. -/

lemma program_equiv.seq_skip_left {S} :
  skip ;; S ≈ S :=
sorry

lemma program_equiv.seq_skip_right {S} :
  S ;; skip ≈ S :=
sorry

lemma program_equiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ≈ S₂) (hT : T₁ ≈ T₂) :
  S₁ ;; T₁ ≈ S₂ ;; T₂ :=
sorry

lemma program_equiv.ite_seq_while {b S} :
  ite b (S ;; while b S) skip ≈ while b S :=
sorry

/- 1.2. Prove one more equivalence. -/

lemma program_equiv.skip_assign_id {x} :
  assign x (λs, s x) ≈ skip :=
sorry


/- Question 2: Guarded Command Language (GCL) -/

/- In 1976, E. W. Dijkstra introduced the guarded command language, a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert b     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert b` aborts if `b` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses **any** of the branches and executes it, ignoring the
  other branches.

* `loop S` executes `S` **any** number of times.

In Lean, GCL is captured by the following inductive type: -/

inductive gcl (σ : Type) : Type
| assign : string → (σ → ℕ) → gcl
| assert : (σ → Prop) → gcl
| seq    : gcl → gcl → gcl
| choice : list gcl → gcl
| loop   : gcl → gcl

infixr ` ;; `:90 := gcl.seq

namespace gcl

/- The parameter `σ` abstracts over the state type. It is necessary to work
around a bug in Lean.

The big-step semantics is defined as follows: -/

inductive big_step : (gcl state × state) → state → Prop
| assign {x a s} :
  big_step (assign x a, s) (s{x ↦ a s})
| assert {b : state → Prop} {s} (hcond : b s) :
  big_step (assert b, s) s
| seq {S T s t u} (h₁ : big_step (S, s) t) (h₂ : big_step (T, t) u) :
  big_step (S ;; T, s) u
| choice {Ss : list (gcl state)} {s t} (i : ℕ) (hless : i < list.length Ss)
    (hbody : big_step (list.nth_le Ss i hless, s) t) :
  big_step (choice Ss, s) t
| loop_base {S s} :
  big_step (loop S, s) s
| loop_step {S s u} (t) (hbody : big_step (S, s) t)
    (hrest : big_step (loop S, t) u) :
  big_step (loop S, s) u

/- Convenience syntax: -/

infix ` ~~> `:110 := big_step

/- 2.1. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] lemma big_step_assign_iff {x a s t} :
  (assign x a, s) ~~> t ↔ t = s{x ↦ a s} :=
sorry

@[simp] lemma big_step_assert {b s t} :
  (assert b, s) ~~> t ↔ t = s ∧ b s :=
sorry

@[simp] lemma big_step_seq_iff {S₁ S₂ s t} :
  (S₁ ;; S₂, s) ~~> t ↔ (∃u, (S₁, s) ~~> u ∧ (S₂, u) ~~> t) :=
sorry

lemma big_step_loop {S s u} :
  (loop S, s) ~~> u ↔ (s = u ∨ (∃t, (S, s) ~~> t ∧ (loop S, t) ~~> u)) :=
sorry

@[simp] lemma big_step_choice {Ss s t} :
  (choice Ss, s) ~~> t ↔
  (∃(i : ℕ) (hless : i < list.length Ss),
    (list.nth_le Ss i hless, s) ~~> t) :=
sorry

/- 2.2. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def of_program : program → gcl state
| program.skip          := assert (λ_, true)
| (program.assign x f)  :=
  sorry
| (program.seq S₁ S₂)   :=
  sorry
| (program.ite b S₁ S₂) :=
  choice [seq (assert b) (of_program S₁),
    seq (assert (λs, ¬ b s)) (of_program S₂)]
| (program.while b S)   :=
  seq (loop (seq (assert b) (of_program S))) (assert (λs, ¬ b s))

/- 2.3. In the definition of `of_program` above, `skip` is translated to
`assert (λ_, true)`. Looking at the big-step semantics of both constructs, we
can convince ourselves that it makes sense. Can you think of other correct ways
to define the `skip` case? -/

-- enter your answer here

end gcl

end LoVe
