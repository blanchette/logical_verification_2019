/- LoVe Exercise 9: Hoare Logic -/

import .love09_hoare_logic_demo

namespace LoVe


/- Question 1: Program Verification -/

section GAUSS

/- The following WHILE program is intended to compute the Gaussian sum up to
`n`, leaving the result in `r`. -/

def GAUSS : program :=
assign "r" (λs, 0) ;;
while (λs, s "n" ≠ 0)
  (assign "r" (λs, s "r" + s "n") ;;
   assign "n" (λs, s "n" - 1))

/- The summation function: -/

def sum_upto : ℕ → ℕ
| 0       := 0
| (n + 1) := n + 1 + sum_upto n

/- 1.1. Prove the correctness of `GAUSS`, using `vcg`. The main challenge is to
figure out which invariant to use for the while loop. The invariant should
capture both the work that has been done already (the intermediate result) and
the work that remains to be done. -/

lemma GAUSS_correct (n : ℕ) :
  {* λs, s "n" = n *} GAUSS {* λs, s "r" = sum_upto n *} :=
show
  {* λs, s "n" = n *}
  assign "r" (λs, 0) ;;
  while_inv (λs, s "r" + sum_upto (s "n") = sum_upto n) (λs, s "n" ≠ 0)
    (assign "r" (λs, s "r" + s "n") ;;
     assign "n" (λs, s "n" - 1))
  {* λs, s "r" = sum_upto n *},
begin
  vcg;
    simp [sum_upto] { contextual := tt },
  intro s,
  cases s "n",
  { simp },
  { simp [nat.succ_eq_add_one, sum_upto, mul_assoc] { contextual := tt } }
end

end GAUSS

section MUL

/- The following WHILE program is intended to compute the product of `n` and
`m`, leaving the result in `r`. -/

def MUL : program :=
assign "r" (λs, 0) ;;
while (λs, s "n" ≠ 0)
  (assign "r" (λs, s "r" + s "m") ;;
   assign "n" (λs, s "n" - 1))

/- 1.2 Prove the correctness of `MUL`, using `vcg`.

Hint: If a variable `x` does not change in a program, it might be useful to
record this in the invariant, by adding a conjunct `s "x" = x`. -/

lemma MUL_correct (n m : ℕ) :
  {* λs, s "n" = n ∧ s "m" = m *} MUL {* λs, s "r" = n * m *} :=
show
  {* λs, s "n" = n ∧ s "m" = m *}
  assign "r" (λs, 0) ;;
  while_inv (λs, s "m" = m ∧ s "r" + s "n" * s "m" = n * s "m") (λs, s "n" ≠ 0)
    (assign "r" (λs, s "r" + s "m") ;;
     assign "n" (λs, s "n" - 1))
  {* λs, s "r" = n * m *},
begin
  vcg;
    simp { contextual := tt },
  intro s,
  cases s "n",
  { simp },
  { simp [nat.succ_eq_add_one, add_mul] { contextual := tt } }
end

end MUL


/- Question 2: Hoare Triples for Total Correctness -/

def total_hoare (P : state → Prop) (p : program) (Q : state → Prop) : Prop :=
∀s, P s → ∃t, (p, s) ⟹ t ∧ Q t

notation `[* ` P : 1 ` *] ` p : 1 ` [* ` Q : 1 ` *]` := total_hoare P p Q

namespace total_hoare

variables {P P' P₁ P₂ P₃ Q Q' : state → Prop} {x : string}
variables {S S₀ S₁ S₂ : program}
variables {b : state → Prop} {a : state → ℕ} {s s₀ s₁ s₂ t u : state}

/- 2.1. Prove the consequence rule. -/

lemma consequence (h : [* P *] S [* Q *]) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
  [* P' *] S [* Q' *] :=
begin
  intros s hs,
  specialize h s (hp s hs),
  cases h with t ht,
  use t,
  apply and.intro,
  { exact and.elim_left ht },
  { exact hq t (and.elim_right ht) }
end

/- 2.2. Prove the rule for `skip`. -/

lemma skip_intro :
  [* P *] skip [* P *] :=
begin
  intros s hs,
  use s,
  apply and.intro big_step.skip hs
end

/- 2.3. Prove the rule for `assign`. -/

lemma assign_intro (P : state → Prop) :
  [* λs, P (s{x ↦ a s}) *] assign x a [* P *] :=
begin
  intros s hs, 
  use s{x ↦ a s}, 
  exact and.intro big_step.assign hs
end

/- 2.4. Prove the rule for `seq`. -/

lemma seq_intro (h₁ : [* P₁ *] S₁ [* P₂ *])
    (h₂ : [* P₂ *] S₂ [* P₃ *]) :
  [* P₁ *] S₁ ;; S₂ [* P₃ *] :=
begin
  intros s hs,
  specialize h₁ s hs,
  cases h₁ with t h₁,
  specialize h₂ t (and.elim_right h₁),
  cases h₂ with u h₂,
  use u,
  apply and.intro,
  { exact big_step.seq (and.elim_left h₁) (and.elim_left h₂) },
  { exact and.elim_right h₂ }
end

/- 2.5 **optional**. Prove the rule for `ite`. This requires `b s ∨ ¬ b s`.
`classical.em (b s)` provides a proof, even when `b` is not decidable. -/

lemma ite_intro (h₁ : [* λs, P s ∧ b s *] S₁ [* Q *])
  (h₂ : [* λs, P s ∧ ¬ b s *] S₂ [* Q *]) :
  [* P *] ite b S₁ S₂ [* Q *] :=
begin
  intros s hs,
  cases classical.em (b s),
  { cases h₁ s (and.intro hs h) with t ht,
    use t,
    apply and.intro,
    { exact big_step.ite_true h (and.elim_left ht) },
    { exact and.elim_right ht } },
  { cases h₂ s (and.intro hs h) with t ht,
    use t,
    apply and.intro,
    { exact big_step.ite_false h (and.elim_left ht) }, 
    { exact and.elim_right ht } }
end

/- 2.6 **optional**. Try to prove the rule for `while`.

Before we prove our final goal, we introduce an auxiliary proof. This proof
requires well-founded induction. When using `while_intro.aux` as induction
hypothesis we recommend to do it directly after proving that the argument is
less than `n`:

    have ih : ∃u, (while c p, t) ⟹ u ∧ I u ∧ ¬ c u :=
      have M < n := …,
        -- necessary for Lean to figure out the well-founded induction
      while_intro.aux M …,

Similar to `ite`, this requires `c s ∨ ¬ c s`. `classical.em (c s)` provides a
proof. -/

lemma while_intro.aux
  (I : state → Prop)
  (V : state → ℕ)
  (h_inv : ∀n, [* λs, I s ∧ b s ∧ V s = n *] S [* λs, I s ∧ V s < n *]) :
  ∀n s, V s = n → I s → ∃t, (while b S, s) ⟹ t ∧ I t ∧ ¬ b t
| n s V_eq hs :=
  begin
    cases classical.em (b s) with hcs hncs,
    { have h_inv : ∃ t, (S, s) ⟹ t ∧ I t ∧ V t < n :=
        h_inv n s (and.intro hs (and.intro hcs V_eq)),
      cases h_inv with t ht,
      have ih : ∃u, (while b S, t) ⟹ u ∧ I u ∧ ¬ b u :=
        have V t < n := and.elim_right (and.elim_right ht),
        while_intro.aux (V t) t rfl (and.elim_left (and.elim_right ht)),
      cases ih with u hu,
      use u,
      apply and.intro,
      { exact big_step.while_true hcs (and.elim_left ht) (and.elim_left hu) },
      { exact and.elim_right hu } },
    { use s, 
      apply and.intro,
      { exact big_step.while_false hncs }, 
      { exact and.intro hs hncs } }
  end

lemma while_intro
  (I : state → Prop)   -- invariant in the loop
  (V : state → ℕ)      -- variant in the loop body (a.k.a. termination measure)
  (h_inv : ∀n, [* λs, I s ∧ b s ∧ V s = n *] S [* λs, I s ∧ V s < n *]) :
  [* I *] while b S [* λs, I s ∧ ¬ b s *] :=
begin
  intros s hs,
  exact while_intro.aux I V h_inv (V s) s rfl hs
end

end total_hoare

end LoVe
