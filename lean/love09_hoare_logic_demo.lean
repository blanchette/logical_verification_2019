/- LoVe Demo 9: Hoare Logic -/

import .love08_operational_semantics_demo

namespace LoVe


/- Hoare Logic: The Semantic Approach -/

variables {b : state → Prop} {a : state → ℕ} {x : string}
variables {S S₀ S₁ S₂ : program} {s s₀ s₁ s₂ t u : state}
variables {P P' P₁ P₂ P₃ Q Q' : state → Prop}

def partial_hoare (P : state → Prop) (S : program)
  (Q : state → Prop) : Prop :=
∀s t, P s → (S, s) ⟹ t → Q t

notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` :=
partial_hoare P S Q

namespace partial_hoare

lemma skip_intro :
  {* P *} skip {* P *} :=
begin
  intros s t hs hst,
  cases hst,
  assumption
end

lemma assign_intro (P : state → Prop) :
  {* λs, P (s{x ↦ a s}) *} assign x a {* P *} :=
begin
  intros s t P hst,
  cases hst,
  assumption
end

lemma seq_intro (h₁ : {* P₁ *} S₁ {* P₂ *})
    (h₂ : {* P₂ *} S₂ {* P₃ *}) :
  {* P₁ *} S₁ ;; S₂ {* P₃ *} :=
begin
  intros s t P hst,
  cases hst,
  apply h₂ _ _ _ hst_h₂,
  apply h₁ _ _ _ hst_h₁,
  assumption
end

lemma ite_intro (h₁ : {* λs, P s ∧ b s *} S₁ {* Q *})
    (h₂ : {* λs, P s ∧ ¬ b s *} S₂ {* Q *}) :
  {* P *} ite b S₁ S₂ {* Q *} :=
begin
  intros s t hs hst,
  cases hst,
  { apply h₁ _ _ _ hst_hbody,
    exact and.intro hs hst_hcond },
  { apply h₂ _ _ _ hst_hbody,
    exact and.intro hs hst_hcond },
end

lemma while_intro (P : state → Prop)
    (h₁ : {* λs, P s ∧ b s *} S {* P *}) :
  {* P *} while b S {* λs, P s ∧ ¬ b s *} :=
begin
  intros s t hs,
  generalize eq : (while b S, s) = ws,
  intro hst,
  induction hst generalizing s;
    cases eq,
  { apply hst_ih_hrest hst_t _ rfl,
    exact h₁ _ _ (and.intro hs hst_hcond) hst_hbody },
  { exact (and.intro hs hst_hcond) }
end

lemma consequence (h : {* P *} S {* Q *}) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
  {* P' *} S {* Q' *} :=
assume s t hs hst,
show Q' t,
  from hq _ (h s t (hp s hs) hst)

lemma consequence_left (P' : state → Prop)
    (h : {* P *} S {* Q *}) (hp : ∀s, P' s → P s) :
  {* P' *} S {* Q *} :=
consequence h hp (assume s hs, hs)

lemma consequence_right (Q : state → Prop)
    (h : {* P *} S {* Q *}) (hq : ∀s, Q s → Q' s) :
  {* P *} S {* Q' *} :=
consequence h (assume s hs, hs) hq

lemma skip_intro' (h : ∀s, P s → Q s):
  {* P *} skip {* Q *} :=
consequence skip_intro h (assume s hs, hs)

lemma assign_intro' (h : ∀s, P s → Q (s{x ↦ a s})):
  {* P *} assign x a {* Q *} :=
consequence (assign_intro Q) h (assume s hs, hs)

lemma seq_intro' (h₂ : {* P₂ *} S₂ {* P₃ *})
    (h₁ : {* P₁ *} S₁ {* P₂ *}) :
  {* P₁ *} S₁ ;; S₂ {* P₃ *} :=
seq_intro h₁ h₂

lemma while_intro' (I : state → Prop)
    (h₁ : {* λs, I s ∧ b s *} S {* I *}) (hp : ∀s, P s → I s)
    (hq : ∀s, ¬ b s → I s → Q s) :
  {* P *} while b S {* Q *} :=
consequence (while_intro I h₁) hp
  (assume s h, hq s (and.elim_right h) (and.elim_left h))

end partial_hoare


/- Example: Exchanging Two Variables -/

section SWAP

def SWAP : program :=
assign "t" (λs, s "a") ;;
assign "a" (λs, s "b") ;;
assign "b" (λs, s "t")

lemma SWAP_correct (x y : ℕ) :
  {* λs, s "a" = x ∧ s "b" = y *} SWAP
  {* λs, s "a" = y ∧ s "b" = x *} :=
begin
  apply partial_hoare.seq_intro',
  apply partial_hoare.seq_intro',
  apply partial_hoare.assign_intro,
  apply partial_hoare.assign_intro,
  apply partial_hoare.assign_intro',
  simp { contextual := tt }
end

end SWAP


/- Example: Adding Two Numbers -/

section ADD

def ADD : program :=
while (λs, s "n" ≠ 0)
  (assign "n" (λs, s "n" - 1) ;;
   assign "m" (λs, s "m" + 1))

lemma ADD_correct (n₀ m₀ : ℕ) :
  {* λs, s "n" = n₀ ∧ s "m" = m₀ *} ADD
  {* λs, s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
begin
  refine partial_hoare.while_intro'
    (λs, s "n" + s "m" = n₀ + m₀) _ _ _,
  apply partial_hoare.seq_intro',
  apply partial_hoare.assign_intro,
  apply partial_hoare.assign_intro',
  { simp,
    -- this looks much better: `simp` removed all updates
    intros s hnm hn0,
    rw ←hnm,
    -- subtracting on `ℕ` is annoying
    cases s "n",
    { apply false.elim, apply hn0, refl },
    { simp [nat.succ_eq_add_one] } },
  { simp { contextual := tt } },
  { simp [not_not_iff] { contextual := tt } }
end

end ADD


/- A Verification Condition Generator -/

def program.while_inv (I : state → Prop) (c : state → Prop)
  (p : program) : program :=
while c p

export program (while_inv)

namespace partial_hoare

lemma while_inv_intro {I : state → Prop}
    (h₁ : {* λs, I s ∧ b s *} S {* I *})
    (hq : ∀s, ¬ b s → I s → Q s) :
  {* I *} while_inv I b S {* Q *} :=
while_intro' I h₁ (assume s hs, hs) hq

lemma while_inv_intro' {I : state → Prop}
    (h₁ : {* λs, I s ∧ b s *} S {* I *}) (hp : ∀s, P s → I s)
    (hq : ∀s, ¬ b s → I s → Q s) :
  {* P *} while_inv I b S {* Q *} :=
while_intro' I h₁ hp hq

end partial_hoare

end LoVe

namespace tactic.interactive

open LoVe

meta def is_meta : expr → bool
| (expr.mvar _ _ _) := tt
| _                 := ff

meta def vcg : tactic unit := do
  t ← tactic.target,
  match t with
  | `({* %%P *} %%S {* _ *}) :=
    match S with
    | `(program.skip)            :=
      tactic.applyc
        (if is_meta P then ``partial_hoare.skip_intro
         else ``partial_hoare.skip_intro')
    | `(program.assign _ _)      :=
      tactic.applyc
        (if is_meta P then ``partial_hoare.assign_intro
         else ``partial_hoare.assign_intro')
    | `(program.seq _ _)         :=
      tactic.applyc ``partial_hoare.seq_intro';
        vcg
    | `(program.ite _ _ _)       :=
      tactic.applyc ``partial_hoare.ite_intro;
        vcg
    | `(program.while_inv _ _ _) :=
      tactic.applyc
          (if is_meta P then ``partial_hoare.while_inv_intro
           else ``partial_hoare.while_inv_intro');
        vcg
    | _                          :=
      tactic.fail (to_fmt "cannot analyze " ++ to_fmt S)
    end
  | _                        := pure ()
  end

end tactic.interactive


/- Example: Adding Two Numbers, Revisited -/

namespace LoVe

lemma ADD_correct₂ (n₀ m₀ : ℕ) :
  {* λs, s "n" = n₀ ∧ s "m" = m₀ *} ADD
  {* λs, s "n" = 0 ∧ s "m" = n₀ + m₀ *} :=
show
  {* λs, s "n" = n₀ ∧ s "m" = m₀ *}
  while_inv (λs, s "n" + s "m" = n₀ + m₀) (λs, s "n" ≠ 0)
    (assign "n" (λs, s "n" - 1) ;;
     assign "m" (λs, s "m" + 1))
  {* λs, s "n" = 0 ∧ s "m" = n₀ + m₀ *},
begin
  vcg;
    simp { contextual := tt },
  intros s hnm hn,
  rw ←hnm,
  cases s "n",
  { contradiction },
  { simp [nat.succ_eq_add_one] }
end

end LoVe
