/- LoVe Demo 8: Operational Semantics -/

import .lovelib

namespace LoVe


/- A Minimalistic Imperative Language -/

inductive program : Type
| skip {} : program
| assign  : string → (state → ℕ) → program
| seq     : program → program → program
| ite     : (state → Prop) → program → program → program
| while   : (state → Prop) → program → program

infixr ` ;; `:90 := program.seq

export program (skip assign seq ite while)


/- Big-Step Semantics -/

inductive big_step : (program × state) → state → Prop
| skip {s} :
  big_step (skip, s) s
| assign {x a s} :
  big_step (assign x a, s) (s{x ↦ a s})
| seq {S T s t u} (h₁ : big_step (S, s) t)
    (h₂ : big_step (T, t) u) :
  big_step (S ;; T, s) u
| ite_true {b : state → Prop} {S₁ S₂ s t} (hcond : b s)
    (hbody : big_step (S₁, s) t) :
  big_step (ite b S₁ S₂, s) t
| ite_false {b : state → Prop} {S₁ S₂ s t} (hcond : ¬ b s)
    (hbody : big_step (S₂, s) t) :
  big_step (ite b S₁ S₂, s) t
| while_true {b : state → Prop} {S s t u} (hcond : b s)
    (hbody : big_step (S, s) t)
    (hrest : big_step (while b S, t) u) :
  big_step (while b S, s) u
| while_false {b : state → Prop} {S s} (hcond : ¬ b s) :
  big_step (while b S, s) s

infix ` ⟹ `:110 := big_step


/- Lemmas about the Big-Step Semantics -/

lemma big_step_unique {S s l r} (hl : (S, s) ⟹ l)
	  (hr : (S, s) ⟹ r) :
  l = r :=
begin
  induction hl generalizing r,
  { cases hr,
    refl },
  { cases hr,
    refl },
  { cases hr,
    rename hl_S S, rename hl_T T, rename hl_s s, rename hl_t t,
    rename hl_u l, rename hr_t t', rename hl_h₁ hSst,
    rename hl_h₂ hTtl, rename hr_h₂ hTt'r, rename hr_h₁ hSst',
    rename hl_ih_h₁ ihS, rename hl_ih_h₂ ihT,
    specialize ihS hSst',
    rw ihS at *,
    specialize ihT hTt'r,
    rw ihT at *},
  { cases hr,
    { apply hl_ih,
      cc },
    { apply hl_ih,
      cc } },
  { cases hr,
    { apply hl_ih,
      cc },
    { apply hl_ih,
      assumption } },
  { cases hr,
    { specialize hl_ih_hbody hr_hbody,
      rw hl_ih_hbody at *,
      specialize hl_ih_hrest hr_hrest,
      rw hl_ih_hrest at *},
    { cc } },
  { cases hr,
    { cc },
    { refl } }
end

@[simp] lemma big_step_skip_iff {s t} :
  (skip, s) ⟹ t ↔ t = s :=
begin
  apply iff.intro,
  { intro h,
    cases h,
    refl },
  { intro h,
    rw h,
    exact big_step.skip }
end

@[simp] lemma big_step_assign_iff {x a s t} :
  (assign x a, s) ⟹ t ↔ t = s{x ↦ a s} :=
begin
  apply iff.intro,
  { intro h,
    cases h,
    refl },
  { intro h,
    rw h,
    exact big_step.assign }
end

@[simp] lemma big_step_seq_iff {S₁ S₂ s t} :
  (S₁ ;; S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
begin
  apply iff.intro,
  { intro h,
    cases h,
    apply exists.intro,
    apply and.intro,
    repeat { assumption } },
  { intro h,
    cases h,
    cases h_h,
    apply big_step.seq,
    repeat { assumption } }
end

@[simp] lemma big_step_ite_iff {b S₁ S₂ s t} :
  (ite b S₁ S₂, s) ⟹ t ↔
  (b s ∧ (S₁, s) ⟹ t) ∨ (¬ b s ∧ (S₂, s) ⟹ t) :=
begin
  apply iff.intro,
  { intro h,
    cases h,
    { apply or.intro_left,
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases h;
    cases h,
    { apply big_step.ite_true,
      repeat { assumption }},
    { apply big_step.ite_false,
      repeat { assumption }}
  }
end

lemma big_step_while_iff {b S s u} :
  (while b S, s) ⟹ u ↔
  (∃t, b s ∧ (S, s) ⟹ t ∧ (while b S, t) ⟹ u)
  ∨ (¬ b s ∧ u = s) :=
begin
  apply iff.intro,
  { intro h,
    cases h,
    { apply or.intro_left,
      apply exists.intro h_t,
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases h,
    { cases h,
      cases h_h,
      cases h_h_right,
      apply big_step.while_true,
      repeat { assumption } },
    { cases h,
      rw h_right,
      apply big_step.while_false,
      assumption } }
end

@[simp] lemma big_step_while_true_iff {b : state → Prop} {S s u}
    (hcond : b s) :
  (while b S, s) ⟹ u ↔
  (∃t, (S, s) ⟹ t ∧ (while b S, t) ⟹ u) :=
by rw [big_step_while_iff]; simp [hcond]

@[simp] lemma big_step_while_false_iff {b : state → Prop}
    {S s t} (hcond : ¬ b s) :
  (while b S, s) ⟹ t ↔ t = s :=
by rw [big_step_while_iff]; simp [hcond]


/- Small-Step Semantics -/

inductive small_step : program × state → program × state → Prop
| assign {x a s} :
  small_step (assign x a, s) (skip, s{x ↦ a s})
| seq_step {S T s s'} (S') :
  small_step (S, s) (S', s') →
  small_step (S ;; T, s) (S' ;; T, s')
| seq_skip {T s} :
  small_step (skip ;; T, s) (T, s)
| ite_true {b : state → Prop} {S₁ S₂ s} :
  b s → small_step (ite b S₁ S₂, s) (S₁, s)
| ite_false {b : state → Prop} {S₁ S₂ s} :
  ¬ b s → small_step (ite b S₁ S₂, s) (S₂, s)
| while {b : state → Prop} {S s} :
  small_step (while b S, s) (ite b (S ;; while b S) skip, s)

infixr ` ⇒ ` := small_step
infixr ` ⇒* ` : 100 := refl_trans small_step


/- Lemmas about the Small-Step Semantics -/

@[simp] lemma small_step_skip {S s t} :
  ¬ ((skip, s) ⇒ (S, t)) :=
by intro h; cases h

lemma small_step_seq_iff {S T s Ut} :
  (S ;; T, s) ⇒ Ut ↔
  (∃S' t, (S, s) ⇒ (S', t) ∧ Ut = (S' ;; T, t))
  ∨ (S = skip ∧ Ut = (T, s)) :=
begin
  apply iff.intro,
  { intro h,
    cases h,
    { apply or.intro_left,
      apply exists.intro h_S',
      apply exists.intro h_s',
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases h,
    { cases h,
      cases h_h,
      cases h_h_h,
      rw h_h_h_right,
      apply small_step.seq_step,
      assumption },
    { cases h,
      rw [h_left, h_right],
      apply small_step.seq_skip } }
end

@[simp] lemma small_step_ite_iff {b S T s Us} :
  (ite b S T, s) ⇒ Us ↔
  (b s ∧ Us = (S, s)) ∨ (¬ b s ∧ Us = (T, s)) :=
begin
  apply iff.intro,
  { intro h,
    cases h,
    { apply or.intro_left,
      cc },
    { apply or.intro_right,
      cc } },
  { intro h,
    cases h,
    { cases h,
      rw h_right,
      apply small_step.ite_true,
      assumption },
    { cases h,
      rw h_right,
      apply small_step.ite_false,
      assumption } }
end


/- **optional** Correspondence between the Big-Step and the
Small-Step Semantics -/

lemma refl_trans_small_step_seq {S₁ S₂ s u}
    (h : (S₁, s) ⇒* (skip, u)) :
  (S₁ ;; S₂, s) ⇒* (skip ;; S₂, u) :=
begin
  apply refl_trans.lift
    (λSs : program × state, (Ss.1 ;; S₂, Ss.2)) _ h,
  intros Ss Ss' h,
  cases Ss,
  cases Ss',
  dsimp,
  apply small_step.seq_step,
  assumption
end

lemma big_step_imp_refl_trans_small_step {S s t}
    (h : (S, s) ⟹ t) :
  (S, s) ⇒* (skip, t) :=
begin
  induction h,
  case big_step.skip { refl },
  case big_step.assign {
    exact refl_trans.single small_step.assign },
  case big_step.seq : S₁ S₂ s t u h₁ h₂ ih₁ ih₂ {
    transitivity,
    exact refl_trans_small_step_seq ih₁,
    exact ih₂.head small_step.seq_skip },
  case big_step.ite_true : B S₁ S₂ s t hs hst ih {
    exact ih.head (small_step.ite_true hs) },
  case big_step.ite_false : B S₁ S₂ s t hs hst ih {
    exact ih.head (small_step.ite_false hs) },
  case big_step.while_true : B S s t u hs h₁ h₂ ih₁ ih₂ {
    exact (refl_trans.head (small_step.while)
      (refl_trans.head (small_step.ite_true hs)
         (refl_trans.trans (refl_trans_small_step_seq ih₁)
            (refl_trans.head small_step.seq_skip ih₂)))) },
  case big_step.while_false : c p s hs {
    exact (refl_trans.single small_step.while).tail
      (small_step.ite_false hs) }
end

lemma big_step_of_small_step_of_big_step {S₀ S₁ s₀ s₁ s₂} :
  (S₀, s₀) ⇒ (S₁, s₁) → (S₁, s₁) ⟹ s₂ → (S₀, s₀) ⟹ s₂ :=
begin
  generalize hv₀ : (S₀, s₀) = v₀,
  generalize hv₁ : (S₁, s₁) = v₀,
  intro h,
  induction h
      generalizing S₀ s₀ S₁ s₁ s₂;
    cases hv₁;
    clear hv₁;
    cases hv₀;
    clear hv₀;
    simp [*, big_step_while_true_iff] { contextual := tt },
  { intros u h₁ h₂,
    use u, 
    exact and.intro (h_ih rfl rfl h₁) h₂ }
end

lemma refl_trans_small_step_imp_big_step {S s t} :
  (S, s) ⇒* (skip, t) → (S, s) ⟹ t :=
begin
  generalize hv₀ : (S, s) = v₀,
  intro h,
  induction h
      using LoVe.refl_trans.head_induction_on
      with v₀ v₁ h h' ih
      generalizing S s;
    cases hv₀;
    clear hv₀,
  { exact big_step.skip },
  { cases v₁ with S' s',
    specialize ih rfl,
    exact big_step_of_small_step_of_big_step h ih }
end

lemma big_step_iff_refl_trans_small_step {S s t} :
  (S, s) ⟹ t ↔ (S, s) ⇒* (skip, t) :=
iff.intro
  big_step_imp_refl_trans_small_step
  refl_trans_small_step_imp_big_step

end LoVe
