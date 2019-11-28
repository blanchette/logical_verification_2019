/- LoVe Demo 10: Denotational Semantics -/

import .love08_operational_semantics_demo

namespace LoVe


/- Complete Lattices -/

class complete_lattice (α : Type)
  extends partial_order α :=
(Inf    : set α → α)
(Inf_le : ∀s a, a ∈ s → Inf s ≤ a)
(le_Inf : ∀s a, (∀a', a' ∈ s → a ≤ a') → a ≤ Inf s)


/- Instance for Complete Lattices: `set α` -/

namespace set

instance (α : Type) : complete_lattice (set α) :=
{ le          := (⊆),
  le_refl     :=
    assume s a h,
    h,
  le_trans    :=
    assume s t u hst htu a has,
    htu (hst has),
  le_antisymm :=
    begin
      intros s t hst hts,
      apply set.ext,
      intro a,
      apply iff.intro,
      apply hst,
      apply hts
    end,
  Inf         := λf, {a | ∀s, s ∈ f → a ∈ s},
  Inf_le      :=
    begin
      intros f s hsf a h,
      simp at h,
      exact h s hsf
    end,
  le_Inf      :=
    assume f s h a has t htf,
    h t htf has }

end set


/- Monotonicity of Functions -/

def monotone {α β : Type} [partial_order α] [partial_order β]
  (f : α → β) : Prop :=
∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

namespace monotone

lemma id {α : Type} [partial_order α] :
  monotone (λa : α, a) :=
assume a₁ a₂ ha,
ha

lemma const {α β : Type} [partial_order α] [partial_order β]
    (b : β) :
  monotone (λa : α, b) :=
assume a₁ a₂ ha,
le_refl b

lemma union {α β : Type} [partial_order α] (f g : α → set β)
    (hf : monotone f) (hg : monotone g) :
  monotone (λa, f a ∪ g a) :=
begin
  intros a₁ a₂ ha b hb,
  cases hb,
  { exact or.intro_left _ (hf a₁ a₂ ha hb) },
  { exact or.intro_right _ (hg a₁ a₂ ha hb) }
end

end monotone


/- Least Fixpoint -/

namespace complete_lattice

variables {α : Type} [complete_lattice α]

def lfp (f : α → α) : α :=
Inf {x | f x ≤ x}

lemma lfp_le (f : α → α) (a : α) (h : f a ≤ a) :
  lfp f ≤ a :=
Inf_le _ _ h

lemma le_lfp (f : α → α) (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
  a ≤ lfp f :=
le_Inf _ _ h

lemma lfp_eq (f : α → α) (hf : monotone f) :
  lfp f = f (lfp f) :=
begin
  have h : f (lfp f) ≤ lfp f :=
    begin
      apply le_lfp,
      intros a' ha',
      apply @le_trans _ _ _ (f a'),
      { apply hf,
        apply lfp_le,
        assumption },
      { assumption }
    end,
  apply le_antisymm,
  { apply lfp_le,
    apply hf,
    assumption },
  { assumption }
end

end complete_lattice


/- Relations -/

def Id (α : Type) : set (α × α) :=
{x | x.2 = x.1}

@[simp] lemma mem_Id {α : Type} (a b : α) :
  (a, b) ∈ Id α ↔ b = a :=
iff.rfl

def comp {α : Type} (r₁ r₂ : set (α × α)) : set (α × α) :=
{x | ∃y, (x.1, y) ∈ r₁ ∧ (y, x.2) ∈ r₂}

infixl ` ◯ ` : 90 := comp

@[simp] lemma mem_comp {α : Type} (r₁ r₂ : set (α × α))
    (a b : α) :
  (a, b) ∈ r₁ ◯ r₂ ↔ (∃c, (a, c) ∈ r₁ ∧ (c, b) ∈ r₂) :=
iff.rfl

def restrict {α : Type} (r : set (α × α)) (b : α → Prop) :
  set (α × α) :=
{x | b x.1 ∧ x ∈ r}

infixl ` ⇃ ` : 90 := restrict

@[simp] lemma mem_restrict {α : Type} (r : set (α × α))
    (p : α → Prop) (a b : α) :
  (a, b) ∈ r ⇃ p ↔ p a ∧ (a, b) ∈ r :=
by refl

/- We will prove the following two lemmas in the exercise. -/

namespace sorry_lemmas

lemma monotone_comp {α β : Type} [partial_order α]
    (f g : α → set (β × β)) (hf : monotone f)
    (hg : monotone g) :
  monotone (λa, f a ◯ g a) :=
sorry

lemma monotone_restrict {α β : Type} [partial_order α]
    (f : α → set (β × β)) (p : β → Prop) (hf : monotone f) :
  monotone (λa, f a ⇃ p) :=
sorry

end sorry_lemmas


/- A Relational Denotational Semantics -/

def den : program → set (state × state)
| skip          := Id state
| (assign n a)  := {x | x.2 = x.1{n ↦ a x.1}}
| (seq S₁ S₂)   := den S₁ ◯ den S₂
| (ite b S₁ S₂) := (den S₁ ⇃ b) ∪ (den S₂ ⇃ λs, ¬ b s)
| (while b S)   :=
  complete_lattice.lfp
    (λX, ((den S ◯ X) ⇃ b) ∪ (Id state ⇃ λs, ¬ b s))

notation `⟦` S `⟧`:= den S

lemma den_while (S : program) (b : state → Prop) :
  ⟦while b S⟧ = ⟦ite b (S ;; while b S) skip⟧ :=
begin
  apply complete_lattice.lfp_eq,
  apply monotone.union,
  { apply sorry_lemmas.monotone_restrict,
    apply sorry_lemmas.monotone_comp,
    { exact monotone.const _ },
    { exact monotone.id } },
  { exact monotone.const _ }
end


/- (**optional**) Equivalence of the Denotational and the
Big-Step Semantics -/

lemma den_of_big_step (S : program) (s t : state) :
  (S, s) ⟹ t → (s, t) ∈ ⟦S⟧ :=
begin
  generalize eq : (S, s) = Ss,
  intro h,
  induction h generalizing eq S s;
    cases eq;
      -- simplify only if `simp` solves the goal completely
      try { simp [den, *], done },
  { use h_t,
    exact and.intro (h_ih_h₁ _ _ rfl) (h_ih_h₂ _ _ rfl) },
  { rw [den_while, den],
    simp [*],
    use h_t,
    exact and.intro (h_ih_hbody _ _ rfl) (h_ih_hrest _ _ rfl) },
  { rw [den_while],
    simp [den, *] }
end

lemma big_step_of_den :
  ∀(S : program) (s t : state), (s, t) ∈ ⟦S⟧ → (S, s) ⟹ t
| skip s t          :=
  by simp [den] { contextual := tt };
    exact _
| (assign n a)  s t  :=
  by simp [den] { contextual := tt }
| (seq S₁ S₂)   s t   :=
  begin
    intro h,
    cases h with u hu,
    exact big_step.seq
      (big_step_of_den S₁ _ _ (and.elim_left hu))
      (big_step_of_den S₂ _ _ (and.elim_right hu))
  end
| (ite b S₁ S₂) s t :=
  assume h,
  match h with
  | or.intro_left  _ (and.intro hs hst) :=
    big_step.ite_true hs (big_step_of_den S₁ _ _ hst)
  | or.intro_right _ (and.intro hs hst) :=
    big_step.ite_false hs (big_step_of_den S₂ _ _ hst)
  end
| (while b S)   s t :=
  begin
    have hw : ⟦while b S⟧ ≤ {x | (while b S, x.1) ⟹ x.2} :=
      begin
        apply complete_lattice.lfp_le _ _ _,
        intros x hx,
        cases x with s t,
        simp at hx,
        cases hx,
        { cases hx with hs hst,
          cases hst with u hu,
          apply big_step.while_true hs,
          { exact big_step_of_den S _ _ (and.elim_left hu) },
          { exact and.elim_right hu } },
        { cases hx,
          cases hx_right,
          apply big_step.while_false hx_left }
      end,
    apply hw
  end

lemma den_eq_bigstep (S : program) (s t : state) :
  (s, t) ∈ ⟦S⟧ ↔ (S, s) ⟹ t :=
iff.intro (big_step_of_den S s t) (den_of_big_step S s t)

end LoVe
