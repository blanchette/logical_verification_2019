/- LoVe Library -/

import tactic.explode
import tactic.find
import tactic.linarith
import tactic.rewrite
import tactic.tidy
import tactic.where
import logic.basic
import algebra
import order
import data.real.basic

namespace LoVe

/- Options -/

set_option pp.beta true


/- Logical connectives -/

attribute [pattern] or.intro_left or.intro_right

meta def tactic.dec_trivial := `[exact dec_trivial]

@[simp] lemma not_not_iff (a : Prop) [decidable a] : ¬¬ a ↔ a :=
by by_cases a; simp [h]

@[simp] lemma and_imp_distrib (a b c : Prop) : (a ∧ b → c) ↔ (a → b → c) :=
iff.intro
  (assume h ha hb, h ⟨ha, hb⟩)
  (assume h ⟨ha, hb⟩, h ha hb)

@[simp] lemma or_imp_distrib {a b c : Prop} : a ∨ b → c ↔ (a → c) ∧ (b → c) :=
iff.intro
  (assume h,
   ⟨assume ha, h (or.intro_left _ ha), assume hb, h (or.intro_right _ hb)⟩)
  (assume ⟨ha, hb⟩ h, match h with or.inl h := ha h | or.inr h := hb h end)

@[simp] lemma exists_imp_distrib {α : Sort*} {p : α → Prop} {a : Prop} :
  ((∃x, p x) → a) ↔ (∀x, p x → a) :=
iff.intro
  (assume h hp ha, h ⟨hp, ha⟩)
  (assume h ⟨hp, ha⟩, h hp ha)

lemma and_exists {α : Sort*} {p : α → Prop} {a : Prop} :
  (a ∧ (∃x, p x)) ↔ (∃x, a ∧ p x) :=
iff.intro
  (assume ⟨ha, x, hp⟩, ⟨x, ha, hp⟩)
  (assume ⟨x, ha, hp⟩, ⟨ha, x, hp⟩)

@[simp] lemma exists_false {α : Sort*} : (∃x : α, false) ↔ false :=
iff.intro (assume ⟨a, f⟩, f) (assume h, h.elim)


/- Reflexive transitive closure of a relation -/

inductive refl_trans {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {} : refl_trans a
| tail {b c} : refl_trans b → r b c → refl_trans c

attribute [refl] refl_trans.refl

namespace refl_trans

variables {α : Sort*} {r : α → α → Prop} {a b c d : α}

@[trans] lemma trans (hab : refl_trans r a b) (hbc : refl_trans r b c) :
  refl_trans r a c :=
begin
  induction hbc,
  case refl_trans.refl { assumption },
  case refl_trans.tail : c d hbc hcd hac { exact hac.tail hcd }
end

lemma single (hab : r a b) : refl_trans r a b :=
refl.tail hab

lemma head (hab : r a b) (hbc : refl_trans r b c) : refl_trans r a c :=
begin
  induction hbc,
  case refl_trans.refl { exact refl.tail hab },
  case refl_trans.tail : c d hbc hcd hac { exact hac.tail hcd }
end

lemma head_induction_on {α : Sort*} {r : α → α → Prop} {b : α}
  {P : ∀a : α, refl_trans r a b → Prop} {a : α} (h : refl_trans r a b)
  (refl : P b refl)
  (head : ∀{a c} (h' : r a c) (h : refl_trans r c b), P c h → P a (h.head h')) :
  P a h :=
begin
  induction h generalizing P,
  case refl_trans.refl { exact refl },
  case refl_trans.tail : b c hab hbc ih {
    apply ih,
    show P b _, from head hbc _ refl,
    show ∀a a', r a a' → refl_trans r a' b → P a' _ → P a _,
      from assume a a' hab hbc, head hab _ }
end

lemma trans_induction_on {α : Sort*} {r : α → α → Prop}
  {P : ∀{a b : α}, refl_trans r a b → Prop}
  {a b : α} (h : refl_trans r a b)
  (ih₁ : ∀a, @P a a refl)
  (ih₂ : ∀{a b} (h : r a b), P (single h))
  (ih₃ : ∀{a b c} (h₁ : refl_trans r a b) (h₂ : refl_trans r b c), P h₁ → P h₂ →
    P (h₁.trans h₂)) :
  P h :=
begin
  induction h,
  case refl_trans.refl { exact ih₁ a },
  case refl_trans.tail : b c hab hbc ih {
    exact ih₃ hab (single hbc) ih (ih₂ hbc) }
end

lemma lift {β : Sort*} {p : β → β → Prop} (f : α → β)
  (h : ∀a b, r a b → p (f a) (f b)) (hab : refl_trans r a b) :
  refl_trans p (f a) (f b) :=
hab.trans_induction_on
  (assume a, refl)
  (assume a b, single ∘ h _ _)
  (assume a b c _ _, trans)

lemma mono {p : α → α → Prop} :
  (∀a b, r a b → p a b) → refl_trans r a b → refl_trans p a b :=
lift id

lemma refl_trans_refl_trans_eq : refl_trans (refl_trans r) = refl_trans r :=
funext $ assume a, funext $ assume b, propext $
iff.intro
  (assume h, begin induction h, { refl }, { transitivity; assumption } end)
  (refl_trans.mono (assume a b, single))

end refl_trans


/- States -/

def state := string → ℕ

def state.update (name : string) (val : ℕ) (s : state) :
  state :=
λname', if name' = name then val else s name'

notation s `{` name ` ↦ ` val `}` := state.update name val s

instance : has_emptyc state := ⟨λ_, 0⟩

@[simp] lemma update_apply (name : string) (val : ℕ)
  (s : state) : s{name ↦ val} name = val :=
if_pos rfl

@[simp] lemma update_apply_ne (name name' : string) (val : ℕ)
    (s : state) (h : name' ≠ name . tactic.dec_trivial) :
  s{name ↦ val} name' = s name' :=
if_neg h

@[simp] lemma update_override (name : string) (val₁ val₂ : ℕ)
  (s : state) : s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp [h]
end

@[simp] lemma update_swap (name₁ name₂ : string) (val₁ val₂ : ℕ)
  (s : state) (h : name₁ ≠ name₂ . tactic.dec_trivial) :
  s{name₂ ↦ val₂}{name₁ ↦ val₁} =
  s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
  apply funext,
  intro name',
  by_cases name' = name₁;
    by_cases name' = name₂;
    simp * at *
end

@[simp] lemma update_id (name : string) (s : state) :
  s{name ↦ s name} = s :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp * at *
end

example (s : state) :
  s{"a" ↦ 0}{"a" ↦ 2} = s{"a" ↦ 2} :=
by simp

example (s : state) :
  s{"a" ↦ 0}{"b" ↦ 2} = s{"b" ↦ 2}{"a" ↦ 0} :=
by simp

example (s : state) :
  s{"a" ↦ s "a"}{"b" ↦ 0} = s{"b" ↦ 0} :=
by simp

end LoVe
