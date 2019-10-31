/- LoVe Demo 2: Tactical Proofs -/

import .love01_definitions_and_lemma_statements_demo

namespace LoVe


/- Tactic Mode -/

lemma fst_of_two_props :
  ∀a b : Prop, a → b → a :=
begin
  intros a b,
  intros ha hb,
  apply ha
end

lemma fst_of_two_props₂ (a b : Prop) (ha : a) (hb : b) :
  a :=
begin
  apply ha
end


/- Basic Tactics -/

lemma prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
begin
  intro ha,
  apply hbc,
  apply hab,
  exact ha
end

lemma prop_comp₂ (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
begin
  intro,
  apply hbc,
  apply hab,
  assumption
end

lemma α_example {α β : Type} (f : α → β) :
  (λx, f x) = (λy, f y) :=
by refl

lemma β_example {α β : Type} (f : α → β) (a : α) :
  (λx, f x) a = f a :=
by refl

def double (n : ℕ) : ℕ :=
n + n

lemma δ_example (m : ℕ) :
  double m = m + m :=
by refl

lemma ζ_example :
  (let n : ℕ := 2 in n + n) = 4 :=
by refl

lemma η_example {α β : Type} (f : α → β) :
  (λx, f x) = f :=
by refl

lemma ι_example {α β : Type} (a : α) (b : β) :
  prod.fst (a, b) = a :=
by refl

lemma nat_exists_double_iden :
  ∃n : ℕ, double n = n :=
begin
  use 0,
  refl
end


/- Proofs about Logical Connectives and Quantifiers -/

-- introduction rules
#check true.intro
#check not.intro
#check and.intro
#check or.intro_left
#check or.intro_right
#check iff.intro
#check exists.intro

-- elimination rules
#check false.elim
#check and.elim_left
#check and.elim_right
#check or.elim
#check iff.elim_left
#check iff.elim_right
#check exists.elim

-- definition of `¬` and related lemmas
#print not
#check classical.em
#check classical.by_contradiction

lemma and_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
begin
  intro hab,
  apply and.intro,
  apply and.elim_right,
  exact hab,
  apply and.elim_left,
  exact hab
end

lemma and_swap₂ :
  ∀a b : Prop, a ∧ b → b ∧ a :=
begin
  intros a b hab,
  apply and.intro,
  { exact and.elim_right hab },
  { exact and.elim_left hab }
end

lemma or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
begin
  intros hab,
  apply or.elim hab,
  { intros ha,
    exact or.intro_right _ ha },
  { intros hb,
    exact or.intro_left _ hb }
end

lemma modus_ponens (a b : Prop) :
  (a → b) → a → b :=
begin
  intros hab ha,
  apply hab,
  exact ha
end

lemma modus_ponens₂ (a b : Prop) (hab : a → b) (hp : a) :
  b :=
begin
  apply hab,
  assumption
end

lemma proof_of_negation (a : Prop) :
  a → ¬¬ a :=
begin
  intro ha,
  apply not.intro,
  intro hna,
  apply hna,
  exact ha
end

lemma proof_of_negation₂ (a : Prop) :
  a → ¬¬ a :=
begin
  intros ha hna,
  apply hna,
  exact ha
end

lemma proof_by_contradiction (a : Prop) :
  ¬¬ a → a :=
begin
  intro hnna,
  apply classical.by_contradiction,
  exact hnna
end

lemma nat_exists_double_iden₂ :
  ∃n : ℕ, double n = n :=
begin
  apply exists.intro 0,
  refl
end


/- Rewriting Tactics -/

lemma proof_of_negation₃ (a : Prop) :
  a → ¬¬ a :=
begin
  dunfold not,
  intro ha,
  apply not.intro,
  intro hna,
  apply hna,
  exact ha
end


/- Proofs about Natural Numbers -/

lemma add_zero (n : ℕ) :
  add 0 n = n :=
begin
  induction n,
  { refl },
  { simp [add, n_ih] }
end

lemma add_zero₂ (n : ℕ) :
  add 0 n = n :=
begin
  induction n,
  case nat.zero {
    refl },
  case nat.succ : m ih {
    simp [add, ih] }
end

lemma add_zero₃ (n : ℕ) :
  add 0 n = n :=
by induction n; simp [add, *]

lemma add_succ (m n : ℕ) :
  add (nat.succ m) n = nat.succ (add m n) :=
begin
  induction n,
  case nat.zero {
    refl },
  case nat.succ : m ih {
    simp [add, ih] }
end

lemma add_comm (m n : ℕ) :
  add m n = add n m :=
begin
  induction n,
  case nat.zero {
    simp [add, add_zero] },
  case nat.succ : m ih {
    simp [add, add_succ, ih] }
end

lemma add_assoc (l m n : ℕ) :
  add (add l m) n = add l (add m n) :=
begin
  induction n,
  case nat.zero {
    refl },
  case nat.succ : m ih {
    simp [add, ih] }
end

-- type classes (useful for `ac_refl` below)
instance : is_commutative ℕ add := ⟨add_comm⟩
instance : is_associative ℕ add := ⟨add_assoc⟩

lemma mul_add (l m n : ℕ) :
  mul l (add m n) = add (mul l m) (mul l n) :=
begin
  induction n,
  case nat.zero {
    refl },
  case nat.succ : m ih {
    simp [add, mul, ih],
    ac_refl }
end


/- Management Tactics -/

lemma cleanup_example (a b c : Prop) (ha : a) (hb : b)
  (hab : a → b) (hbc : b → c) :
  c :=
begin
  revert a b c ha hb hab hbc,
  intros x y z hx hy hxy hyz,
  clear hx hxy x,
  apply hyz,
  clear hyz z,
  rename hy h,
  exact h
end

end LoVe
