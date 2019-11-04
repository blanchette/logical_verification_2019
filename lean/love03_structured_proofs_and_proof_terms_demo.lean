/- LoVe Demo 3: Structured Proofs and Proof Terms -/

import .love01_definitions_and_lemma_statements_demo

namespace LoVe


/- Structured Proofs -/

lemma add_comm_zero_left (n : ℕ):
  add 0 n = add n 0 :=
add_comm 0 n

lemma add_comm_zero_left₂ (n : ℕ):
  add 0 n = add n 0 :=
by exact add_comm 0 n

lemma fst_of_two_props :
  ∀a b : Prop, a → b → a :=
assume a b ha hb,
show a, from ha

lemma fst_of_two_props₂ (a b : Prop) (ha : a) (hb : b) :
  a :=
show a,
begin
  exact ha
end

lemma fst_of_two_props₃ (a b : Prop) (ha : a) (hb : b) :
  a :=
ha

lemma prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
assume ha,
have hb : b := hab ha,
have hc : c := hbc hb,
show c, from hc

lemma β_example {α β : Type} (f : α → β) (a : α) :
  (λx, f x) a = f a :=
rfl

def double (n : ℕ) : ℕ :=
n + n

lemma nat_exists_double_iden :
  ∃n : ℕ, double n = n :=
exists.intro 0
  (show double 0 = 0, from rfl)

lemma nat_exists_double_iden₂ :
  ∃n : ℕ, double n = n :=
exists.intro 0 rfl

lemma nat_exists_double_iden₃ :
  ∃n : ℕ, double n = n :=
exists.intro 0 (by refl)

lemma and_swap (a b : Prop) :
  a ∧ b → b ∧ a :=
assume hab : a ∧ b,
have ha : a := and.elim_left hab,
have hb : b := and.elim_right hab,
show b ∧ a, from and.intro hb ha

lemma and_swap₂ (a b : Prop) :
  a ∧ b → b ∧ a :=
assume hab : a ∧ b,
have ha : a := and.elim_left hab,
have hb : b := and.elim_right hab,
begin
  apply and.intro,
  { exact hb },
  { exact ha }
end

lemma or_swap (a b : Prop) :
  a ∨ b → b ∨ a :=
assume hab : a ∨ b,
show b ∨ a, from or.elim hab
  (assume ha,
   show b ∨ a, from or.intro_right b ha)
  (assume hb,
   show b ∨ a, from or.intro_left a hb)

lemma modus_ponens (a b : Prop) :
  (a → b) → a → b :=
assume (hab : a → b) (ha : a),
show b, from hab ha

lemma proof_of_negation (a : Prop) :
  a → ¬¬ a :=
assume ha hna,
show false, from hna ha

#check classical.by_contradiction

lemma proof_by_contradiction (a : Prop) :
  ¬¬ a → a :=
assume hnna,
show a, from classical.by_contradiction hnna

lemma exists_or {α : Type} (p q : α → Prop) :
  (∃x, p x ∨ q x) ↔ (∃x, p x) ∨ (∃x, q x) :=
iff.intro
  (assume hxpq,
   match hxpq with
   | Exists.intro x hpq :=
     match hpq with
     | or.inl hp := or.intro_left _ (exists.intro x hp)
     | or.inr hq := or.intro_right _ (exists.intro x hq)
     end
   end)
  (assume hxpq,
   match hxpq with
   | or.inl hxp :=
     match hxp with
     | Exists.intro x hp := exists.intro x (or.intro_left _ hp)
     end
   | or.inr hxq :=
     match hxq with
     | Exists.intro x hq := exists.intro x (or.intro_right _ hq)
     end
   end)


/- Calculational Proofs -/

lemma two_mul_example (m n : ℕ) :
  2 * m + n = m + n + m :=
calc 2 * m + n = (m + m) + n : by rw two_mul
... = m + n + m : by ac_refl

lemma two_mul_example₂ (m n : ℕ) :
  2 * m + n = m + n + m :=
have h₁ : 2 * m + n = (m + m) + n := by rw two_mul,
have h₂ : (m + m) + n = m + n + m := by ac_refl,
show _, from eq.trans h₁ h₂


/- Induction by Pattern Matching -/

lemma add_zero :
  ∀n : ℕ, add 0 n = n
| 0            := by refl
| (nat.succ m) := by simp [add, add_zero m]

lemma add_succ :
  ∀m n : ℕ, add (nat.succ m) n = nat.succ (add m n)
| m 0            := by refl
| m (nat.succ n) := by simp [add, add_succ m n]

lemma add_comm :
  ∀m n : ℕ, add m n = add n m
| m 0            := by simp [add, add_zero]
| m (nat.succ n) := by simp [add, add_succ, add_comm m n]

lemma add_comm₂ :
  ∀m n : ℕ, add m n = add n m
| m 0            := by simp [add, add_zero]
| m (nat.succ n) :=
  have ih : _ := add_comm₂ m n,
  by simp [add, add_succ, ih]

lemma add_assoc :
  ∀l m n : ℕ, add (add l m) n = add l (add m n)
| l m 0            := by refl
| l m (nat.succ n) := by simp [add, add_assoc l m n]

-- type classes (useful for `ac_refl` below)
instance : is_commutative ℕ add := ⟨add_comm⟩
instance : is_associative ℕ add := ⟨add_assoc⟩

lemma mul_add (l m : ℕ) :
  ∀n : ℕ, mul l (add m n) = add (mul l m) (mul l n)
| 0            := by refl
| (nat.succ l) := by simp [add, mul, mul_add l]; ac_refl


/- The Curry–Howard Correspondence -/

lemma and_swap₃ (a b : Prop) :
  a ∧ b → b ∧ a :=
λhab : a ∧ b, and.intro (and.elim_right hab) (and.elim_left hab)

lemma and_swap₄ (a b : Prop) :
  a ∧ b → b ∧ a :=
begin
  intro hab,
  apply and.intro,
  apply and.elim_right,
  exact hab,
  apply and.elim_left,
  exact hab
end

#print and_swap₃
#print and_swap₄


/- Forward Tactics -/

lemma prop_comp₂ (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c :=
begin
  intro ha,
  have hb : b := hab ha,
  have hc : c := hbc hb,
  exact hc
end

end LoVe
