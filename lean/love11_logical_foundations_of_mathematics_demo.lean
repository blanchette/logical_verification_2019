/- LoVe Demo 11: Logical Foundations of Mathematics -/

import .love05_inductive_predicates_demo_master

namespace LoVe

set_option pp.beta true


/- Type Universes -/

#check @and.intro
#check ∀a b : Prop, a → b → a ∧ b
#check Prop
#check ℕ
#check Type
#check Type 1
#check Type 2
-- ...

universe variables u v

#check Type u

#check Sort 0
#check Sort 1
#check Sort 2
#check Sort u

#check Type*


/- Impredicativity -/

section impredicativity

variables (α : Type u) (β : Type v)

#check α → β

#check Πa : Type, a → a
#check ∀a : Prop, a → a

end impredicativity


/- Proof Irrelevance -/

#check proof_irrel

lemma proof_irrel {a : Prop} (h₁ h₂ : a) :
  h₁ = h₂ :=
by refl


/- Large Elimination -/

inductive square_roots (sq : ℤ) : Type u
| intro (z : ℤ) (h : sq = z * z) : square_roots
-- `square_roots sq` contains all square roots of a number `sq`. 
-- * It is empty if `sq` is not square.
-- * It has one element if `sq = 0`.
-- * It has two elements if `sq > 0` is square.

def two_as_root : square_roots 4 :=
square_roots.intro 2 (by refl)

def neg_two_as_root : square_roots 4 :=
square_roots.intro (-2) (by refl)

def large_elim {sq : ℤ} {α : Sort v} :
  square_roots sq → (Π(z : ℤ) (h : sq = z * z), α) → α
| (square_roots.intro z h) f := f z h

#eval large_elim two_as_root (λz _, z)       -- result: 2
#eval large_elim neg_two_as_root (λz _, z)   -- result: -2

example :
  two_as_root ≠ neg_two_as_root :=
begin
  have hne : large_elim two_as_root (λz _, z) 
      ≠ large_elim neg_two_as_root (λz _, z) :=
    by intro h; cases h,
  intro hr,
  apply hne,
  rw hr
end
-- Above, we could also have used `cases hr`.

example (sq : ℤ) (r : square_roots sq) :
  sq ≥ 0 :=
begin
  apply large_elim r,
  intros z hz,
  rw hz,
  apply mul_self_nonneg
end
-- Above, we could also have used `cases r`.


/- Small Elimination -/

inductive square_number (sq : ℤ) : Prop
| intro (z : ℤ) (h : sq = z * z) : square_number
-- only difference: `Prop` instead of `Type u`

lemma four_is_square :
  square_number 4 :=
square_number.intro 2 (by refl)

lemma four_is_square' :
  square_number 4 :=
square_number.intro (-2) (by refl)

example :
  four_is_square = four_is_square' :=
by apply proof_irrel
-- The "no confusion" principle does not hold for inductive predicates, 
-- only for inductive types.

-- If we could define a large eliminator, this would lead to a contradiction.
def large_elim' {sq : ℤ} {α : Sort v} :
  square_number sq → (∀(z : ℤ) (h : sq = z * z), α) → α
| (square_number.intro z h) f := f z h
-- induction tactic failed, recursor
-- 'LoVe.square_number.dcases_on' can only eliminate into Prop

-- We cannot extract the information that `four_is_square` was
-- constructed using `2` and `four_is_square'` was constructed
-- using `-2`.

def small_elim {sq : ℤ} {α : Prop} :
  square_number sq → (∀(z : ℤ) (h : sq = z * z), α) → α
| (square_number.intro z h) f := f z h

-- It is called a small eliminator because it eliminates only 
-- into `Prop`, whereas a large eliminator can eliminate into 
-- an arbitrary large type universe `Sort v`.

example (sq : ℤ) (h : square_number sq) :
  sq ≥ 0 :=
begin
  apply small_elim h,
  intros z hz,
  rw hz,
  apply mul_self_nonneg
end


/- Axiom of Choice -/

#print nonempty

/-
inductive nonempty (α : Sort u) : Prop
| intro (val : α) : nonempty
-/

lemma nat.nonempty :
  nonempty ℕ :=
nonempty.intro 0

#print classical.choice

-- classical.choice is noncomputable:
#eval classical.choice nat.nonempty
#reduce classical.choice nat.nonempty

-- definitions using it need to be marked as noncomputable:
def some_natural_number :=
classical.choice nat.nonempty

noncomputable def some_natural_number' :=
classical.choice nat.nonempty

-- Law of excluded middle:

#check classical.em -- excluded middle
#check classical.by_contradiction

local attribute [instance, priority 0] classical.prop_decidable
-- This enables the tactic `by_cases` to be used on any proposition.

example (a : Prop) :
  a ∨ ¬ a :=
begin
  by_cases h : a,
  { exact or.intro_left (¬ a) h },
  { exact or.intro_right a h }
end
-- `by_cases` makes a case distinction on the truth of a proposition,
-- whereas `cases` makes a case distinction on an inductive predicate/datatype.

-- Hilbert choice: classical.some

variables (p : ℕ → Prop) (h : ∃n : ℕ, p n)

#check classical.some h
#check classical.some_spec h
-- In contrast to `cases` this can also be used in definitions.

-- Set-theoretic axiom of choice:

#check @classical.axiom_of_choice

example (x : list ℕ)
    (h : ∀y : list ℕ, ∃z : list ℕ, [0] ++ z = x ++ y) :
  x.head = 0 :=
begin
  choose z h using h,
  have hx : x = [0] ++ z [] :=
    by simp [h []],
  simp [hx]
end


/- Subtype Example: Full Binary Trees -/

#check btree
#check is_full
#check mirror
#check is_full_mirror
#check mirror_mirror

def full_btree (α : Type) : Type :=
{t : btree α // is_full t}

/- This is syntactic sugar for:
def full_btree (α : Type) :=
@subtype (btree α) is_full
-/

#check subtype

-- To define elements of this subtype,
-- we need to provide a btree and a proof that it is full:
def some_full_btree : full_btree ℕ :=
subtype.mk empty is_full.empty

#check subtype.mk

def another_full_btree : full_btree ℕ :=
subtype.mk (node 6 empty empty)
  begin 
    apply is_full.node, 
    apply is_full.empty, 
    apply is_full.empty, 
    refl 
  end

#reduce subtype.val another_full_btree
  -- returns: node 6 empty empty

#check subtype.property another_full_btree
  -- returns: is_full (subtype.val another_full_btree)

def full_btree.mirror {α : Type} (t : full_btree α) :
  full_btree α :=
subtype.mk 
  (mirror (subtype.val t)) 
  begin
    apply is_full_mirror,
    apply subtype.property t
  end

#reduce subtype.val (full_btree.mirror another_full_btree)

lemma full_btree.mirror_mirror {α : Type} (t : full_btree α) :
  (full_btree.mirror (full_btree.mirror t)) = t :=
begin
  apply subtype.eq,
  simp [full_btree.mirror],
  apply mirror_mirror
end

#check subtype.eq

/- Subtype Example: Vectors -/

#check vector
def vector (α : Type u) (n : ℕ) : Type u :=
{l : list α // l.length = n}

def some_vector : vector ℤ 3 :=
subtype.mk ([1, 2, 3]) (by refl)

def vector.neg {n : ℕ} (v : vector ℤ n) : vector ℤ n :=
subtype.mk (list.map int.neg (subtype.val v))
  begin rw list.length_map, exact subtype.property v end

lemma int.neg_comp_neg :
  int.neg ∘ int.neg = id :=
begin
  apply funext,
  apply neg_neg
end

lemma vector.neg_neg (n : ℕ) (v : vector ℤ n) :
  vector.neg (vector.neg v) = v :=
begin
  apply subtype.eq,
  simp [vector.neg],
  rw [int.neg_comp_neg, list.map_id]
end


/- Quotient Types -/

-- `quotient` for equivalence relations
#check quotient
#print setoid

def base : Type :=
sorry

def e : base → base → Prop :=
sorry

instance base.setoid : setoid base := 
{ r := e,
  iseqv := sorry }

def my_quotient : Type :=
quotient base.setoid

variables (a : base) 

#check quotient.mk a
#check ⟦a⟧
#check @quotient.sound base base.setoid
#check @quotient.exact base base.setoid

variables (q q' : my_quotient) (β : Type) (f : base → β) (g : base → base → β)

#check quotient.lift f
#check quotient.lift₂ g
#check quotient.induction_on
#check quotient.induction_on₂
#check quotient.induction_on₃

/- Integers as a Quotient -/

/- Basic idea: `(p, n)` represents `p - n` -/

instance myℤ.rel : setoid (ℕ × ℕ) :=
{ r     := λa b, a.1 + b.2 = b.1 + a.2,
  iseqv :=
  begin
    apply and.intro,
    { intro a,
      refl },
    apply and.intro,
    { intros a b h,
      rw h },
    { intros a b c eq_ab eq_bc, 
      apply eq_of_add_eq_add_right,
      calc  (a.1 + c.2) + b.2
		      = (a.1 + b.2) + c.2 :
        by ac_refl
      ... = a.2 + (b.1 + c.2) :
        by rw [eq_ab]; ac_refl
      ... = (c.1 + a.2) + b.2 :
        by rw [eq_bc]; ac_refl }
  end }

#print equivalence

def myℤ : Type :=
quotient myℤ.rel

lemma rel_iff (a b : ℕ × ℕ) :
  a ≈ b ↔ a.1 + b.2 = b.1 + a.2 :=
by refl

def zero : myℤ := ⟦(0, 0)⟧

example (n : ℕ) : zero = ⟦(n, n)⟧ :=
begin
  rw zero,
  apply quotient.sound,
  rw [rel_iff],
  simp
end

#check quotient.lift₂ 

def add : myℤ → myℤ → myℤ :=
quotient.lift₂ 
  (λa b : ℕ × ℕ, ⟦(a.1 + b.1, a.2 + b.2)⟧)
  begin
    intros a₁ b₁ a₂ b₂ ha hb,
    apply quotient.sound,
    rw [rel_iff] at ha hb ⊢,
    calc  (a₁.1 + b₁.1) + (a₂.2 + b₂.2)
        = (a₁.1 + a₂.2) + (b₁.1 + b₂.2) :
	  by ac_refl
    ... = (a₂.1 + a₁.2) + (b₂.1 + b₁.2) :
      by rw [ha, hb]
    ... = (a₂.1 + b₂.1) + (a₁.2 + b₁.2) :
	  by ac_refl
  end

lemma add_mk (ap an bp bn : ℕ) :
  add ⟦(ap, an)⟧ ⟦(bp, bn)⟧ = ⟦(ap + bp, an + bn)⟧ :=
by refl

lemma add_zero (i : myℤ) :
  add zero i = i :=
begin
  apply quotient.induction_on i,
  intro p,
  rw zero,
  cases p,
  rw add_mk,
  apply quotient.sound,
  simp
end

end LoVe
