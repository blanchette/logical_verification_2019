/- LoVe Demo 12: Basic Mathematical Structures -/

import .love05_inductive_predicates_demo

namespace LoVe


/- Type Classes -/

-- The `inhabited` typeclass for types that contain at least one element
#check inhabited

-- `nonempty` lives in `Prop`, whereas `inhabited` lives in `Type`
#check nonempty

-- Recall: `head` returns `option α`
#check head

-- Variant of `head` for inhabited types
def ihead {α : Type} [inhabited α] (xs : list α) : α :=
match xs with
| []     := inhabited.default α
| x :: _ := x
end

lemma ihead_ihead {α : Type} [inhabited α] (xs : list α) :
  ihead [ihead xs] = ihead xs :=
begin
  cases xs,
  { refl },
  { refl }
end

-- The natural numbers can be made an instance as follows:
instance : inhabited ℕ :=
{ default := 0 }

#reduce inhabited.default ℕ
#reduce ihead ([] : list ℕ)
#check ihead_ihead ([1, 2, 3] : list ℕ)

-- Syntactic type classes
#check has_zero
#check has_neg
#check has_add
#check has_one
#check has_inv
#check has_mul

#check (1 : ℕ)
#check (1 : ℤ)
#check (1 : ℝ)
#check (1 : linear_map _ _ _)


/- Groups -/

#print group

#print add_group

inductive ℤ₂ : Type
| zero
| one

def ℤ₂.add : ℤ₂ → ℤ₂ → ℤ₂
| ℤ₂.zero x       := x
| x       ℤ₂.zero := x
| ℤ₂.one  ℤ₂.one  := ℤ₂.zero

instance ℤ₂.add_group : add_group ℤ₂ :=
{ add          := ℤ₂.add,
  add_assoc    :=
    begin
      intros a b c,
      simp [(+)],
      cases a;
        cases b;
        cases c;
        refl
    end,
  zero         := ℤ₂.zero,
  zero_add     :=
    begin
      intro a,
      cases a;
        refl
    end,
  add_zero     :=
    begin
      intro a,
      cases a;
        refl
    end,
  neg          := (λ x, x),
  add_left_neg :=
    begin
      intro a,
      cases a;
        refl
    end }

#reduce ℤ₂.one + 0 - 0 - ℤ₂.one

example :
  ∀a : ℤ₂, a + - a = 0 :=
add_right_neg

-- Another example: lists as `add_monoid`:
instance {α : Type} : add_monoid (list α) :=
{ zero      := [],
  add       := (++),
  add_assoc := list.append_assoc,
  zero_add  := list.nil_append,
  add_zero  := list.append_nil }


/- Fields -/

#print field

def ℤ₂.mul : ℤ₂ → ℤ₂ → ℤ₂
| ℤ₂.one  x       := x
| x       ℤ₂.one  := x
| ℤ₂.zero ℤ₂.zero := ℤ₂.zero

instance : field ℤ₂ :=
{ one            := ℤ₂.one,
  mul            := ℤ₂.mul,
  inv            := λx, x,
  add_comm       :=
    begin
      intros a b,
      cases a;
        cases b;
        refl
    end,
  zero_ne_one    :=
    begin
      intro h,
      cases h
    end,
  one_mul        :=
    begin
      intros a,
      cases a;
        refl
    end,
  mul_one        :=
    begin
      intros a,
      cases a;
        refl
    end,
  mul_inv_cancel :=
    begin 
      intros a h,
      cases a,
      apply false.elim,
      apply h,
      refl,
      refl 
    end,
  inv_mul_cancel :=
    begin 
      intros a h,
      cases a,
      apply false.elim,
      apply h,
      refl,
      refl
    end,
  mul_assoc      :=
    begin
      intros a b c,
      cases a;
        cases b;
        cases c;
        refl
    end,
  mul_comm       :=
    begin
      intros a b,
      cases a;
        cases b;
        refl
    end,
  left_distrib   :=
    begin
      intros a b c,
      cases a;
        cases b;
        cases c;
        refl
    end,
  right_distrib  :=
    begin
      intros a b c,
      cases a;
        cases b;
        cases c;
        refl
    end,
  ..ℤ₂.add_group }

#reduce (1 : ℤ₂) * 0 / (0 - 1)  -- result: ℤ₂.zero

#reduce (3 : ℤ₂)  -- result: ℤ₂.one

example (a b : ℤ₂) :
  (a + b) ^ 3 = a ^ 3 + 3 * a^2 * b + 3 * a * b ^ 2 + b ^ 3 :=
by ring -- normalizes terms of rings

example (a b : ℤ) :
  (a + b + 0) - ((b + a) + a) = -a :=
by abel -- normalizes terms of commutative monoids


/- Coercions -/

lemma neg_mul_neg_nat (n : ℕ) (z : ℤ) :
  (- z) * (- n) = z * n :=
neg_mul_neg z n
-- This works, althogh negation `- n` is not defined on natural numbers.

#print neg_mul_neg_nat
-- Lean introduced a coercion `↑` automatically.

lemma neg_mul_neg_nat₂ (n : ℕ) (z : ℤ) :
  (- n : ℤ) * (- z) = n * z :=
neg_mul_neg n z

#print neg_mul_neg_nat₂

example (m n : ℕ) (h : (m : ℤ) = (n : ℤ)) :
  m = n :=
begin
  norm_cast at h,
  exact h
end

example (m n : ℕ) :
  (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) :=
begin norm_cast end

-- norm_cast internally uses lemmas such as:
#check nat.cast_add
#check int.cast_add
#check rat.cast_add


/- Lists, Multisets and Finite Sets -/

-- lists: number of occurrences and order matter

example :
  [1, 2, 2, 3] ≠ [1, 2, 3] :=
dec_trivial

example :
  [3, 2, 1] ≠ [1, 2, 3] :=
dec_trivial

-- multisets: number of occurrences matters, order doesn't

example :
  ({1, 2, 2, 3} : multiset ℕ) ≠ {1, 2, 3} :=
dec_trivial

example :
  ({1, 2, 3} : multiset ℕ) = {3, 2, 1} :=
dec_trivial

-- finsets: number of occurrences and order don't matter

example :
  ({1, 2, 2, 3} : finset ℕ) = {1, 2, 3} :=
dec_trivial

example :
  ({1, 2, 3} : finset ℕ) = {3, 2, 1} :=
dec_trivial

-- `dec_trivial` can solve goals for which Lean can infer an algorithm 
-- to compute their truth value, i.e., trivially decidable goals

-- list of nodes (depth first)
def nodes_list : btree ℕ → list ℕ
| empty          := []
| (node a t₁ t₂) := a :: nodes_list t₁ ++ nodes_list t₂

-- multiset of nodes
def nodes_multiset : btree ℕ → multiset ℕ
| empty          := ∅
| (node a t₁ t₂) :=
  insert a (nodes_multiset t₁ ∪ nodes_multiset t₂)

-- finset of nodes
def nodes_finset : btree ℕ → finset ℕ
| empty          := ∅
| (node a t₁ t₂) := insert a (nodes_finset t₁ ∪ nodes_finset t₂)

#eval list.sum [1, 2, 3, 4]                          -- result: 10
#eval multiset.sum ({1, 2, 3, 4} : multiset ℕ)       -- result: 10
#eval finset.sum ({1, 2, 3, 4} : finset ℕ) (λx, x)   -- result: 10

#eval list.prod [1, 2, 3, 4]                         -- result: 24
#eval multiset.prod ({1, 2, 3, 4} : multiset ℕ)      -- result: 24
#eval finset.prod ({1, 2, 3, 4} : finset ℕ) (λx, x)  -- result: 24

end LoVe
