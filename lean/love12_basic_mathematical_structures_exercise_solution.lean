/- LoVe Exercise 12: Basic Mathematical Structures -/

import .lovelib
import .love12_basic_mathematical_structures_demo

namespace LoVe

set_option pp.beta true


/- Question 1: Type Classes -/

namespace btree

/- Recall the datatype `btree` we introduced earlier: -/

#check btree

/- The following function takes two trees and attaches copies of the second
tree to each leaf of the first tree. -/

def append {α : Type} : btree α -> btree α -> btree α
| empty          y := y
| (node a x₁ x₂) y := node a (append x₁ y) (append x₂ y)

#reduce append (node 1 empty empty) (node 2 empty empty)

/- 1.1. Prove the following two lemmas by induction on `x`. -/

lemma append_assoc {α : Type} (x y z : btree α) :
  append (append x y) z = append x (append y z) :=
begin
  induction x,
  case btree.empty {
    refl },
  case btree.node : a x₁ x₂ ih₁ ih₂ {
    simp [append, ih₁, ih₂] }
end

lemma append_empty {α : Type} (x : btree α) :
  append x empty = x :=
begin
  induction x,
  case btree.empty {
    refl },
  case btree.node : a x₁ x₂ ih₁ ih₂ {
    simp [append, ih₁, ih₂] }
end

/- 1.2. Declare btree an instance of `add_monoid` using `append` as addition
operator. -/

#print add_monoid

instance {α : Type} : add_monoid (btree α) :=
{ add       := append,
  add_assoc := append_assoc,
  zero      := empty,
  add_zero  := append_empty,
  zero_add  := begin intro x, refl end }

/- 1.3. Explain why `btree` with `append` as addition cannot be declared an
instance of `add_group`. -/

#print add_group

/- If `t₁` is a non-empty tree, `append t₁ t₂` will always yield a nonempty
tree. Therefore, there is no inverse of a non-empty tree. No matter what we
choose `neg`  to be, we will not able to prove `add_left_neg`. -/

/- 1.4. (**optional**) Prove the following lemma illustrating why this does not
constitute an `add_group`. -/

lemma example_no_inverse :
  ∃x : btree ℕ, ∀ y : btree ℕ, append y x ≠ empty :=
begin
  use node 0 empty empty,
  intros y hy,
  cases y,
  cases hy,
  cases hy
end

end btree


/- Question 2: Multisets and Finsets -/

/- Recall the following definitions from the lecture: -/

#check nodes_multiset
#check nodes_finset
#check nodes_list

/- 2.1. Prove that the multiset of nodes does not change when mirroring a tree.

Hint: Use induction on t and `ac_refl`. -/

lemma nodes_multiset_mirror (t : btree ℕ) :
  nodes_multiset (mirror t) = nodes_multiset t :=
begin
  induction t with a t₁ t₂ h₁ h₂,
  refl,
  rw nodes_multiset,
  rw mirror,
  rw [←h₁, ←h₂],
  rw nodes_multiset,
  ac_refl
end

/- 2.2. Prove that the finset of nodes does not change when mirroring a tree.

Hint: Use induction on t and `ac_refl`. -/

example (t : btree ℕ) :
  nodes_finset (mirror t) = nodes_finset t :=
begin
  induction t with a t₁ t₂ h₁ h₂,
  refl,
  rw nodes_finset,
  rw mirror,
  rw [←h₁, ←h₂],
  rw nodes_finset,
  ac_refl
end

/- 2.3. Prove that this does not hold for the list of nodes by providing an
example of a btree `t` for which `nodes_list t ≠ nodes_list (mirror t)`.

Hint: If you define a suitable counterexample, the proof below will succeed
without modifying it. -/

def counterexample : btree ℕ :=
node 0 (node 1 empty empty) (node 2 empty empty)

#reduce nodes_list counterexample
#reduce nodes_list (mirror counterexample)

example :
  ∃t : btree ℕ, nodes_list t ≠ nodes_list (mirror t) :=
begin
  use counterexample,
  exact dec_trivial
end

end LoVe
