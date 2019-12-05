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
sorry

lemma append_empty {α : Type} (x : btree α) :
  append x empty = x :=
sorry

/- 1.2. Declare btree an instance of `add_monoid` using `append` as addition
operator. -/

#print add_monoid

instance {α : Type} : add_monoid (btree α) :=
sorry

/- 1.3. Explain why `btree` with `append` as addition cannot be declared an
instance of `add_group`. -/

#print add_group

/- 1.4. (**optional**) Prove the following lemma illustrating why this does not
constitute an `add_group`. -/

lemma example_no_inverse :
  ∃x : btree ℕ, ∀ y : btree ℕ, append y x ≠ empty :=
sorry

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
sorry

/- 2.2. Prove that the finset of nodes does not change when mirroring a tree.

Hint: Use induction on t and `ac_refl`. -/

example (t : btree ℕ) :
  nodes_finset (mirror t) = nodes_finset t :=
sorry

/- 2.3. Prove that this does not hold for the list of nodes by providing an
example of a btree `t` for which `nodes_list t ≠ nodes_list (mirror t)`.

Hint: If you define a suitable counterexample, the proof below will succeed
without modifying it. -/

def counterexample : btree ℕ :=
sorry

#reduce nodes_list counterexample
#reduce nodes_list (mirror counterexample)

example :
  ∃t : btree ℕ, nodes_list t ≠ nodes_list (mirror t) :=
begin
  use counterexample,
  exact dec_trivial
end

end LoVe
