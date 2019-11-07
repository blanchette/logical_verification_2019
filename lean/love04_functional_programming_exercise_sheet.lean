/- LoVe Exercise 4: Functional Programming -/

import .love04_functional_programming_demo

namespace LoVe


/- Question 1: Reverse of a List -/

/- We define a new accumulator-based version of `reverse`. The first argument
serves as the accumulator. This definition is _tail-recursive_, meaning that
compilers and interpreters can easily optimize the recursion away, resulting in
more efficient code. -/

def areverse {α : Type} : list α → list α → list α
| ys []        := ys
| ys (x :: xs) := areverse (x :: ys) xs

/- 1.1. Our intention is that `areverse [] xs` should be equal to `reverse xs`.
But if we start an induction, we quickly see that the induction hypothesis is
not strong enough. Start by proving the following generalization (using pattern
matching or the `induction` tactic): -/

lemma areverse_eq_reverse_append {α : Type} :
  ∀ys xs : list α, areverse ys xs = reverse xs ++ ys
:= sorry

/- 1.2. Derive the desired equation. -/

lemma areverse_eq_reverse {α : Type} (xs : list α) :
  areverse [] xs = reverse xs :=
sorry

/- 1.3. Prove the following property. Hint: A one-line inductionless proof is
 possible. -/

lemma areverse_areverse {α : Type} (xs : list α) :
  areverse [] (areverse [] xs) = xs :=
sorry


/- Question 2: Drop and Take -/

/- The `drop` function removes the first `n` elements from the front of a
list. -/

def drop {α : Type} : ℕ → list α → list α
| 0       xs        := xs
| (_ + 1) []        := []
| (m + 1) (x :: xs) := drop m xs

/- Its relative `take` returns a list consisting of the the first `n` elements
at the front of a list. -/

/- 2.1. Define `take`. -/

/- To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α : Type} : ℕ → list α → list α
:= sorry

#reduce take 0 [3, 7, 11]  -- expected: []
#reduce take 1 [3, 7, 11]  -- expected: [3]
#reduce take 2 [3, 7, 11]  -- expected: [3, 7]
#reduce take 3 [3, 7, 11]  -- expected: [3, 7, 11]
#reduce take 4 [3, 7, 11]  -- expected: [3, 7, 11]

-- when `#reduce` fails for some obscure reason, try `#eval`:
#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 2.2. Prove the following lemmas. Notice that they are registered as
simplification rules thanks to the `@[simp]` attribute. -/

@[simp] lemma drop_nil {α : Type} :
  ∀n : ℕ, drop n ([] : list α) = []
:= sorry

@[simp] lemma take_nil {α : Type} :
  ∀n : ℕ, take n ([] : list α) = []
:= sorry

/- 2.3. Follow the recursion pattern of `drop` and `take` to prove the following
lemmas. In other words, for each lemma, there should be three cases, and the
third case will need to invoke the induction hypothesis.

The first case is shown for `drop_drop`. Beware of the fact that there are three
variables in the `drop_drop` lemma (but only two arguments to `drop`).

Hint: The `refl` tactic might be useful in the third case of `drop_drop`. -/

lemma drop_drop {α : Type} :
  ∀(m n : ℕ) (xs : list α), drop n (drop m xs) = drop (n + m) xs
| 0       n xs        := by refl
-- supply the two missing cases here

lemma take_take {α : Type} :
  ∀(m : ℕ) (xs : list α), take m (take m xs) = take m xs
:= sorry

lemma take_drop {α : Type} :
  ∀(n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
:= sorry


/- Question 3: λ-Terms -/

/- 3.1. Define an inductive type corresponding to the untyled λ-terms, as given
by the following context-free grammar:

<lam> ::= 'var' <string>
        | 'abs' <string> <lam>
        | 'app' <lam> <lam> -/

-- enter your definition here

/- 3.2. Register a textual representation of the type `lam`. Make sure to supply
enough parentheses to guarantee that the output is unambiguous. -/

def lam.repr : lam → string
-- enter your answer here

instance : has_repr lam :=
⟨lam.repr⟩


/- Question 4 (**optional**): Concatenation -/

/- Consider the following Lean definition of 2–3 trees as an inductive type: -/

inductive tttree (α : Type) : Type
| empty {} : tttree
| bin      : α → tttree → tttree → tttree
| ter      : α → tttree → tttree → tttree → tttree

export tttree (empty bin ter)

/- 4.1 (**optional**). Complete the following Lean definition. The `map_tree`
function should apply its argument `f` to all values of type α stored in the
tree and otherwise preserve the tree's structure. -/

-- enter your definition here

/- 4.2 (**optional**). Prove the following lemma about your definition of
`map_tree`. -/

lemma map_tttree_id {α : Type} :
  ∀t : tttree α, map_tttree (λx : α, x) t = t
:= sorry

/- 4.3 (**optional**). Complete the following Lean definition. The `set_tree`
function should return the set of all values of type α stored in the tree. In
your answer, you may use traditional set notations regardless of whether they
are actually supported by Lean. -/

def set_tttree {α : Type} : tttree α → set α
:= sorry

/- A _congruence rule_ is a lemma that can be used to lift an equivalence
relation between terms to the same terms occurring under a common context.
Congruence rules for equality are built into Lean's logic. In the following
example, the equivalence relation is `=`, the terms are `f` and `g`, and the
context is `map_tree … t`: -/

lemma map_tttree_congr_weak {α β : Type} (f g : α → β) (f = g) (t : tttree α) :
  map_tttree f t = map_tttree g t :=
by simp *

/- 4.4 (**optional**). The above rule is not as flexible as it could be,
because it requires `f = g`. As long as `f` and `g` are equal for all values
`x : α` stored in `t`, we have `map_tree f t = map_tree g t`, even if `f` and
`g` disagree on other `α` values. Inspired by this observation, prove the
following stronger congruence rule. -/

lemma map_tttree_congr_strong {α β : Type} (f g : α → β) :
  ∀t : tttree α, (∀x, x ∈ set_tttree t → f x = g x) →
  map_tttree f t = map_tttree g t
:= sorry

end LoVe
