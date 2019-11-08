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
| ys []        := by refl
| ys (x :: xs) := by simp [reverse, areverse, areverse_eq_reverse_append _ xs]

/- 1.2. Derive the desired equation. -/

lemma areverse_eq_reverse {α : Type} (xs : list α) :
  areverse [] xs = reverse xs :=
by simp [areverse_eq_reverse_append]

/- 1.3. Prove the following property. Hint: A one-line inductionless proof is
 possible. -/

lemma areverse_areverse {α : Type} (xs : list α) :
  areverse [] (areverse [] xs) = xs :=
by simp [areverse_eq_reverse, reverse_reverse]


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
| 0       _         := []
| (_ + 1) []        := []
| (m + 1) (x :: xs) := x :: take m xs

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
| 0       := by refl
| (_ + 1) := by refl

@[simp] lemma take_nil {α : Type} :
  ∀n : ℕ, take n ([] : list α) = []
| 0       := by refl
| (_ + 1) := by refl

/- 2.3. Follow the recursion pattern of `drop` and `take` to prove the following
lemmas. In other words, for each lemma, there should be three cases, and the
third case will need to invoke the induction hypothesis.

The first case is shown for `drop_drop`. Beware of the fact that there are three
variables in the `drop_drop` lemma (but only two arguments to `drop`).

Hint: The `refl` tactic might be useful in the third case of `drop_drop`. -/

lemma drop_drop {α : Type} :
  ∀(m n : ℕ) (xs : list α), drop n (drop m xs) = drop (n + m) xs
| 0       n xs        := by refl
| (_ + 1) _ []        := by simp [drop]
| (m + 1) n (x :: xs) :=
  begin
    simp [drop, drop_drop m n xs],
    refl
  end

lemma take_take {α : Type} :
  ∀(m : ℕ) (xs : list α), take m (take m xs) = take m xs
| 0       _         := by refl
| (_ + 1) []        := by refl
| (m + 1) (x :: xs) := by simp [take, take_take m xs]

lemma take_drop {α : Type} :
  ∀(n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
| 0       _         := by refl
| (_ + 1) []        := by refl
| (m + 1) (x :: xs) := by simp [take, drop, take_drop m]


/- Question 3: λ-Terms -/

/- 3.1. Define an inductive type corresponding to the untyled λ-terms, as given
by the following context-free grammar:

<lam> ::= 'var' <string>
        | 'abs' <string> <lam>
        | 'app' <lam> <lam> -/

inductive lam : Type
| var : string → lam
| abs : string → lam → lam
| app : lam → lam → lam

export lam (var abs app)

/- 3.2. Register a textual representation of the type `lam`. Make sure to supply
enough parentheses to guarantee that the output is unambiguous. -/

def lam.repr : lam → string
| (var s)   := s
| (abs s t) := "(λ" ++ s ++ ", " ++ lam.repr t ++ ")"
| (app t u) := "(" ++ lam.repr t ++ " " ++ lam.repr u ++ ")"

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

def map_tttree {α β : Type} (f : α → β) : tttree α → tttree β
| empty         := empty
| (bin a l r)   := bin (f a) (map_tttree l) (map_tttree r)
| (ter a l m r) := ter (f a) (map_tttree l) (map_tttree m) (map_tttree r)

/- 4.2 (**optional**). Prove the following lemma about your definition of
`map_tree`. -/

lemma map_tttree_id {α : Type} :
  ∀t : tttree α, map_tttree (λx : α, x) t = t
| empty         := by refl
| (bin a l r)   := by simp [map_tttree, map_tttree_id l, map_tttree_id r]
| (ter a l m r) :=
  by simp [map_tttree, map_tttree_id l, map_tttree_id m, map_tttree_id r]

/- 4.3 (**optional**). Complete the following Lean definition. The `set_tree`
function should return the set of all values of type α stored in the tree. In
your answer, you may use traditional set notations regardless of whether they
are actually supported by Lean. -/

def set_tttree {α : Type} : tttree α → set α
| empty         := ∅
| (bin a l r)   := insert a (set_tttree l ∪ set_tttree r)
| (ter a l m r) := insert a (set_tttree l ∪ set_tttree m ∪ set_tttree r)

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
| empty         := by intros; refl
| (bin a l r)   :=
  begin
    intros,
    simp [map_tttree],
    apply and.intro,
    { apply a_1,
      simp [set_tttree] },
    apply and.intro,
    { apply map_tttree_congr_strong,
      intros,
      apply a_1,
      simp [set_tttree],
      cc },
    { apply map_tttree_congr_strong,
      intros,
      apply a_1,
      simp [set_tttree],
      cc },
  end
| (ter a l m r)   :=
  begin
    intros,
    simp [map_tttree],
    apply and.intro,
    { apply a_1,
      simp [set_tttree] },
    apply and.intro,
    { apply map_tttree_congr_strong,
      intros,
      apply a_1,
      simp [set_tttree],
      cc },
    apply and.intro,
    { apply map_tttree_congr_strong,
      intros,
      apply a_1,
      simp [set_tttree],
      cc },
    { apply map_tttree_congr_strong,
      intros,
      apply a_1,
      simp [set_tttree],
      cc }
  end

end LoVe
