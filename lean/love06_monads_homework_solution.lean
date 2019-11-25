/- LoVe Homework 6: Monads -/

import .lovelib

namespace LoVe


/- Question 2 **optional**: Monadic Structure on Lists -/

/- `list` can be seen as a monad, similar to `option` but with several possible
outcomes. It is also similar to `set`, but the results are ordered and finite.
The code below sets `list` up as a monad. -/

namespace list

protected def bind {α β : Type} : list α → (α → list β) → list β
| []        f := []
| (a :: as) f := f a ++ bind as f

protected def pure {α : Type} (a : α) : list α :=
[a]

lemma pure_eq_singleton {α : Type} (a : α) :
  pure a = [a] :=
by refl

instance : monad list :=
{ pure := @list.pure,
  bind := @list.bind }

/- 2.1 **optional**. Prove the following properties of `bind` under the empty
list (`[]`), the list constructor (`::`), and `++`. -/

@[simp] lemma bind_nil {α β : Type} (f : α → list β) :
  [] >>= f = [] :=
by refl

@[simp] lemma bind_cons {α β : Type} (f : α → list β) (a : α) (as : list α) :
  list.cons a as >>= f = f a ++ (as >>= f) :=
by refl

@[simp] lemma bind_append {α β : Type} (f : α → list β) :
  ∀as as' : list α, (as ++ as') >>= f = (as >>= f) ++ (as' >>= f)
| []        as' := by refl
| (a :: as) as' := by simp [bind_append as as']

/- 2.2 **optional**. Prove the monadic laws for `list`.

Hint: The simplifier cannot see through the type class definition of `pure`. You
can use `pure_eq_singleton` to unfold the definition or `show` to state the
lemma statement using `bind` and `[…]`. -/

lemma pure_bind {α β : Type} (a : α) (f : α → list β) :
  (pure a >>= f) = f a :=
show ([a] >>= f) = f a,
  by simp

lemma bind_pure {α : Type} :
  ∀as : list α, as >>= pure = as
| []       := by refl
| (a :: l) := by simp [pure_eq_singleton, bind_pure l]

lemma bind_assoc {α β γ : Type} (f : α → list β) (g : β → list γ) :
  ∀as : list α, (as >>= f) >>= g = as >>= (λa, f a >>= g)
| []        := by refl
| (a :: as) := by simp [bind_append, bind_assoc as]

lemma bind_pure_comp_eq_map {α β : Type} {f : α → β} :
  ∀as : list α, as >>= (pure ∘ f) = list.map f as
| []        := by refl
| (a :: as) := by simp [bind_pure_comp_eq_map as, pure_eq_singleton]

end list

end LoVe
