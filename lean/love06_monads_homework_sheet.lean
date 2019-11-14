/- LoVe Homework 6: Monads -/

import .lovelib

namespace LoVe


/- Question 1: `map` for Monads

Define `map` for monads. This is the generalization of `map` on lists. Use the
monad operations to define `map`. The functorial properties (`map_id` and
`map_map`) are derived from the monad laws.

This time, we use Lean's monad definition. In combination, `monad` and
`is_lawful_monad` include the same constants, laws, and syntactic sugar as the
`lawful_monad` type class from the lecture. -/

section map

/- We fix a lawful monad `m`: -/

variables {m : Type → Type} [monad m] [is_lawful_monad m]

/- 1.1. Define `map` on `m`.

**Hint:** The challenge is to find a way to create `m β`. Follow the types.
One way to proceed is to list all the arguments and operations
available (e.g., `pure`, `>>=`) with their types and see if you can plug
them together like Lego blocks. -/

def map {α β} (f : α → β) (ma : m α) : m β :=
:= sorry

/- 1.2. Prove the identity law for `map`.

**Hint**: You will need the `bind_pure` property of monads. -/

lemma map_id {α} (ma : m α) : map id ma = ma :=
sorry

/- 1.3. Prove the composition law for `map`. -/

lemma map_map {α β γ} (f : α → β) (g : β → γ) (ma : m α) :
  map g (map f ma) = map (g ∘ f) ma :=
sorry

end map


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
sorry

@[simp] lemma bind_cons {α β : Type} (f : α → list β) (a : α) (as : list α) :
  list.cons a as >>= f = f a ++ (as >>= f) :=
sorry

@[simp] lemma bind_append {α β : Type} (f : α → list β) :
  ∀as as' : list α, (as ++ as') >>= f = (as >>= f) ++ (as' >>= f)
:= sorry

/- 2.2. Prove the monadic laws for `list`.

**Hint:** The simplifier cannot see through the type class definition of `pure`. You can use
`pure_eq_singleton` to unfold the definition or `show` to state the lemma statement using `bind` and
`[...]`. -/

lemma pure_bind {α β : Type} (a : α) (f : α → list β) :
  (pure a >>= f) = f a :=
sorry

lemma bind_pure {α : Type} :
  ∀as : list α, as >>= pure = as
:= sorry

lemma bind_assoc {α β γ : Type} (f : α → list β) (g : β → list γ) :
  ∀as : list α, (as >>= f) >>= g = as >>= (λa, f a >>= g)
:= sorry

lemma bind_pure_comp_eq_map {α β : Type} {f : α → β} :
  ∀as : list α, as >>= (pure ∘ f) = list.map f as
:= sorry

end list

end LoVe
