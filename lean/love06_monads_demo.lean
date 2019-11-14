/- LoVe Demo 6: Monads -/

import .lovelib

namespace LoVe


/- Motivating Example -/

def sum_2_5_7₁ (ns : list ℕ) : option ℕ :=
match list.nth ns 1 with
| none    := none
| some n2 :=
  match list.nth ns 4 with
  | none    := none
  | some n5 :=
    match list.nth ns 6 with
    | none    := none
    | some n7 := some (n2 + n5 + n7)
    end
  end
end

def bind_option {α : Type} {β : Type} :
  option α → (α → option β) → option β
| none     f := none
| (some a) f := f a

def sum_2_5_7₂ (ns : list ℕ) : option ℕ :=
bind_option (list.nth ns 1)
  (λn2, bind_option (list.nth ns 4)
    (λn5, bind_option (list.nth ns 6)
      (λn7, some (n2 + n5 + n7))))

#check bind

def sum_2_5_7₃ (ns : list ℕ) : option ℕ :=
bind (list.nth ns 1)
  (λn2, bind (list.nth ns 4)
    (λn5, bind (list.nth ns 6)
      (λn7, some (n2 + n5 + n7))))

#check (>>=)

def sum_2_5_7₄ (ns : list ℕ) : option ℕ :=
list.nth ns 1 >>=
  λn2, list.nth ns 4 >>=
    λn5, list.nth ns 6 >>=
      λn7, some (n2 + n5 + n7)

def sum_2_5_7₅ (ns : list ℕ) : option ℕ :=
  do n2 ← list.nth ns 1,
    do n5 ← list.nth ns 4,
      do n7 ← list.nth ns 6,
        some (n2 + n5 + n7)

def sum_2_5_7₆ (ns : list ℕ) : option ℕ :=
do
  n2 ← list.nth ns 1,
  n5 ← list.nth ns 4,
  n7 ← list.nth ns 6,
  some (n2 + n5 + n7)


/- A Type Class of Monads -/

class lawful_monad (m : Type → Type)
  extends has_bind m, has_pure m : Type 1 :=
(pure_bind {α β : Type} (a : α) (f : α → m β) :
  (pure a >>= f) = f a)
(bind_pure {α : Type} (ma : m α) :
  ma >>= pure = ma)
(bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
    (ma : m α) :
  ((ma >>= f) >>= g) = (ma >>= (λa, f a >>= g)))

attribute [simp]
  LoVe.lawful_monad.bind_pure
  LoVe.lawful_monad.bind_assoc
  LoVe.lawful_monad.pure_bind

open LoVe.lawful_monad

#print monad
#print is_lawful_monad


/- The Option Monad -/

namespace option

def pure {α : Type} : α → option α :=
option.some

def bind {α β : Type} : option α → (α → option β) → option β
| none     f := none
| (some a) f := f a

instance lawful_monad_option : lawful_monad option :=
{ pure       := @option.pure,
  bind       := @option.bind,
  pure_bind  :=
    begin
      intros α β a f,
      refl
    end,
  bind_pure  :=
    begin
      intros α m,
      cases m; refl
    end,
  bind_assoc :=
    begin
      intros α β γ f g m,
      cases m; refl
    end }

end option


/- The State Monad -/

namespace state

def state (σ : Type) (α : Type) :=
σ → α × σ

end state

namespace state

def read {σ : Type} : state σ σ
| s := (s, s)

def write {σ : Type} (s : σ) : state σ unit
| _ := ((), s)

def pure {σ α : Type} (a : α) : state σ α
| s := (a, s)

def bind {σ : Type} {α β : Type} (ma : state σ α)
  (f : α → state σ β) : state σ β
| s :=
  match ma s with
  | (a, s') := f a s'
  end

instance {σ : Type} : lawful_monad (state σ) :=
{ pure       := @state.pure σ,
  bind       := @state.bind σ,
  pure_bind  :=
    begin
      intros α β a f,
      apply funext,
      intro s,
      refl
    end,
  bind_pure  :=
    begin
      intros α m,
      apply funext,
      intro s,
      simp [bind],
      cases m s,
      refl
    end,
  bind_assoc :=
    begin
      intros α β γ f g m,
      apply funext,
      intro s,
      simp [bind],
      cases m s,
      refl
    end }

end state

namespace state

def diff_list : list ℕ → state ℕ (list ℕ)
| []        := pure []
| (n :: ns) :=
  do
    prev ← read,
    if n < prev then
      diff_list ns
    else
      do
        write n,
        ns' ← diff_list ns,
        pure (n :: ns')

#eval diff_list [1, 2, 3, 2] 0
#eval diff_list [1, 2, 3, 2, 4, 5, 2] 0

end state


/- Example: Generic Iteration over a List -/

def mmap {m : Type → Type} [lawful_monad m] {α β : Type}
    (f : α → m β) : list α → m (list β)
| []       := pure []
| (a :: as) :=
  do
    b ← f a,
    bs ← mmap as,
    pure (b :: bs)

lemma mmap_append {m : Type → Type} [lawful_monad m]
    {α β : Type} (f : α → m β) :
  ∀as as' : list α, mmap f (as ++ as') =
    do
      bs ← mmap f as,
      bs' ← mmap f as',
      pure (bs ++ bs')
| []        _   := by simp [mmap]
| (a :: as) as' := by simp [mmap, mmap_append as as']

def nths {α : Type} (xss : list (list α)) (n : ℕ) :
  option (list α) :=
mmap (λxs, list.nth xs n) xss

#eval nths
  [[11, 12, 13, 14],
   [21, 22, 23],
   [31, 32, 33]] 2

end LoVe
