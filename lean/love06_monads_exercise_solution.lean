/- LoVe Exercise 6: Monads -/

import .love06_monads_demo

namespace LoVe


/- Question 1: A State Monad with Failure -/

open LoVe.lawful_monad

/- We introduce a richer notion of lawful monad that provides an `orelse`
operator `<|>` satisfying some laws, given below. `emp` denotes failure.
`x <|> y` tries `x` first, falling back on `y` on failure. -/

class lawful_monad_with_orelse (m : Type → Type)
  extends lawful_monad m, has_orelse m :=
(emp {} {α} : m α)
(emp_orelse {α} (a : m α) :
  (emp <|> a) = a)
(orelse_emp {α} (a : m α) :
  (a <|> emp) = a)
(orelse_assoc {α} (a b c : m α) :
  ((a <|> b) <|> c) = (a <|> (b <|> c)))
(emp_bind {α β} (f : α → m β) :
  (emp >>= f) = emp)
(bind_emp {α β} (f : m α) :
  (f >>= (λa, emp : α → m β)) = emp)

open LoVe.lawful_monad_with_orelse

/- We register the laws as simplification rules: -/

attribute [simp]
  LoVe.lawful_monad_with_orelse.emp_orelse
  LoVe.lawful_monad_with_orelse.orelse_emp
  LoVe.lawful_monad_with_orelse.orelse_assoc
  LoVe.lawful_monad_with_orelse.emp_bind
  LoVe.lawful_monad_with_orelse.bind_emp

/- 1.1. We set up the `option` type constructor to be a
`lawful_monad_with_orelse`. Complete the proofs. -/

namespace option

/- The following line declares some variables as default arguments to
definitions that refer to them. -/

variables {α β γ : Type}

def orelse {α} : option α → option α → option α
| none     b := b
| (some a) _ := some a

instance lawful_monad_with_orelse_option : lawful_monad_with_orelse option :=
{ emp          := λα, none,
  orelse       := @option.orelse,
  emp_orelse   :=
    begin
      intros α a,
      refl
    end,
  orelse_emp   :=
    begin
      intros α a,
      cases a,
      { refl },
      { refl }
    end,
  orelse_assoc :=
    begin
      intros α a b c,
      cases a,
      { refl },
      { refl }
    end,
  emp_bind     :=
    begin
      intros α β f,
      refl
    end,
  bind_emp     :=
    begin
      intros α β g,
      cases g,
      { refl },
      { refl }
    end,
  .. LoVe.option.lawful_monad_option }

@[simp] lemma some_bind (a : α) (g : α → option β) :
  (some a >>= g) = g a :=
by refl

end option

/- Let us enable some convenient pattern matching syntax, by instantiating
Lean's `monad_fail` type class. (Do not worry if you do not understand what
we are referring to.) -/

instance {m : Type → Type} [lawful_monad_with_orelse m] : monad_fail m :=
⟨λα msg, emp⟩

/- Now we can write definitions such as the following: -/

def first_of_three {m : Type → Type} [lawful_monad_with_orelse m]
  (c : m (list ℕ)) : m ℕ :=
do
  [n, _, _] ← c,  -- look ma, this list has three elements!
  pure n

#eval first_of_three (some [1])
#eval first_of_three (some [1, 2, 3])
#eval first_of_three (some [1, 2, 3, 4])

/- Using `lawful_monad_with_orelse` and the `monad_fail` syntax, we can give a
consise definition for the `sum_2_5_7` function seen in the lecture. -/

def sum_2_5_7₇ {m : Type → Type} [lawful_monad_with_orelse m]
  (c : m (list ℕ)) : m ℕ :=
do
  (_ :: n2 :: _ :: _ :: n5 :: _ :: n7 :: _) ← c,
  pure (n2 + n5 + n7)

/- 1.2. Now we are ready to define `fstate σ`: a monad with an internal state of
type `σ` that can fail (unlike `state σ`).

We start with defining `fstate σ α`, where `σ` is the type of the internal
state, and `α` is the type of the value stored in the monad. We use `option` to
model failure. This means we can also use the monadic behvior of `option` when
defining the monadic opertions on `fstate`.

**Hint:** Remember that `fstate σ α` is an alias for a function type, so you can
use pattern matching and `λs, …` to define values of type `fstate σ α`.

**Hint:** `fstate` is very similar to `state` in the lecture demonstration. You
can look there for inspiration. -/

def fstate (σ : Type) (α : Type) :=
σ → option (α × σ)

/- 1.3. Define the `get` and `set` function for `fstate`, where `get` returns
the state passed along the state monad and `set s` changes the state to `s`. -/

def get {σ : Type} : fstate σ σ
| s := some (s, s)

def set {σ : Type} (s : σ) : fstate σ unit
| _ := some ((), s)

namespace fstate

/- The following line declares some variables as default arguments to
definitions that refer to them. -/

variables {σ α β γ : Type}

/- 1.4. Define the monadic operator `pure` for `fstate`, in such a way that it
will satisfy the monadic laws. -/

protected def bind (f : fstate σ α) (g : α → fstate σ β) : fstate σ β
| s := f s >>= function.uncurry g

#check function.uncurry

/- We set up the `>>=` syntax on `fstate`: -/

instance : has_bind (fstate σ) := ⟨@fstate.bind σ⟩

@[simp] lemma bind_apply (f : fstate σ α) (g : α → fstate σ β) (s : σ) :
  (f >>= g) s = f s >>= function.uncurry g :=
by refl

protected def pure (a : α) : fstate σ α
| s := some (a, s)

/- We set up the syntax for `pure` on `fstate`: -/

instance : has_pure (fstate σ) := ⟨@fstate.pure σ⟩

@[simp] lemma pure_apply (a : α) (s : σ) :
  (pure a : fstate σ α) s = some (a, s) :=
by refl

/- 1.3. Register `fstate` as a monad.

**Hint:** `pure` and `bind` are introduced using `protected`, so their names are
`fstate.pure` and `fstate.bind`.

**Hint**: The `funext` lemma is useful when you need to prove equality between
two functions.

**Hint**: Sometimes one invocation of `cases` is not enough. In particular,
`uncurry f p` requires that `p` is a pair of the form `(a, b)`.

**Hint**: `cases f s` only works when `f s` appears in your goal, so you may
need to unfold some constants before you can do a `cases`. -/

instance : lawful_monad (fstate σ) :=
{ pure_bind  :=
    begin
      intros α β a f,
      apply funext,
      intro s,
      refl
    end,
  bind_pure  :=
    begin
      intros α ma,
      apply funext,
      intro s,
      simp,
      cases ma s,
      { refl },
      { cases val,
        refl }
    end,
  bind_assoc :=
    begin
      intros α β γ f g ma,
      apply funext,
      intro s,
      simp,
      cases ma s,
      refl,
      cases val,
      refl
    end,
  .. fstate.has_bind, .. fstate.has_pure }

end fstate


/-  Question 2: Kleisli Operator

The kleisly operator `>=>` (not to be confused with `>>=`) is useful for
pipelining monadic operations. -/

open monad

/- The following two lines declare some variables as default arguments to
definitions that refer to them. -/

variables {m : Type → Type} [lawful_monad m] {α β γ δ : Type}
variables {f : α → m β} {g : β → m γ} {h : γ → m δ}

def kleisli (f : α → m β) (g : β → m γ) : (α → m γ) :=
λa, f a >>= g

infixr ` >=> `:90 := kleisli

/- 2.1. Prove that `pure` is a left and right unit for the Kleisli operator. -/

lemma pure_kleisli :
  pure >=> f = f :=
begin
  apply funext,
  intro a,
  exact pure_bind a f
end

lemma kleisli_pure :
  f >=> pure = f :=
begin
  apply funext,
  intro a,
  exact bind_pure (f a)
end

/- 2.2. Prove associativity of the Kleisli operator. -/

lemma kleisli_assoc :
  (f >=> g) >=> h = f >=> (g >=> h) :=
begin
  apply funext,
  intro a,
  apply bind_assoc g h (f a)
end

end LoVe
