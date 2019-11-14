# LoVe Lecture 6: Monads

We take a look at an important functional programming abstraction: monads

We review the concept from the ground up and see how it is used in Lean


## Introductory Example

Consider the following programming task: Implement a function sum_2_5_7 ns that sums up the second, fifth, and seventh items of a list `ns` of natural numbers

Use `option ℕ` for the result so that if the list has fewer than seven elements, you can return `none`

A straightforward implementation follows:

    def sum_2_5_7 (ns : list ℕ) : option ℕ :=
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

The code is quite ugly, because of all the pattern matching on options

We can put all the ugliness in one function, which we call `bind_option`:

    def bind_option {α : Type} {β : Type} :
      option α → (α → option β) → option β
    | none     f := none
    | (some a) f := f a

    def sum_2_5_7 (ns : list ℕ) : option ℕ :=
    bind_option (list.nth ns 1)
      (λn2, bind_option (list.nth ns 4)
        (λn5, bind_option (list.nth ns 6)
          (λn7, some (n2 + n5 + n7))))


Instead of defining bind_option ourselves, we could use Lean's predefined general `bind` operation:

    def sum_2_5_7 (ns : list ℕ) : option ℕ :=
    bind (list.nth ns 1)
      (λn2, bind (list.nth ns 4)
        (λn5, bind (list.nth ns 6)
          (λn7, some (n2 + n5 + n7))))

Alternative with syntactic sugar:

    def sum_2_5_7 (ns : list ℕ) : option ℕ :=
    list.nth ns 1 >>=
      λn2, list.nth ns 4 >>=
        λn5, list.nth ns 6 >>=
          λn7, some (n2 + n5 + n7)

The syntax `ma >>= f` expands to `bind ma f`

More syntactic sugar:

    def sum_2_5_7 (ns : list ℕ) : option ℕ :=
      do n2 ← list.nth ns 1,
        do n5 ← list.nth ns 4,
          do n7 ← list.nth ns 6,
            some (n2 + n5 + n7)

The syntax `do a ← ma, t` expands to `ma >>= λa, t`

Even more syntactic sugar:

    def sum_2_5_7 (ns : list ℕ) : option ℕ :=
    do
      n2 ← list.nth ns 1,
      n5 ← list.nth ns 4,
      n7 ← list.nth ns 6,
      some (n2 + n5 + n7)

Although the notation has an imperative flavor, the function is a pure functional program


## Overview

The `option` type constructor is an example of a monad

In general, a monad is a type constructor `m` that depends on some type parameter `α`—i.e., `m α`—equipped with two distinguished operations:

    pure : Π{α : Type}, α → m α
    bind : Π{α β : Type}, m α → (α → m β) → m β

For `option`:

* `pure` := `some`
* `bind` := `bind_option`

Intuitively, we can think of a monad as a "box":

* `pure` puts the data into the box

* `bind` allows us to access the data in the box and modify it (possibly even changing its type, since the result is an `m β` monad, not a `m α` monad)

There is no general way to extract the data from the monad, i.e., to obtain an `α` from an `m α`

To summarize, `pure a` (also called `return a`) provides no side effect and simply provides a box containing the the value `a`, whereas `bind ma f` (also written `ma >>= f`) executes `ma`, then executes `f` with the boxed result `a` of `ma`

The option monad is only one instance among many

Type         | Effect
------------ | ------
`option α`   | failure when `none`; otherwise, `some a` is the result
`set α`      | nondeterministic behavior (set of behaviors)
`t → α`      | reading elements of type `t` (e.g., a configuration)
`ℕ × α`      | adjoining running time (e.g., to model algorithmic complexity)
`string × α` | adjoining text output (e.g., for logging)
`prob α`     | probability (e.g., using random number generators)
`io α`       | interaction with the operating system
`tactic α`   | interaction with the prover


All of the above are type constructors `m` are parameterized by a type `α`

Some effects can be combined (e.g., `option (t → α)`)

Some effects are not executable (e.g., `set α`, `prob α`); they are nonetheless useful for modeling programs abstractly in the logic

Specific monads may provide a way to extract the boxed value stored in the monad without `bind`'s requirement of putting it back in a monad

Monads have several benefits, including:

* They provide the convenient and highly readable `do` notation

* They support generic operations, such as `mmap : (α → M β) → list α → M (list β)`, which work uniformly across all monad instances

To quote _Programming in Lean_:

> The power of the abstraction is not only that it provides general functions and notation the can be used in all these various instantiations, but also that it provides a helpful way of thinking about what they all have in common

For us, they are interesting in three ways:

* Monads are a useful concept in their own right

* Monads provide a nice, "nonmathematical" example of axiomatic reasoning

* Monads are useful for programming Lean itself (metaprogramming)


## Monadic Laws

The `bind` and `pure` operations are normally required to obey three laws, called the monadic laws

Pure data as the first program:

    do
      a' ← pure a,
      f a'
    ═════════════
    f a

Pure data as the second program:

    do
      a ← x,
      pure a
    ══════════════
    x

Nested programs `x`, `f`, `g` can be linearized using this associativity rule:

    do
      b ← (do
        a ← x,
        f a),
      g b
    ══════════
    do
      a ← x,
      b ← f a,
      g b


## A Type Class of Monads

Monads are a mathematical structure, so we use class to add them as a type class (lecture 12)

We can think of a type class as a structure or record that is parameterized by a type—or here, by a type constructor `m : Type → Type`

    class lawful_monad (m : Type → Type)
      extends has_bind m, has_pure m : Type 1 :=
    (pure_bind {α β} (a : α) (f : α → m β) :
      (pure a >>= f) = f a)
    (bind_pure {α} (ma : m α) :
      ma >>= pure = ma)
    (bind_assoc {α β γ} (f : α → m β) (g : β → m γ) (ma : m α) :
      ((ma >>= f) >>= g) = (ma >>= (λa, f a >>= g)))

Step by step:

* We are creating a structure parameterized by a unary type constructor `m : Type → Type`

* The type class inherits the fields, and any syntactic sugar, from type classes called `has_bind` and `has_pure`, which provide the `bind` and `pure` operations on `m` and some syntactic sugar

* The type `Type 1` is a technical necessity explained in lecture 11

* The definition adds three fields to those already provided by `has_bind` and `has_pure`, to store the proofs of the three monadic laws

To instantiate this definition with a concrete monad, we must supply the monad `m` (e.g., `option`), suitable `bind` and `pure` operators, and proofs of the three monadic laws

(Lean's actual definition of monads is more complicated; one of the differences is that it distributes the definition over two type classes, called `monad` and `is_lawful_monad`)


## Demo

[`love06_monads_demo.lean`](../lean/love06_monads_demo.lean)
