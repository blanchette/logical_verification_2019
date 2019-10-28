/- LoVe Exercise 1: Definitions and Lemma Statements -/

/- Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

import .love01_definitions_and_lemma_statements_demo

namespace LoVe


/- Question 1: Fibonacci Numbers -/

/- 1.1. Define the function `fib` that computes the Fibonacci numbers. -/

def fib : ℕ → ℕ
:= sorry

/- 1.2. Check that your function works as expected. -/

#reduce fib 0  -- expected: 0
#reduce fib 1  -- expected: 1
#reduce fib 2  -- expected: 1
#reduce fib 3  -- expected: 2
#reduce fib 4  -- expected: 3
#reduce fib 5  -- expected: 5
#reduce fib 6  -- expected: 8
#reduce fib 7  -- expected: 13
#reduce fib 8  -- expected: 21


/- Question 2: Arithmetic Expressions -/

/- Consider the type `aexp` from the lecture. -/

#print aexp
#check eval

/- 2.1. Test that `eval` behaves as expected. Making sure to exercise each
constructor at least once. You can use the following environment in your
tests. What happens if you divide by zero? -/

def some_env : string → ℤ
| "x" := 3
| "y" := 17
| _   := 201

-- invoke `#eval` here

/- 2.2. The following function simplifies arithmetic expressions involving
addition. It simplifies `0 + e` and `e + 0` to `e`. Complete the definition so
that it also simplifies expressions involving the other three binary
operators. -/

def simplify : aexp → aexp
| (aexp.add (aexp.num 0) e₂) := simplify e₂
| (aexp.add e₁ (aexp.num 0)) := simplify e₁
-- insert the missing cases here
-- catch-all cases below
| (aexp.num i)               := aexp.num i
| (aexp.var x)               := aexp.var x
| (aexp.add e₁ e₂)           := aexp.add (simplify e₁) (simplify e₂)
| (aexp.sub e₁ e₂)           := aexp.sub (simplify e₁) (simplify e₂)
| (aexp.mul e₁ e₂)           := aexp.mul (simplify e₁) (simplify e₂)
| (aexp.div e₁ e₂)           := aexp.div (simplify e₁) (simplify e₂)

/- 2.3. State the correctness lemma for `simplify`, namely that the simplified
expression should have the same semantics, with respect to `eval`, as the
original expression. -/

-- enter your lemma statement here


/- Question 3: λ-Terms -/

/- We start by declaring three new opaque types. -/

constants α β γ : Type

/- 3.1. Complete the following definitions, by replacing the `sorry` markers by
terms of the expected type.

Hint: You can use `_` as a placeholder while constructing a term. By hovering
over `_`, you will see the current logical context. -/

def I : α → α :=
λa, a

def K : α → β → α :=
λa b, a

def C : (α → β → γ) → β → α → γ :=
sorry

def proj_1st : α → α → α :=
sorry

-- please give a different answer than for `proj_1st`
def proj_2nd : α → α → α :=
sorry

def some_nonsense : (α → β → γ) → α → (α → γ) → β → γ :=
sorry

/- 3.2. Show the typing derivation for your definition of `C` above. -/

-- write your solution here in a comment or on paper

end LoVe
