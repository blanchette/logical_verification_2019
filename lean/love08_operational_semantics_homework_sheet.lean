/- LoVe Homework 8: Operational Semantics -/

import .lovelib

namespace LoVe


/- Question 1: Semantics of Regular Expressions

Regular expression are a very popular tool for software development. Often, when
textual input needs to be analyzed it is matched against a regular expression.
In this homework, we define the syntax of regular expressions and what it means
that a regular expression matches a string.

We define `regex` to represent the following grammar:

    R ::= c       — `char`: accepts one character `c`
        | ∅       — `nothing`: accepts nothing
        | ε       — `empty`: accepts the empty string
        | R ⬝ R    — `concat`: accepts the concatenation of two regexes
        | R + R   — `alt`: accepts either of two regexes
        | R*      — `star`: accept arbitrary many repetitions of a regex

Notice the rough correspondence with a WHILE language:

  `char`   ~ assignment
  `empty`  ~ `skip`
  `concat` ~ sequential composition
  `alt`    ~ conditional statement
  `star`   ~ while loop -/

inductive regex : Type
| char    : char → regex
| nothing : regex
| empty   : regex
| concat  : regex → regex → regex
| alt     : regex → regex → regex
| star    : regex → regex

/- The `accept r s` predicate indicates that the regular expression `r` accepts
the string `s`. -/

inductive accept : regex → list char → Prop
/- accept one character -/
| char (c : char) :
  accept (regex.char c) [c]
/- accept the empty string -/
| empty :
  accept regex.empty []
/- accept two concatenated regexes -/
| concat {r₁ r₂ : regex} (s₁ s₂ : list char) (h₁ : accept r₁ s₁)
    (h₂ : accept r₂ s₂) :
  accept (regex.concat r₁ r₂) (s₁ ++ s₂)
/- accept the left alternative -/
| alt_left {r₁ r₂ : regex} (s : list char) (h : accept r₁ s) :
  accept (regex.alt r₁ r₂) s
/- accept the right alternative -/
| alt_right {r₁ r₂ : regex} (s : list char) (h : accept r₂ s) :
  accept (regex.alt r₁ r₂) s
/- accepts the empty string; this is the base case of `R*` -/
| star_base {r : regex} : accept (regex.star r) []
/- accepts `R` followed again by `R*`; this is the induction step of `R*` -/
| star_step {r : regex} (s s' : list char) (h₁ : accept r s)
    (h₂ : accept (regex.star r) s') :
  accept (regex.star r) (s ++ s')

/- 1.1. Explain why there is no rule for `nothing`. -/

-- enter your answer here

/- 1.2. Prove the following inversion rules.

These proofs are very similar to the inversion rules in the lecture and the
exercise. -/

@[simp] lemma accept_char {s : list char} {c : char} :
  accept (regex.char c) s ↔ s = [c] :=
sorry

@[simp] lemma accept_nothing {s : list char} :
  ¬ accept regex.nothing s :=
sorry

@[simp] lemma accept_empty {s : list char} :
  accept regex.empty s ↔ s = [] :=
sorry

@[simp] lemma accept_concat {s : list char} {r₁ r₂  : regex} :
  accept (regex.concat r₁ r₂) s
  ↔ (∃s₁ s₂, accept r₁ s₁ ∧ accept r₂ s₂ ∧ s = s₁ ++ s₂) :=
sorry

@[simp] lemma accept_alt {s : list char} {r₁ r₂  : regex} :
  accept (regex.alt r₁ r₂) s ↔ (accept r₁ s ∨ accept r₂ s) :=
sorry

lemma accept_star {s : list char} {r : regex} :
  accept (regex.star r) s ↔
  (s = [] ∨ (∃s₁ s₂, accept r s₁ ∧ accept (regex.star r) s₂ ∧ s = s₁ ++ s₂)) :=
sorry

end LoVe
