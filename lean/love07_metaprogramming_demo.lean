/- LoVe Demo 7: Metaprogramming -/

import .lovelib

namespace LoVe


/- The Tactic Monad -/

example :
  true :=
by tactic.triv

example :
  true :=
by do
  tactic.trace "Hello, Metacosmos!",
  tactic.triv

meta def hello_world : tactic unit :=
do
  tactic.trace "Hello, Metacosmos!",
  tactic.triv

example :
  true :=
by hello_world

run_cmd tactic.trace "Hello, Metacosmos!"

open tactic

example (α : Type) (a : α) :
  true :=
by do
  trace "local context:",
  local_context >>= trace,
  trace "goals:",
  get_goals >>= trace,
  trace "target:",
  target >>= trace,
  triv

meta def exact_list : list expr → tactic unit
| []        := fail "no matching expression found"
| (e :: es) :=
  (do
     trace "trying ",
     trace e,
     exact e)
  <|> exact_list es

meta def find_assumption : tactic unit := do
  es ← local_context,
  exact_list es

example {p : Prop} {α : Type} (a : α) (h : p) :
  p :=
by do find_assumption

example {p : Prop} (h : p) :
  p :=
by do
  p_proof ← get_local `h,
  trace "p_proof:",
  trace p_proof,
  trace (expr.to_raw_fmt p_proof),
  trace "type of p_proof:",
  infer_type p_proof >>= trace,
  trace "type of type of p_proof:",
  infer_type p_proof >>= infer_type >>= trace,
  apply p_proof


/- Names and Expressions -/

#print expr

#check expr tt  -- elaborated expressions
#check expr ff  -- unelaborated expressions (pre-expressions)

#print name

#check (expr.const `ℕ [] : expr)
#check expr.sort level.zero  -- Sort 0, i.e., Prop
#check expr.sort (level.succ level.zero)
  -- Sort 1, i.e., Type 0 (Type)
#check expr.var 0  -- bound variable with De Bruijn index 0
#check (expr.local_const `uniq_name `pp_name binder_info.default
  `(ℕ) : expr)
#check (expr.mvar `uniq_name `pp_name `(ℕ) : expr)
#check (expr.pi `pp_name binder_info.default `(ℕ)
  (expr.sort level.zero) : expr)
#check (expr.lam `pp_name binder_info.default `(ℕ)
  (expr.var 0) : expr)
#check expr.elet
#check expr.macro

run_cmd do
  let e : expr := `(list.map (λn : ℕ, n + 1) [1, 2, 3]),
  trace e

run_cmd do
  let e : expr := `(list.map _ [1, 2, 3]),
    -- fails (holes are disallowed)
  skip

run_cmd do
  let e₁ : pexpr := ``(list.map (λn, n + 1) [1, 2, 3]),
  let e₂ : pexpr := ``(list.map _ [1, 2, 3]),
  trace e₁,
  trace e₂

run_cmd do
  let e := ```(some_silly_name),
  trace e

run_cmd trace `some.silly.name
run_cmd trace ``true
run_cmd trace ``some.silly.name  -- fails (not found)

run_cmd do
  let x : expr := `(2 : ℕ),
  let e : expr := `(%%x + 1),
  trace e

run_cmd do
  let x : expr := `(@id ℕ),
  let e := ``(list.map %%x),
  trace e

run_cmd do
  let x : expr := `(@id ℕ),
  let e := ```(a _ %%x),
  trace e

example :
  1 + 2 = 3 :=
by do
  `(%%a + %%b = %%c) ← target,
  trace a,
  trace b,
  trace c,
  `(@eq %%α %%l %%r) ← target,
  trace α,
  trace l,
  trace r,
  exact `(refl _ : 3 = 3)


/- A Simple Tactic: `destruct_and` -/

example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) :
  a :=
and.elim_left h

example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) :
  b :=
and.elim_left (and.elim_left (and.elim_right h))

example {a b c d : Prop} (h : a ∧ (b ∧ c) ∧ d) :
  b ∧ c :=
and.elim_left (and.elim_right h)

meta def destruct_and_helper : expr → expr → tactic unit
| `(%%a ∧ %%b) h :=
    exact h
    <|> (do
      ha ← to_expr ``(and.elim_left %%h),
      destruct_and_helper a ha)
    <|> (do
      hb ← to_expr ``(and.elim_right %%h),
      destruct_and_helper b hb)
| _            h := exact h

meta def destruct_and (nam : name) : tactic unit :=
do
  h ← get_local nam,
  t ← infer_type h,
  destruct_and_helper t h

example {a b c d : Prop} (h : a ∧ b ∧ c) :
  a :=
by destruct_and `h

example {a b c d : Prop} (h : a ∧ b ∧ c) :
  c :=
by destruct_and `h

example {a b c d : Prop} (h : a ∧ b ∧ c) :
  b ∧ c :=
by destruct_and `h

example {a b c d : Prop} (h : a ∧ b ∧ c) :
  a ∧ c :=
by destruct_and `h  -- fails


/- Example: A Solvability Advisor -/

meta def is_theorem : declaration → bool
| (declaration.defn _ _ _ _ _ _) := ff
| (declaration.thm _ _ _ _)      := tt
| (declaration.cnst _ _ _ _)     := ff
| (declaration.ax _ _ _)         := tt

meta def get_all_theorems : tactic (list name) :=
do
  env ← get_env,
  pure (environment.fold env [] (λdecl nams,
    if is_theorem decl then declaration.to_name decl :: nams
    else nams))

meta def solve_with_name (nam : name) : tactic unit :=
do
  cst ← mk_const nam,
  apply cst
    ({ md := transparency.reducible, unify := ff } : apply_cfg),
  all_goals assumption

meta def solve_direct : tactic unit :=
do
  nams ← get_all_theorems,
  list.mfirst (λnam,
    do
      solve_with_name nam,
      trace ("directly solved by " ++ to_string nam))
    nams

example {x y : ℕ} (h : x = y) :
  y = x :=
by solve_direct

meta def solve_direct_symm : tactic unit :=
solve_direct
<|> (do
  cst ← mk_const `eq.symm,
  apply cst,
  solve_direct)

example {n : ℕ} :
  n + 0 = n :=
by solve_direct_symm

example {n : ℕ} :
  n = n + 0 :=
by solve_direct_symm

end LoVe
