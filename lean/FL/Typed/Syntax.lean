import FL.Typed.Fn
import Mathlib.Tactic.Simps.Basic

/-!
# FL.Typed.Syntax: conveniences for writing typed bodies

* `Tm.v0 … Tm.v7`: the de Bruijn variables `0 … 7` (`v0` is the innermost binder).
* Boolean connectives as `ite` macros: `Tm.not`, `Tm.and`, `Tm.or`, `Tm.xor`, `Tm.xor3`,
  `Tm.maj` (majority, i.e. the carry of a full adder), `Tm.borrow`.
* `Tm.isZero`, `Tm.isPos`, `Tm.div2`, `Tm.odd` on the binary encoding (one `ncase`).

All are `abbrev`s, so `simp [Tm.den, Tm.cost, …]` sees through them; the `@[simp]` lemmas
below give their meanings directly.
-/

set_option autoImplicit false

namespace QecReliability.FL

namespace Tm

abbrev v0 {Γ : List Ty} {t : Ty} : Tm (t :: Γ) t := .var .zero
abbrev v1 {Γ : List Ty} {s₀ t : Ty} : Tm (s₀ :: t :: Γ) t := .var (.succ .zero)
abbrev v2 {Γ : List Ty} {s₀ s₁ t : Ty} : Tm (s₀ :: s₁ :: t :: Γ) t :=
  .var (.succ (.succ .zero))
abbrev v3 {Γ : List Ty} {s₀ s₁ s₂ t : Ty} : Tm (s₀ :: s₁ :: s₂ :: t :: Γ) t :=
  .var (.succ (.succ (.succ .zero)))
abbrev v4 {Γ : List Ty} {s₀ s₁ s₂ s₃ t : Ty} : Tm (s₀ :: s₁ :: s₂ :: s₃ :: t :: Γ) t :=
  .var (.succ (.succ (.succ (.succ .zero))))
abbrev v5 {Γ : List Ty} {s₀ s₁ s₂ s₃ s₄ t : Ty} :
    Tm (s₀ :: s₁ :: s₂ :: s₃ :: s₄ :: t :: Γ) t :=
  .var (.succ (.succ (.succ (.succ (.succ .zero)))))
abbrev v6 {Γ : List Ty} {s₀ s₁ s₂ s₃ s₄ s₅ t : Ty} :
    Tm (s₀ :: s₁ :: s₂ :: s₃ :: s₄ :: s₅ :: t :: Γ) t :=
  .var (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))
abbrev v7 {Γ : List Ty} {s₀ s₁ s₂ s₃ s₄ s₅ s₆ t : Ty} :
    Tm (s₀ :: s₁ :: s₂ :: s₃ :: s₄ :: s₅ :: s₆ :: t :: Γ) t :=
  .var (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))))

/-! ## Booleans -/

abbrev not {Γ : List Ty} (b : Tm Γ .bool) : Tm Γ .bool := .ite b .ff .tt
abbrev and {Γ : List Ty} (b c : Tm Γ .bool) : Tm Γ .bool := .ite b c .ff
abbrev or {Γ : List Ty} (b c : Tm Γ .bool) : Tm Γ .bool := .ite b .tt c
abbrev xor {Γ : List Ty} (b c : Tm Γ .bool) : Tm Γ .bool := .ite b (.not c) c
/-- Sum bit of a full adder. -/
abbrev xor3 {Γ : List Ty} (b c d : Tm Γ .bool) : Tm Γ .bool := .ite b (.not (.xor c d)) (.xor c d)
/-- Majority: carry of a full adder. -/
abbrev maj {Γ : List Ty} (b c d : Tm Γ .bool) : Tm Γ .bool := .ite b (.or c d) (.and c d)
/-- Borrow of a full subtractor `b - c - d`: `b < c + d`. -/
abbrev borrow {Γ : List Ty} (b c d : Tm Γ .bool) : Tm Γ .bool := .ite b (.and c d) (.or c d)

/-! ## One-step operations on binary naturals -/

abbrev isZero {Γ : List Ty} (n : Tm Γ .nat) : Tm Γ .bool := .ncase n .tt .ff
abbrev isPos {Γ : List Ty} (n : Tm Γ .nat) : Tm Γ .bool := .ncase n .ff .tt
abbrev div2 {Γ : List Ty} (n : Tm Γ .nat) : Tm Γ .nat := .ncase n .zero v1
abbrev odd {Γ : List Ty} (n : Tm Γ .nat) : Tm Γ .bool := .ncase n .ff v0

variable {Γ : List Ty} (ρ : Env Γ)

@[simp] theorem den_not (b : Tm Γ .bool) : (Tm.not b).den ρ = !(b.den ρ) := by
  cases h : b.den ρ <;> simp [den, h]
@[simp] theorem den_and (b c : Tm Γ .bool) : (Tm.and b c).den ρ = (b.den ρ && c.den ρ) := by
  cases h : b.den ρ <;> simp [den, h]
@[simp] theorem den_or (b c : Tm Γ .bool) : (Tm.or b c).den ρ = (b.den ρ || c.den ρ) := by
  cases h : b.den ρ <;> simp [den, h]
@[simp] theorem den_xor (b c : Tm Γ .bool) :
    (Tm.xor b c).den ρ = Bool.xor (b.den ρ) (c.den ρ) := by
  cases h : b.den ρ <;> cases h' : c.den ρ <;> simp [den, h, h']
@[simp] theorem den_isZero (n : Tm Γ .nat) : (isZero n).den ρ = decide (n.den ρ = 0) := by
  by_cases h : n.den ρ = 0 <;> simp [den, h]
@[simp] theorem den_isPos (n : Tm Γ .nat) : (isPos n).den ρ = decide (n.den ρ ≠ 0) := by
  by_cases h : n.den ρ = 0 <;> simp [den, h]
@[simp] theorem den_div2 (n : Tm Γ .nat) : (div2 n).den ρ = n.den ρ / 2 := by
  by_cases h : n.den ρ = 0 <;> simp [den, h, Env.get]
@[simp] theorem den_odd (n : Tm Γ .nat) : (odd n).den ρ = decide (n.den ρ % 2 = 1) := by
  by_cases h : n.den ρ = 0 <;> simp [den, h, Env.get]

end Tm

/-! ## Small facts used by the library proofs -/

@[simp] theorem bitNat_false (n : ℕ) : bitNat false n = 2 * n := by simp [bitNat]
@[simp] theorem bitNat_true (n : ℕ) : bitNat true n = 2 * n + 1 := by simp [bitNat]

theorem Enc.nat_one : Enc.nat 1 = .cons (.cons .nil .nil) .nil := by
  rw [Enc.nat_pos (by omega)]; simp [Enc.nat_zero, Enc.bool]

@[simp] theorem Enc.nat_one_size : (Enc.nat 1).size = 5 := by rw [Enc.nat_one]; rfl
@[simp] theorem Enc.nat_zero_size : (Enc.nat 0).size = 1 := by rw [Enc.nat_zero]; rfl
@[simp] theorem Enc.bool_false_size : (Enc.bool false).size = 1 := rfl
@[simp] theorem Enc.bool_true_size : (Enc.bool true).size = 3 := rfl

theorem Ty.prod_eq_iff {a b : Ty} (p q : (Ty.prod a b).den) : p = q ↔ p.1 = q.1 ∧ p.2 = q.2 :=
  Prod.ext_iff

theorem Bool.true_eq_decide' (p : Prop) [Decidable p] : (true = decide p) ↔ p := by
  rw [eq_comm]; exact decide_eq_true_iff
theorem Bool.false_eq_decide' (p : Prop) [Decidable p] : (false = decide p) ↔ ¬p := by
  rw [eq_comm]; exact decide_eq_false_iff_not
theorem Bool.decide_eq_decide' {p q : Prop} [Decidable p] [Decidable q] :
    decide p = decide q ↔ (p ↔ q) := decide_eq_decide

theorem Bool.and_decide' (p q : Prop) [Decidable p] [Decidable q] :
    (decide p && decide q) = decide (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
theorem Bool.or_decide' (p q : Prop) [Decidable p] [Decidable q] :
    (decide p || decide q) = decide (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
theorem Bool.not_decide' (p : Prop) [Decidable p] : (!decide p) = decide (¬p) := by
  by_cases hp : p <;> simp [hp]

attribute [tm_simp] Tm.den Tm.cost Tm.depth Tm.msize Tm.CallsOK Env.get Ty.sz

theorem Nat.mod_two_cases (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n

/-! ## A tactic adding size bounds

`size_bounds` scans the goal for `(Enc.nat x).size`, `(Enc.bool b).size` and `Nat.size x`
and adds, for `omega`:
* `(Enc.nat x).size ≤ 4 * x.size + 1`, `(Enc.bool b).size ≤ 3`;
* for every `Nat.size x` (also those just introduced), a bound by the sizes of the
  immediate subterms of `x`, according to its head: `2 * k`, `2 * k + 1`, `k + 1`, `a + b`,
  `a * b`, `a / b`, `a - b`, `max a b`, `min a b` (recursively). -/

open Lean Meta Elab Tactic in
partial def collectEncArgs (e : Lean.Expr) (acc : Array (Name × Lean.Expr)) :
    Array (Name × Lean.Expr) :=
  let acc :=
    if e.isAppOfArity ``Val.size 1 then
      let arg := e.appArg!
      if arg.isAppOfArity ``Enc.nat 1 then
        if acc.any (fun p => p.1 == ``Enc.nat && p.2 == arg.appArg!) then acc
        else acc.push (``Enc.nat, arg.appArg!)
      else if arg.isAppOfArity ``Enc.bool 1 then
        if acc.any (fun p => p.1 == ``Enc.bool && p.2 == arg.appArg!) then acc
        else acc.push (``Enc.bool, arg.appArg!)
      else acc
    else acc
  match e with
  | Lean.Expr.app f a => collectEncArgs a (collectEncArgs f acc)
  | Lean.Expr.mdata _ b => collectEncArgs b acc
  | _ => acc

open Lean Meta Elab Tactic in
partial def collectSizeArgs (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let acc :=
    if e.isAppOfArity ``Nat.size 1 then
      if acc.contains e.appArg! then acc else acc.push e.appArg!
    else acc
  match e with
  | Lean.Expr.app f a => collectSizeArgs a (collectSizeArgs f acc)
  | Lean.Expr.mdata _ b => collectSizeArgs b acc
  | _ => acc

open Lean in
def isNumLit (e : Lean.Expr) (k : ℕ) : Bool :=
  e.rawNatLit? == some k ||
    (match e.getAppFnArgs with
     | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit? == some k
     | _ => false)

open Lean Meta Elab Tactic in
elab "size_bounds" : tactic => withMainContext do
  let goal0 ← instantiateMVars (← getMainTarget)
  -- also scan the generalized bound `tmRHS_def`, if present
  let lctx ← getLCtx
  let goal ← match lctx.findFromUserName? `tmRHS_def with
    | some d => do
      let t ← instantiateMVars d.type
      pure (mkApp2 (mkConst ``And) goal0 t)
    | none => pure goal0
  let mut todo : Array Lean.Expr := collectSizeArgs goal #[]
  for (kind, x) in collectEncArgs goal #[] do
    let stx ← Term.exprToSyntax x
    if kind == ``Enc.nat then
      evalTactic (← `(tactic| have := Enc.nat_size_le $stx))
      todo := todo.push x
    else
      evalTactic (← `(tactic| have := Enc.bool_size $stx))
  let mut seen : Array Lean.Expr := #[]
  let mut fuel := 200
  while 0 < todo.size && 0 < fuel do
    fuel := fuel - 1
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.push x
    match x.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      if isNumLit b 1 then
        match a.getAppFnArgs with
        | (``HMul.hMul, #[_, _, _, _, two, k]) =>
          if isNumLit two 2 then
            evalTactic (← `(tactic| have := NatSize.size_bit1_le $(← Term.exprToSyntax k)))
            todo := todo.push k
          else
            evalTactic (← `(tactic| have := NatSize.size_succ_le $(← Term.exprToSyntax a)))
            todo := todo.push a
        | _ =>
          evalTactic (← `(tactic| have := NatSize.size_succ_le $(← Term.exprToSyntax a)))
          todo := todo.push a
      else
        evalTactic (← `(tactic| have := NatSize.size_add_le' $(← Term.exprToSyntax a)
          $(← Term.exprToSyntax b)))
        todo := (todo.push a).push b
    | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      if isNumLit a 2 then
        evalTactic (← `(tactic| have := NatSize.size_double_le $(← Term.exprToSyntax b)))
        todo := todo.push b
      else
        evalTactic (← `(tactic| have := NatSize.size_mul_le $(← Term.exprToSyntax a)
          $(← Term.exprToSyntax b)))
        todo := (todo.push a).push b
    | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
      evalTactic (← `(tactic| have := NatSize.size_div_le $(← Term.exprToSyntax a)
        $(← Term.exprToSyntax b)))
      todo := todo.push a
    | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      evalTactic (← `(tactic| have := NatSize.size_sub_le $(← Term.exprToSyntax a)
        $(← Term.exprToSyntax b)))
      todo := todo.push a
    | (``Max.max, #[_, _, a, b]) =>
      evalTactic (← `(tactic| have := NatSize.size_max_le $(← Term.exprToSyntax a)
        $(← Term.exprToSyntax b)))
      todo := (todo.push a).push b
    | (``Min.min, #[_, _, a, b]) =>
      evalTactic (← `(tactic| have := NatSize.size_min_le $(← Term.exprToSyntax a)
        $(← Term.exprToSyntax b)))
      todo := todo.push a
    | (``Nat.size, #[y]) =>
      evalTactic (← `(tactic| have := NatSize.size_le_self $(← Term.exprToSyntax x)))
      todo := todo.push y
    | _ => pure ()

/-- Remove all `mdata` nodes (e.g. `save_info` left by `@[simps]` lemmas), which hide
arithmetic from `omega`. -/
partial def stripMData (e : Lean.Expr) : Lean.Expr :=
  e.replace fun e => match e with
    | Lean.Expr.mdata _ b => some (stripMData b)
    | _ => none

open Lean Meta Elab Tactic in
elab "strip_mdata" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  replaceMainGoal [← g.replaceTargetDefEq (stripMData t)]

open Lean Meta Elab Tactic in
elab "strip_mdata_at " h:ident : tactic => withMainContext do
  let g ← getMainGoal
  let fv ← getFVarId h
  let t ← instantiateMVars (← fv.getType)
  replaceMainGoal [← g.replaceLocalDeclDefEq fv (stripMData t)]

/- `gen_rhs`: if the goal is `a ≤ b` (on `ℕ`), generalize `b` to a fresh variable `tmRHS` and
record `tmRHS_def : b = tmRHS`. The bound side is then simplified once, in that hypothesis,
instead of once per conjunct of the simplified left-hand side. -/
open Lean Meta Elab Tactic in
elab "gen_rhs" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  match t.getAppFnArgs with
  | (``LE.le, #[ty, _, _, b]) =>
    if ty.isConstOf ``Nat then
      let stx ← Term.exprToSyntax b
      evalTactic (← `(tactic| generalize $(mkIdent `tmRHS_def) : $stx = $(mkIdent `tmRHS)))
  | _ => pure ()

/-- `tm_unfold [lemmas]`: the unfolding phase of `tm_auto` (simp, strip `mdata`, simp
again), leaving the arithmetic goal for a custom finish (e.g. `nlinarith`). -/
syntax "tm_unfold" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| tm_unfold) => `(tactic| tm_unfold [])
  | `(tactic| tm_unfold [$ls,*]) =>
    `(tactic| (simp [tm_simp, Ty.den, $ls,*] <;> strip_mdata <;> (try simp [$ls,*])))

/-- `tm_auto [lemmas]`: unfold the typed-term semantics with `simp`, add size bounds, and
finish with `omega`. The workhorse for the five `FnSig.BodyOK` obligations. -/
syntax "tm_auto" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| tm_auto) => `(tactic| tm_auto [])
  | `(tactic| tm_auto [$ls,*]) =>
    `(tactic| (gen_rhs <;> (try simp [tm_simp, Ty.den, $ls,*] at tmRHS_def) <;>
      (try strip_mdata_at tmRHS_def) <;>
      simp [tm_simp, Ty.den, $ls,*] <;> strip_mdata <;> (try simp [$ls,*]) <;> (try split_ifs) <;>
      (try simp only [Ty.prod_eq_iff, Prod.mk.injEq, Bool.true_eq_decide', Bool.false_eq_decide',
        Bool.decide_eq_decide', Bool.and_decide', Bool.or_decide', Bool.not_decide',
        decide_eq_true_eq, decide_eq_false_iff_not, Bool.true_eq_false,
        Bool.false_eq_true, iff_true, true_iff, iff_false, false_iff, true_and, and_true]) <;>
      strip_mdata <;> size_bounds <;> omega))

/-- `tm_lean [lemmas]`: like `tm_auto` but with `simp only` (structural lemmas, the given
lemmas, and a fixed cleanup set) instead of the full simp set. Use it for large bodies where
the full simp set blows up (nested `max`/`ite` in size goals). Callee signatures' `@[simps]`
lemmas (`fooF_cost`, …) must be passed explicitly. -/
syntax "tm_lean" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| tm_lean) => `(tactic| tm_lean [])
  | `(tactic| tm_lean [$ls,*]) =>
    `(tactic| (gen_rhs <;>
      (try simp only [tm_simp, Ty.enc_prod, Ty.enc_nat, Ty.enc_bool, Ty.enc_unit, Ty.enc_val,
        Ty.enc_list_nil, Ty.enc_list_cons, Ty.enc_list_cons_nat, Ty.enc_list_cons_bool,
        Ty.enc_list_cons_nat2, Ty.enc_prod_nat2, Ty.enc_list_nil_nat, Ty.enc_list_nil_bool,
        Ty.enc_list_nil_nat2, Val.size_cons, Val.size_nil, $ls,*] at tmRHS_def) <;>
      (try strip_mdata_at tmRHS_def) <;>
      simp only [tm_simp, Ty.enc_prod, Ty.enc_nat, Ty.enc_bool, Ty.enc_unit, Ty.enc_val,
        Ty.enc_list_nil, Ty.enc_list_cons, Ty.enc_list_cons_nat, Ty.enc_list_cons_bool,
        Ty.enc_list_cons_nat2, Ty.enc_prod_nat2, Ty.enc_list_nil_nat, Ty.enc_list_nil_bool,
        Ty.enc_list_nil_nat2, Val.size_cons, Val.size_nil, $ls,*] <;>
      strip_mdata <;>
      (try simp only [ite_true, ite_false, if_true, if_false, ↓reduceIte, decide_true,
        decide_false, decide_eq_true_eq, decide_eq_false_iff_not, Bool.true_eq_false,
        Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or,
        Bool.true_and, Bool.false_and, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false,
        not_true_eq_false, not_false_eq_true, max_le_iff, true_and, and_true, Nat.zero_le,
        eq_self_iff_true, Nat.size_zero, Enc.nat_zero_size, Enc.nat_one_size,
        Enc.bool_false_size, Enc.bool_true_size, Prod.fst, Prod.snd]) <;>
      (try split_ifs) <;>
      strip_mdata <;> size_bounds <;> omega))

end QecReliability.FL
