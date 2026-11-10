import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

/-!
# FL: a first-order functional language over binary trees

FL is the bridge between Lean functions and register programs (`RegMachine`). Every
value is a binary tree `Val`; numbers, booleans, lists and records are encoded as trees
(`FL/Encode.lean`). A program is a list of one-argument function bodies; recursion is
general (termination is witnessed by the evaluation derivation).

The big-step judgement `Eval P m env e v cost depth` records
* `cost`: the number of evaluation nodes (the interpreter's step count is linear in it),
* `depth`: the maximal nesting of function calls (the interpreter's stack height is
  linear in it, with a program-dependent constant),
* `m`: a bound on the size of every value bound or produced (the interpreter's register
  contents are bounded by `O((depth + 1) * (m + 1))`).

Variables are de Bruijn indices into the environment `env` (index 0 is the innermost).
A function body runs in the environment `[argument]`.
-/

set_option autoImplicit false

namespace QecReliability.FL

/-- Binary trees: the single value type of FL. -/
inductive Val where
  | nil : Val
  | cons : Val → Val → Val
  deriving DecidableEq, Repr, Inhabited

namespace Val

/-- Length of the preorder serialization `bits` (one bit per node). -/
def size : Val → ℕ
  | nil => 1
  | cons a b => 1 + a.size + b.size

/-- Preorder serialization: `nil ↦ 0`, `cons a b ↦ 1 a b`. -/
def bits : Val → List Bool
  | nil => [false]
  | cons a b => true :: (a.bits ++ b.bits)

@[simp] theorem size_nil : nil.size = 1 := rfl
@[simp] theorem size_cons (a b : Val) : (cons a b).size = 1 + a.size + b.size := rfl

theorem size_pos (v : Val) : 0 < v.size := by
  cases v <;> simp only [size] <;> omega

@[simp] theorem bits_length (v : Val) : v.bits.length = v.size := by
  induction v with
  | nil => rfl
  | cons a b iha ihb => simp [bits, size, iha, ihb]; omega

/-- Parse one serialized tree off the front of a bit list; returns the tree and the rest.
`fuel` bounds the recursion; `bits.length + 1` always suffices. -/
def parse : ℕ → List Bool → Option (Val × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some (nil, rest)
  | fuel + 1, true :: rest =>
      match parse fuel rest with
      | none => none
      | some (a, rest') =>
          match parse fuel rest' with
          | none => none
          | some (b, rest'') => some (cons a b, rest'')

theorem parse_bits_append (v : Val) (rest : List Bool) (fuel : ℕ) (h : v.size ≤ fuel) :
    parse fuel (v.bits ++ rest) = some (v, rest) := by
  induction v generalizing rest fuel with
  | nil =>
    cases fuel with
    | zero => simp [size] at h
    | succ f => simp [parse, bits]
  | cons a b iha ihb =>
    cases fuel with
    | zero => simp [size] at h
    | succ f =>
      have ha : a.size ≤ f := by simp [size] at h; omega
      have hb : b.size ≤ f := by simp [size] at h; omega
      simp only [bits, List.cons_append, parse, List.append_assoc]
      rw [iha _ _ ha]
      simp only
      rw [ihb _ _ hb]

/-- Serialization is injective (it is a prefix code). -/
theorem bits_injective : Function.Injective bits := by
  intro v w h
  have hv := parse_bits_append v [] (v.size + w.size) (by omega)
  have hw := parse_bits_append w [] (v.size + w.size) (by omega)
  rw [List.append_nil] at hv hw
  rw [h, hw] at hv
  exact (Prod.mk.inj (Option.some.inj hv)).1.symm

end Val

/-- FL expressions. `case s e₁ e₂` evaluates `e₁` when `s` is `nil` and `e₂` with the head
and tail of `s` bound (head = `var 0`, tail = `var 1`) when it is a `cons`. `cond s e₁ e₂`
is the same test without binding anything; `fst`/`snd` project a `cons`. -/
inductive Expr where
  | var : ℕ → Expr
  | nil : Expr
  | cons : Expr → Expr → Expr
  | case : Expr → Expr → Expr → Expr
  | call : ℕ → Expr → Expr
  | letE : Expr → Expr → Expr
  | cond : Expr → Expr → Expr → Expr
  | fst : Expr → Expr
  | snd : Expr → Expr
  deriving DecidableEq, Repr, Inhabited

/-- Function `f` has body `P[f]`; its argument is `var 0`. -/
abbrev Program := List Expr

namespace Expr

/-- Syntactic size; bounds the interpreter's per-frame bookkeeping. -/
def size : Expr → ℕ
  | var _ => 1
  | nil => 1
  | cons a b => 1 + a.size + b.size
  | case s a b => 1 + s.size + a.size + b.size
  | call _ a => 1 + a.size
  | letE a b => 1 + a.size + b.size
  | cond s a b => 1 + s.size + a.size + b.size
  | fst a => 1 + a.size
  | snd a => 1 + a.size

end Expr

/-- Big-step evaluation with node cost, call depth, and value-size bound `m`. -/
inductive Eval (P : Program) (m : ℕ) : List Val → Expr → Val → ℕ → ℕ → Prop
  | var {env i v} : env[i]? = some v → Eval P m env (.var i) v 1 0
  | nil {env} : Eval P m env .nil .nil 1 0
  | cons {env a b va vb ta tb da db} :
      Eval P m env a va ta da → Eval P m env b vb tb db → (Val.cons va vb).size ≤ m →
      Eval P m env (.cons a b) (.cons va vb) (ta + tb + 1) (max da db)
  | caseNil {env s e₁ e₂ v ts t₁ ds d₁} :
      Eval P m env s .nil ts ds → Eval P m env e₁ v t₁ d₁ →
      Eval P m env (.case s e₁ e₂) v (ts + t₁ + 1) (max ds d₁)
  | caseCons {env s e₁ e₂ h tl v ts t₂ ds d₂} :
      Eval P m env s (.cons h tl) ts ds → Eval P m (h :: tl :: env) e₂ v t₂ d₂ →
      Eval P m env (.case s e₁ e₂) v (ts + t₂ + 1) (max ds d₂)
  | call {env f a body va v ta tb da db} :
      Eval P m env a va ta da → P[f]? = some body → Eval P m [va] body v tb db →
      Eval P m env (.call f a) v (ta + tb + 1) (max da (db + 1))
  | letE {env a b va v ta tb da db} :
      Eval P m env a va ta da → Eval P m (va :: env) b v tb db →
      Eval P m env (.letE a b) v (ta + tb + 1) (max da db)
  | condNil {env s e₁ e₂ v ts t₁ ds d₁} :
      Eval P m env s .nil ts ds → Eval P m env e₁ v t₁ d₁ →
      Eval P m env (.cond s e₁ e₂) v (ts + t₁ + 1) (max ds d₁)
  | condCons {env s e₁ e₂ h tl v ts t₂ ds d₂} :
      Eval P m env s (.cons h tl) ts ds → Eval P m env e₂ v t₂ d₂ →
      Eval P m env (.cond s e₁ e₂) v (ts + t₂ + 1) (max ds d₂)
  | fst {env e a b t d} : Eval P m env e (.cons a b) t d → Eval P m env (.fst e) a (t + 1) d
  | snd {env e a b t d} : Eval P m env e (.cons a b) t d → Eval P m env (.snd e) b (t + 1) d

namespace Eval

variable {P : Program} {m : ℕ}

/-- Evaluation is deterministic, including its cost and depth. -/
theorem det {env : List Val} {e : Expr} {v w : Val} {t t' d d' : ℕ}
    (h : Eval P m env e v t d) (g : Eval P m env e w t' d') : v = w ∧ t = t' ∧ d = d' := by
  induction h generalizing w t' d' with
  | var hv => cases g with | var hw => rw [hv] at hw; exact ⟨Option.some.inj hw, rfl, rfl⟩
  | nil => cases g; exact ⟨rfl, rfl, rfl⟩
  | cons _ _ _ iha ihb =>
    cases g with
    | cons ga gb _ =>
      obtain ⟨rfl, rfl, rfl⟩ := iha ga
      obtain ⟨rfl, rfl, rfl⟩ := ihb gb
      exact ⟨rfl, rfl, rfl⟩
  | caseNil _ _ ihs ih₁ =>
    cases g with
    | caseNil gs g₁ =>
      obtain ⟨-, rfl, rfl⟩ := ihs gs
      obtain ⟨rfl, rfl, rfl⟩ := ih₁ g₁
      exact ⟨rfl, rfl, rfl⟩
    | caseCons gs _ => exact absurd (ihs gs).1 (by simp)
  | caseCons _ _ ihs ih₂ =>
    cases g with
    | caseNil gs _ => exact absurd (ihs gs).1 (by simp)
    | caseCons gs g₂ =>
      obtain ⟨hv, rfl, rfl⟩ := ihs gs
      cases hv
      obtain ⟨rfl, rfl, rfl⟩ := ih₂ g₂
      exact ⟨rfl, rfl, rfl⟩
  | call _ hb _ iha ihb =>
    cases g with
    | call ga gb gc =>
      obtain ⟨rfl, rfl, rfl⟩ := iha ga
      rw [hb] at gb
      cases gb
      obtain ⟨rfl, rfl, rfl⟩ := ihb gc
      exact ⟨rfl, rfl, rfl⟩
  | letE _ _ iha ihb =>
    cases g with
    | letE ga gb =>
      obtain ⟨rfl, rfl, rfl⟩ := iha ga
      obtain ⟨rfl, rfl, rfl⟩ := ihb gb
      exact ⟨rfl, rfl, rfl⟩
  | condNil _ _ ihs ih₁ =>
    cases g with
    | condNil gs g₁ =>
      obtain ⟨-, rfl, rfl⟩ := ihs gs
      obtain ⟨rfl, rfl, rfl⟩ := ih₁ g₁
      exact ⟨rfl, rfl, rfl⟩
    | condCons gs _ => exact absurd (ihs gs).1 (by simp)
  | condCons _ _ ihs ih₂ =>
    cases g with
    | condNil gs _ => exact absurd (ihs gs).1 (by simp)
    | condCons gs g₂ =>
      obtain ⟨-, rfl, rfl⟩ := ihs gs
      obtain ⟨rfl, rfl, rfl⟩ := ih₂ g₂
      exact ⟨rfl, rfl, rfl⟩
  | fst _ ih =>
    cases g with
    | fst g' =>
      obtain ⟨hv, rfl, rfl⟩ := ih g'
      cases hv
      exact ⟨rfl, rfl, rfl⟩
  | snd _ ih =>
    cases g with
    | snd g' =>
      obtain ⟨hv, rfl, rfl⟩ := ih g'
      cases hv
      exact ⟨rfl, rfl, rfl⟩

/-- A larger size bound admits the same evaluation. -/
theorem mono {m' : ℕ} (hm : m ≤ m') {env : List Val} {e : Expr} {v : Val} {t d : ℕ}
    (h : Eval P m env e v t d) : Eval P m' env e v t d := by
  induction h with
  | var hv => exact .var hv
  | nil => exact .nil
  | cons _ _ hs iha ihb => exact .cons iha ihb (Nat.le_trans hs hm)
  | caseNil _ _ ihs ih₁ => exact .caseNil ihs ih₁
  | caseCons _ _ ihs ih₂ => exact .caseCons ihs ih₂
  | call _ hb _ iha ihb => exact .call iha hb ihb
  | letE _ _ iha ihb => exact .letE iha ihb
  | condNil _ _ ihs ih₁ => exact .condNil ihs ih₁
  | condCons _ _ ihs ih₂ => exact .condCons ihs ih₂
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

theorem cost_pos {env : List Val} {e : Expr} {v : Val} {t d : ℕ}
    (h : Eval P m env e v t d) : 0 < t := by
  cases h <;> omega

end Eval

/-- `P` computes the call `f x = y` with cost at most `t`, call depth at most `d`, and every
intermediate value of size at most `m` (the argument included). -/
def Computes (P : Program) (f : ℕ) (x y : Val) (m t d : ℕ) : Prop :=
  x.size ≤ m ∧ ∃ t' d', t' ≤ t ∧ d' ≤ d ∧ Eval P m [x] (.call f (.var 0)) y t' d'

end QecReliability.FL
