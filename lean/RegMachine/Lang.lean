import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

/-!
# Register programs: syntax and abstract semantics

A register program is a finite control-flow graph (CFG). Every node carries one
*primitive* and a routing table `Bool → Option node`: the primitive transforms the
state and returns a Boolean answer, which selects the next node (`none` = halt
with that answer). Operations simply ignore the answer (they return `true`),
tests leave the state unchanged.

The semantics is generic in the primitive set (`PrimSem`): a precondition, a
deterministic effect, and an abstract cost. `Exec` is the inductive big-step
"run to halt" relation; it carries no fuel. A state invariant `Inv` (typically a
register-length bound, i.e. a space bound) is required at every visited state.

`Instr R` is the basic instruction set over `R` registers (`clear`, `pushBack`,
`popFront`, `append`, `isEmpty`, `headIs`, `const`, `pushFront`) with its semantics
`basicSem`; its cost is `1 + (lengths of the registers it touches)`.
-/

set_option autoImplicit false

namespace QecReliability.RegMachine

/-- Register file: `R` registers, each a finite bit string. -/
abbrev Regs (R : ℕ) := Fin R → List Bool

/-- Abstract semantics of a primitive set `P` over states `S`. -/
structure PrimSem (P S : Type) where
  /-- Precondition under which the primitive is defined/implemented. -/
  pre : P → S → Prop
  /-- Effect: new state and Boolean answer (used for routing). -/
  eval : P → S → S × Bool
  /-- Abstract cost of executing the primitive in this state. -/
  cost : P → S → ℕ

/-- A finite control-flow-graph program with `n` nodes. -/
structure Prog (P : Type) (n : ℕ) where
  entry : Fin n
  prim : Fin n → P
  next : Fin n → Bool → Option (Fin n)

section Exec
variable {P S : Type} {n : ℕ}

/-- `Exec σ prog Inv i s N C t b`: started at node `i` in state `s`, the program
halts after executing `N` primitives of total abstract cost `C`, in state `t`
with answer `b`; every state along the way (including `s` and `t`) satisfies
`Inv`, and every executed primitive's precondition holds. -/
inductive Exec (σ : PrimSem P S) (prog : Prog P n) (Inv : S → Prop) :
    Fin n → S → ℕ → ℕ → S → Bool → Prop
  | halt {i : Fin n} {s t : S} {b : Bool} :
      Inv s → σ.pre (prog.prim i) s → σ.eval (prog.prim i) s = (t, b) → Inv t →
      prog.next i b = none → Exec σ prog Inv i s 1 (σ.cost (prog.prim i) s) t b
  | step {i j : Fin n} {s s' t : S} {b b' : Bool} {N C : ℕ} :
      Inv s → σ.pre (prog.prim i) s → σ.eval (prog.prim i) s = (s', b) →
      prog.next i b = some j → Exec σ prog Inv j s' N C t b' →
      Exec σ prog Inv i s (N + 1) (σ.cost (prog.prim i) s + C) t b'

variable {σ : PrimSem P S} {prog : Prog P n} {Inv : S → Prop}

/-- Executions are deterministic: steps, cost, final state and answer are unique. -/
theorem Exec.det {i : Fin n} {s t t' : S} {N N' C C' : ℕ} {b b' : Bool}
    (h : Exec σ prog Inv i s N C t b) (h' : Exec σ prog Inv i s N' C' t' b') :
    N = N' ∧ C = C' ∧ t = t' ∧ b = b' := by
  induction h generalizing N' C' t' b' with
  | halt _ _ he _ hn =>
    cases h' with
    | halt _ _ he' _ _ =>
      rw [he] at he'
      cases he'
      exact ⟨rfl, rfl, rfl, rfl⟩
    | step _ _ he' hn' _ =>
      rw [he] at he'
      cases he'
      rw [hn] at hn'
      cases hn'
  | step _ _ he hn _ ih =>
    cases h' with
    | halt _ _ he' _ hn' =>
      rw [he] at he'
      cases he'
      rw [hn] at hn'
      cases hn'
    | step _ _ he' hn' tail' =>
      rw [he] at he'
      cases he'
      rw [hn] at hn'
      cases hn'
      obtain ⟨h1, h2, h3, h4⟩ := ih tail'
      exact ⟨by rw [h1], by rw [h2], h3, h4⟩

/-- The invariant holds at the start of an execution. -/
theorem Exec.inv_start {i : Fin n} {s t : S} {N C : ℕ} {b : Bool}
    (h : Exec σ prog Inv i s N C t b) : Inv s := by
  cases h with
  | halt hs _ _ _ _ => exact hs
  | step hs _ _ _ _ => exact hs

/-- The invariant holds at the end of an execution. -/
theorem Exec.inv_end {i : Fin n} {s t : S} {N C : ℕ} {b : Bool}
    (h : Exec σ prog Inv i s N C t b) : Inv t := by
  induction h with
  | halt _ _ _ ht _ => exact ht
  | step _ _ _ _ _ ih => exact ih

/-- Every execution performs at least one primitive. -/
theorem Exec.steps_pos {i : Fin n} {s t : S} {N C : ℕ} {b : Bool}
    (h : Exec σ prog Inv i s N C t b) : 0 < N := by
  cases h <;> omega

/-- Weakening the invariant. -/
theorem Exec.mono {Inv' : S → Prop} (hI : ∀ s, Inv s → Inv' s) {i : Fin n} {s t : S}
    {N C : ℕ} {b : Bool} (h : Exec σ prog Inv i s N C t b) : Exec σ prog Inv' i s N C t b := by
  induction h with
  | halt hs hp he ht hn => exact .halt (hI _ hs) hp he (hI _ ht) hn
  | step hs hp he hn _ ih => exact .step (hI _ hs) hp he hn ih

end Exec

/-! ## The basic instruction set -/

/-- Basic register primitives over `R` registers. -/
inductive Instr (R : ℕ) where
  /-- `r := []` -/
  | clear (r : Fin R)
  /-- `r := r ++ [b]` -/
  | pushBack (r : Fin R) (b : Bool)
  /-- `r := r.tail` -/
  | popFront (r : Fin R)
  /-- `dst := dst ++ src` (precondition `dst ≠ src`) -/
  | append (dst src : Fin R)
  /-- test `r = []` -/
  | isEmpty (r : Fin R)
  /-- test `r.head? = some b` -/
  | headIs (r : Fin R) (b : Bool)
  /-- answer the constant `b` (used to halt with an output) -/
  | const (b : Bool)
  /-- `r := b :: r` -/
  | pushFront (r : Fin R) (b : Bool)
  deriving DecidableEq

namespace Instr
variable {R : ℕ}

/-- Precondition: `append` needs distinct registers. -/
def pre : Instr R → Regs R → Prop
  | .append dst src, _ => dst ≠ src
  | _, _ => True

/-- Effect of a basic instruction. -/
def eval : Instr R → Regs R → Regs R × Bool
  | .clear r, s => (Function.update s r [], true)
  | .pushBack r b, s => (Function.update s r (s r ++ [b]), true)
  | .popFront r, s => (Function.update s r (s r).tail, true)
  | .append dst src, s => (Function.update s dst (s dst ++ s src), true)
  | .isEmpty r, s => (s, decide (s r = []))
  | .headIs r b, s => (s, decide ((s r).head? = some b))
  | .const b, s => (s, b)
  | .pushFront r b, s => (Function.update s r (b :: s r), true)

/-- Abstract cost: one plus the lengths of the touched registers (pre-state). -/
def cost : Instr R → Regs R → ℕ
  | .clear r, s => 1 + (s r).length
  | .pushBack r _, s => 1 + (s r).length
  | .popFront r, s => 1 + (s r).length
  | .append dst src, s => 1 + (s dst).length + (s src).length
  | .isEmpty _, _ => 1
  | .headIs _ _, _ => 1
  | .const _, _ => 1
  | .pushFront r _, s => 1 + (s r).length

end Instr

/-- Semantics of the basic instruction set. -/
def basicSem (R : ℕ) : PrimSem (Instr R) (Regs R) :=
  ⟨Instr.pre, Instr.eval, Instr.cost⟩

/-- Space invariant: every register has length at most `S`. -/
def Fits {R : ℕ} (S : ℕ) (s : Regs R) : Prop := ∀ r, (s r).length ≤ S

/-- Initial register file: input in register `0`, all other registers empty. -/
def inputRegs {R : ℕ} (bits : List Bool) : Regs (R + 1) :=
  fun r => if r = 0 then bits else []

end QecReliability.RegMachine
