import QecReliability.BitModelsCore
import Mathlib.Data.Fin.Tuple.Basic

namespace QecReliability
namespace SharedCircuit

inductive Gate (v : ℕ) where
  | andGate : Fin v → Fin v → Gate v
  | xorGate : Fin v → Fin v → Gate v
  | notGate : Fin v → Gate v
  | constGate : Bool → Gate v
  deriving DecidableEq

namespace Gate

def eval {v : ℕ} : Gate v → BitModels v → Bool
  | andGate x y, a => a x && a y
  | xorGate x y, a => xor (a x) (a y)
  | notGate x, a => !(a x)
  | constGate b, _ => b

def arity {v : ℕ} : Gate v → ℕ
  | andGate _ _ => 2
  | xorGate _ _ => 2
  | notGate _ => 1
  | constGate _ => 0

def map {v w : ℕ} (f : Fin v → Fin w) : Gate v → Gate w
  | andGate x y => andGate (f x) (f y)
  | xorGate x y => xorGate (f x) (f y)
  | notGate x => notGate (f x)
  | constGate b => constGate b

theorem eval_map {v w : ℕ} (f : Fin v → Fin w) (g : Gate v) (a : BitModels w) :
    (g.map f).eval a = g.eval (fun i => a (f i)) := by cases g <;> rfl

theorem arity_le_two {v : ℕ} (g : Gate v) : g.arity ≤ 2 := by cases g <;> simp [arity]

end Gate

/-- `n` primary wires, then exactly `g` gate-output wires in topological order. -/
inductive Circuit (n : ℕ) : ℕ → Type where
  | nil : Circuit n 0
  | snoc {g : ℕ} : Circuit n g → Gate (n + g) → Circuit n (g + 1)

namespace Circuit

def run {n : ℕ} : {g : ℕ} → Circuit n g → BitModels n → BitModels (n + g)
  | _, nil, a => a
  | _, snoc C gate, a =>
      let values := C.run a
      Fin.snoc values (gate.eval values)

def edges {n : ℕ} : {g : ℕ} → Circuit n g → ℕ
  | _, nil => 0
  | _, snoc C gate => C.edges + gate.arity

theorem edges_le {n g : ℕ} (C : Circuit n g) : C.edges ≤ 2 * g := by
  induction C with
  | nil => simp [edges]
  | snoc C gate ih => have h := gate.arity_le_two; simp only [edges]; omega

def inputs {n g : ℕ} (v : BitModels (n + g)) : BitModels n := fun i => v (Fin.castAdd g i)

@[simp] theorem run_inputs {n g : ℕ} (C : Circuit n g) (a : BitModels n) :
    inputs (C.run a) = a := by
  funext i
  induction C with
  | nil => rfl
  | @snoc g C gate ih =>
    change Fin.snoc (n := n + g) (α := fun _ => Bool) (C.run a) (gate.eval (C.run a)) (Fin.castSucc (Fin.castAdd g i)) = a i
    rw [Fin.snoc_castSucc]
    exact ih

theorem run_primary {n g : ℕ} (C : Circuit n g) (a : BitModels n) (i : Fin n) :
    C.run a (Fin.castAdd g i) = a i := congrFun (run_inputs C a) i

theorem snoc_output {n g : ℕ} (C : Circuit n g) (gate : Gate (n + g)) (a : BitModels n) :
    (C.snoc gate).run a (Fin.last (n + g)) = gate.eval (C.run a) := by
  change Fin.snoc (n := n + g) (α := fun _ => Bool) (C.run a) (gate.eval (C.run a))
    (Fin.last (n + g)) = gate.eval (C.run a)
  exact Fin.snoc_last (n := n + g) (α := fun _ => Bool) (gate.eval (C.run a)) (C.run a)

theorem snoc_old {n g : ℕ} (C : Circuit n g) (gate : Gate (n + g)) (a : BitModels n)
    (i : Fin (n + g)) : (C.snoc gate).run a i.castSucc = C.run a i := by
  change Fin.snoc (n := n + g) (α := fun _ => Bool) (C.run a) (gate.eval (C.run a)) i.castSucc = _
  exact Fin.snoc_castSucc (n := n + g) (α := fun _ => Bool) (gate.eval (C.run a)) (C.run a) i

end Circuit
end SharedCircuit
end QecReliability
