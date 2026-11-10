import QecReliability.CircuitCompiler
import QecReliability.BinarySymplectic
import Mathlib.Algebra.BigOperators.Fin

/-! Linear-size parity and parity-of-products shared circuits, plus support clauses.
These are concrete quantum-certificate components, not yet a complete Good/Bad compiler. -/

namespace QecReliability.SharedCircuit
open PrefixCNF
open scoped BigOperators

def parityValue {v : ℕ} (a : BitModels v) : List (Fin v) → Bool
  | [] => false
  | x :: xs => xor (a x) (parityValue a xs)

def parityCircuit {v : ℕ} : (xs : List (Fin v)) → Circuit v (xs.length + 1)
  | [] => Circuit.nil.snoc (Gate.constGate false)
  | x :: xs => (parityCircuit xs).snoc
      (Gate.xorGate (Fin.castAdd (xs.length + 1) x) (Fin.last (v + xs.length)))

theorem parityCircuit_correct {v : ℕ} (xs : List (Fin v)) (a : BitModels v) :
    (parityCircuit xs).run a (Fin.last (v + xs.length)) = parityValue a xs := by
  induction xs with
  | nil => exact Circuit.snoc_output _ _ _
  | cons x xs ih =>
    rw [parityCircuit]
    simp only [List.length_cons]
    rw [Circuit.snoc_output (parityCircuit xs)]
    change xor ((parityCircuit xs).run a (Fin.castAdd (xs.length + 1) x))
      ((parityCircuit xs).run a (Fin.last (v + xs.length))) = xor (a x) (parityValue a xs)
    rw [Circuit.run_primary, ih]

def productParityValue {v : ℕ} (a : BitModels v) : List (Fin v × Fin v) → Bool
  | [] => false
  | (x, y) :: xs => xor (a x && a y) (productParityValue a xs)

def productParityCircuit {v : ℕ} : (xs : List (Fin v × Fin v)) → Circuit v (2 * xs.length + 1)
  | [] => Circuit.nil.snoc (Gate.constGate false)
  | (x, y) :: xs =>
      ((productParityCircuit xs).snoc
        (Gate.andGate (Fin.castAdd (2 * xs.length + 1) x) (Fin.castAdd (2 * xs.length + 1) y))).snoc
        (Gate.xorGate (Fin.last (v + (2 * xs.length + 1)))
          (Fin.castSucc (Fin.last (v + 2 * xs.length))))

theorem productParityCircuit_correct {v : ℕ} (xs : List (Fin v × Fin v)) (a : BitModels v) :
    (productParityCircuit xs).run a (Fin.last (v + 2 * xs.length)) = productParityValue a xs := by
  induction xs with
  | nil => exact Circuit.snoc_output _ _ _
  | cons xy xs ih =>
    obtain ⟨x, y⟩ := xy
    rw [productParityCircuit]
    simp only [List.length_cons, Nat.mul_succ]
    rw [Circuit.snoc_output ((productParityCircuit xs).snoc
      (Gate.andGate (Fin.castAdd (2 * xs.length + 1) x) (Fin.castAdd (2 * xs.length + 1) y)))]
    change xor (_ ) (_) = _
    rw [Circuit.snoc_output (productParityCircuit xs), Circuit.snoc_old]
    change xor (((productParityCircuit xs).run a (Fin.castAdd (2 * xs.length + 1) x)) &&
      ((productParityCircuit xs).run a (Fin.castAdd (2 * xs.length + 1) y)))
      ((productParityCircuit xs).run a (Fin.last (v + 2 * xs.length))) = _
    rw [Circuit.run_primary, Circuit.run_primary, ih]
    rfl

def boolBit (b : Bool) : Binary.Bit := if b then 1 else 0

theorem boolBit_xor (a b : Bool) : boolBit (xor a b) = boolBit a + boolBit b := by
  cases a <;> cases b <;> decide

theorem boolBit_and (a b : Bool) : boolBit (a && b) = boolBit a * boolBit b := by
  cases a <;> cases b <;> decide

@[simp] theorem boolBit_eq_zero (a : Bool) : boolBit a = 0 ↔ a = false := by cases a <;> decide
@[simp] theorem boolBit_eq_one (a : Bool) : boolBit a = 1 ↔ a = true := by cases a <;> decide

theorem parityValue_sum {v : ℕ} (a : BitModels v) (xs : List (Fin v)) :
    boolBit (parityValue a xs) = (xs.map (fun i => boolBit (a i))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [parityValue, boolBit_xor, ih, List.map_cons, List.sum_cons]

theorem productParityValue_sum {v : ℕ} (a : BitModels v) (xs : List (Fin v × Fin v)) :
    boolBit (productParityValue a xs) = (xs.map (fun xy => boolBit (a xy.1) * boolBit (a xy.2))).sum := by
  induction xs with
  | nil => rfl
  | cons xy xs ih =>
    obtain ⟨x,y⟩ := xy
    simp only [productParityValue, boolBit_xor, boolBit_and, ih, List.map_cons, List.sum_cons]

/-- Input incidence lists may be empty or contain repeated indices; repeated F₂ terms cancel. -/
theorem parity_zero_iff {v : ℕ} (xs : List (Fin v)) (a : BitModels v) :
    (parityCircuit xs).run a (Fin.last (v + xs.length)) = false ↔
      (xs.map (fun i => boolBit (a i))).sum = 0 := by
  rw [parityCircuit_correct, ← parityValue_sum, boolBit_eq_zero]

def incidences {v : ℕ} (rows : List (List (Fin v))) : ℕ := (rows.map List.length).sum

def nonemptyRows {v : ℕ} (rows : List (List (Fin v))) : List (List (Fin v)) :=
  rows.filter (fun row => !row.isEmpty)

theorem nonemptyRows_constraints {v : ℕ} (rows : List (List (Fin v))) (a : BitModels v) :
    (∀ row ∈ nonemptyRows rows, parityValue a row = false) ↔
      ∀ row ∈ rows, parityValue a row = false := by
  constructor
  · intro h row hr
    cases row with
    | nil => rfl
    | cons x xs => exact h (x :: xs) (by simp [nonemptyRows, hr])
  · intro h row hr
    exact h row (List.mem_filter.mp hr).1

/-- Empty zero rows are discarded. The per-row parity blocks cost at most twice total incidence. -/
theorem parity_blocks_gate_bound {v : ℕ} (rows : List (List (Fin v))) :
    ((nonemptyRows rows).map (fun row => row.length + 1)).sum ≤ 2 * incidences rows := by
  induction rows with
  | nil => simp [nonemptyRows, incidences]
  | cons row rows ih =>
    cases row with
    | nil => simpa [nonemptyRows, incidences] using ih
    | cons x xs =>
      simp only [nonemptyRows, List.filter_cons, List.isEmpty_cons, Bool.not_false, ↓reduceIte,
        List.map_cons, List.sum_cons, List.length_cons, incidences] at *
      omega

/-- Direct support clauses are already width two and need no gate auxiliaries. -/
def supportClauses {v : ℕ} (pairs : List (Fin v × Fin v)) : Formula v :=
  pairs.map (fun xe => [(xe.1, false), (xe.2, true)])

theorem supportClauses_correct {v : ℕ} (pairs : List (Fin v × Fin v)) (a : BitModels v) :
    PrefixCNF.eval (supportClauses pairs) a = true ↔
      ∀ xe ∈ pairs, a xe.1 = true → a xe.2 = true := by
  simp only [supportClauses, PrefixCNF.eval, List.all_map, Function.comp_def, List.all_eq_true]
  apply forall_congr'
  intro xe
  apply imp_congr_right
  intro _
  cases hx : a xe.1 <;> cases he : a xe.2 <;> simp [evalClause, hx, he]

theorem supportClauses_width {v : ℕ} (pairs : List (Fin v × Fin v)) : Width 2 (supportClauses pairs) := by
  intro c hc
  obtain ⟨xe, _, rfl⟩ := List.mem_map.mp hc
  simp

theorem supportClauses_length {v : ℕ} (pairs : List (Fin v × Fin v)) :
    (supportClauses pairs).length = pairs.length := by simp [supportClauses]

end QecReliability.SharedCircuit
