import QecReliability.SparseGenerators

/-! Sparse row-wise reconstruction: one XOR per incidence, with shared coefficient wires. -/
namespace QecReliability.SharedCircuit

def coordValue {n : ℕ} (x : Binary.Pauli n) : PauliCoord n → Binary.Bit := Sum.elim x.1 x.2

theorem coordValue_injective (n : ℕ) : Function.Injective (@coordValue n) := by
  intro x y h
  exact Prod.ext (funext (fun i => congrFun h (.inl i))) (funext (fun i => congrFun h (.inr i)))

theorem coordValue_add {n : ℕ} (x y : Binary.Pauli n) (c : PauliCoord n) :
    coordValue (x + y) c = coordValue x c + coordValue y c := by cases c <;> rfl

theorem coordValue_smul {n : ℕ} (a : Binary.Bit) (x : Binary.Pauli n) (c : PauliCoord n) :
    coordValue (a • x) c = a * coordValue x c := by cases c <;> rfl

theorem coordValue_unit {n : ℕ} (c t : PauliCoord n) :
    coordValue (coordPauli c) t = if t = c then 1 else 0 := by
  cases c <;> cases t <;> simp [coordValue, coordPauli, Binary.xUnit, Binary.zUnit, Pi.single_apply, eq_comm]

structure Reconstruction (n v : ℕ) where
  gates : ℕ
  circuit : Circuit v gates
  output : PauliCoord n → Fin (v + gates)

namespace Reconstruction

def value {n v : ℕ} (R : Reconstruction n v) (a : BitModels v) : Binary.Pauli n :=
  wiredPauli (R.circuit.run a) (fun i => R.output (.inl i)) (fun i => R.output (.inr i))

theorem value_coord {n v : ℕ} (R : Reconstruction n v) (a : BitModels v) (c : PauliCoord n) :
    coordValue (R.value a) c = boolBit (R.circuit.run a (R.output c)) := by cases c <;> rfl

def zero (n v : ℕ) : Reconstruction n v :=
  ⟨1, Circuit.nil.snoc (.constGate false), fun _ => Fin.last v⟩

theorem zero_value (n v : ℕ) (a : BitModels v) : (zero n v).value a = 0 := by
  apply coordValue_injective n
  funext c
  rw [value_coord]
  have h := Circuit.snoc_output (Circuit.nil (n := v)) (.constGate false) a
  change boolBit ((Circuit.nil.snoc (.constGate false)).run a (Fin.last v)) = _
  exact (congrArg boolBit h).trans (by cases c <;> rfl)

def addIncidence {n v : ℕ} (R : Reconstruction n v) (c : PauliCoord n) (coeff : Fin v) : Reconstruction n v where
  gates := R.gates + 1
  circuit := R.circuit.snoc (.xorGate (R.output c) (Fin.castAdd R.gates coeff))
  output t := if t = c then Fin.last (v + R.gates) else (R.output t).castSucc

theorem addIncidence_value {n v : ℕ} (R : Reconstruction n v) (c : PauliCoord n)
    (coeff : Fin v) (a : BitModels v) :
    (R.addIncidence c coeff).value a = R.value a + boolBit (a coeff) • coordPauli c := by
  apply coordValue_injective n
  funext t
  rw [coordValue_add, coordValue_smul, coordValue_unit, value_coord, value_coord]
  by_cases ht : t = c
  · subst t
    simp only [addIncidence, ↓reduceIte]
    rw [Circuit.snoc_output]
    change boolBit (Bool.xor (R.circuit.run a (R.output c))
      (R.circuit.run a (Fin.castAdd R.gates coeff))) = _
    rw [Circuit.run_primary, boolBit_xor]
    simp
  · simp only [addIncidence, ht, ↓reduceIte, mul_zero, add_zero]
    rw [Circuit.snoc_old]

def addRow {n v : ℕ} (R : Reconstruction n v) (coeff : Fin v) : List (PauliCoord n) → Reconstruction n v
  | [] => R
  | c :: cs => (addRow R coeff cs).addIncidence c coeff

theorem addRow_gates {n v : ℕ} (R : Reconstruction n v) (coeff : Fin v) (row : List (PauliCoord n)) :
    (R.addRow coeff row).gates = R.gates + row.length := by
  induction row with
  | nil => rfl
  | cons c cs ih => simp [addRow, addIncidence, ih, Nat.add_assoc]

theorem addRow_value {n v : ℕ} (R : Reconstruction n v) (coeff : Fin v)
    (row : List (PauliCoord n)) (a : BitModels v) :
    (R.addRow coeff row).value a = R.value a + boolBit (a coeff) • decodeRow row := by
  induction row with
  | nil => simp [addRow, decodeRow]
  | cons c cs ih =>
    rw [addRow, addIncidence_value, ih]
    simp only [decodeRow, List.map_cons, List.sum_cons, smul_add]
    abel

def synthesize {n v : ℕ} : (rows : List (List (PauliCoord n))) → (Fin rows.length → Fin v) → Reconstruction n v
  | [], _ => zero n v
  | row :: rows, coeff => (synthesize rows (Fin.tail coeff)).addRow (coeff ⟨0, by simp⟩) row

theorem synthesize_gates {n v : ℕ} (rows : List (List (PauliCoord n))) (coeff : Fin rows.length → Fin v) :
    (synthesize rows coeff).gates = rowIncidences rows + 1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [synthesize, addRow_gates, ih]
    simp [rowIncidences]
    omega

theorem synthesize_value {n v : ℕ} (rows : List (List (PauliCoord n)))
    (coeff : Fin rows.length → Fin v) (a : BitModels v) :
    (synthesize rows coeff).value a = combination rows (fun i => boolBit (a (coeff i))) := by
  induction rows with
  | nil => rw [synthesize, zero_value]; simp [combination]
  | cons row rows ih =>
    rw [synthesize, addRow_value, ih, combination_cons]
    exact add_comm _ _

end Reconstruction
end QecReliability.SharedCircuit
