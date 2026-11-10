import QecReliability.RecursiveEncoderDistanceCandidate

/-!


An actual typed finite zero/XOR emitter. Each row emits exactly one XOR per
column in ascending column order; rows are emitted in ascending row order.
A false matrix coefficient will later be represented by the shared zero wire,
not by skipping a gate or computing a support count. This deterministic choice
still gives the exact required linear gate bounds. All raw gates/output
references are materialized by the existing `XorProgram.serialize` operation.
The semantic proofs below derive correctness; no emitter-correctness premise.
-/

set_option autoImplicit false
namespace QecReliability.SharedCircuit.FiniteXorRowEmitter
open scoped BigOperators
open CodeHash EncoderSemantics

/-- Retain primary inputs while emitting two supplied blocks once each. -/
def parallel {n k l : Nat} (P : XorProgram n k) (Q : XorProgram n l) :
    XorProgram n (k + l) :=
  P.keepFollow (Q.rewire (Fin.castAdd P.gates))

@[simp] theorem parallel_gates {n k l : Nat} (P : XorProgram n k) (Q : XorProgram n l) :
    (parallel P Q).gates = P.gates + Q.gates := rfl

theorem parallel_eval {n k l : Nat} (P : XorProgram n k) (Q : XorProgram n l)
    (x : BitModels n) :
    (parallel P Q).toProgram.eval x = Fin.append (P.toProgram.eval x) (Q.toProgram.eval x) := by
  rw [parallel, XorProgram.keepFollow_eval, XorProgram.rewire_toProgram, Program.rewire_eval]
  have hp : P.circuit.toCircuit.run x ∘ Fin.castAdd P.gates = x := by
    funext i
    exact Circuit.run_primary _ _ _
  rw [hp]

theorem parallel_linear {n k l : Nat} (P : XorProgram n k) (Q : XorProgram n l)
    (x : Word n) :
    (parallel P Q).toLinear x = Fin.append (P.toLinear x) (Q.toLinear x) := by
  rw [XorProgram.toLinear_wordBits, parallel_eval, bitsVector_append]
  simp only [← XorProgram.toLinear_bool, bitsVector_wordBits]

/-- Exact field semantics of retained outputs, inherited from Boolean wiring. -/
theorem keepFollow_linear {n k l : Nat} (P : XorProgram n k)
    (Q : XorProgram (n + P.gates) l) (x : Word n) :
    (P.keepFollow Q).toLinear x =
      Fin.append (P.toLinear x) (Q.toLinear (P.circuit.fieldRun x)) := by
  rw [XorProgram.toLinear_wordBits, XorProgram.keepFollow_eval, bitsVector_append]
  simp only [← XorProgram.toLinear_bool, ← XorCircuit.fieldRun_bool, bitsVector_wordBits]

/-- Appended gates never alter a primary input wire. -/
theorem fieldRun_primary {n g : Nat} (C : XorCircuit n g) (x : Word n) (i : Fin n) :
    C.fieldRun x (Fin.castAdd g i) = x i := by
  induction C with
  | nil => rfl
  | zero C ih =>
    change Fin.snoc (α := fun _ => F) (C.fieldRun x) 0 (Fin.castSucc (Fin.castAdd _ i)) = x i
    rw [Fin.snoc_castSucc]
    exact ih
  | xor C a b ih =>
    change Fin.snoc (α := fun _ => F) (C.fieldRun x) (C.fieldRun x a + C.fieldRun x b)
      (Fin.castSucc (Fin.castAdd _ i)) = x i
    rw [Fin.snoc_castSucc]
    exact ih

/-- Start at the supplied primary zero reference, then append columns in order.
The zero-value hypothesis is not needed to DEFINE this finite program. -/
def row {n : Nat} (zero : Fin n) :
    (columns : Nat) → (Fin columns → Fin n) → XorProgram n 1
  | 0, _ => ⟨0, .nil, fun _ => zero⟩
  | c + 1, refs =>
      let P := row zero c (fun i => refs i.castSucc)
      { gates := P.gates + 1
        circuit := .xor P.circuit (P.output 0) (Fin.castAdd P.gates (refs (Fin.last c)))
        output := fun _ => Fin.last (n + P.gates) }

@[simp] theorem row_gates {n : Nat} (zero : Fin n) (c : Nat) (refs : Fin c → Fin n) :
    (row zero c refs).gates = c := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [row, ih]

theorem row_value {n : Nat} (zero : Fin n) (c : Nat) (refs : Fin c → Fin n)
    (x : Word n) :
    (row zero c refs).toLinear x 0 = x zero + ∑ j : Fin c, x (refs j) := by
  induction c with
  | zero => simp [row, XorProgram.toLinear, XorCircuit.fieldRun]
  | succ c ih =>
    let P := row zero c (fun i => refs i.castSucc)
    change Fin.snoc (α := fun _ => F) (P.circuit.fieldRun x)
      (P.circuit.fieldRun x (P.output 0) +
        P.circuit.fieldRun x (Fin.castAdd P.gates (refs (Fin.last c))))
      (Fin.last (n + P.gates)) = _
    rw [Fin.snoc_last, fieldRun_primary]
    change P.toLinear x 0 + x (refs (Fin.last c)) = _
    rw [ih, Fin.sum_univ_castSucc]
    exact add_assoc _ _ _

/-- A finite rectangular reference table; each row shares the primary inputs.
The empty row family emits no gates and has no output references. -/
def rows {n : Nat} (zero : Fin n) (c : Nat) :
    (m : Nat) → (Fin m → Fin c → Fin n) → XorProgram n m
  | 0, _ => ⟨0, .nil, Fin.elim0⟩
  | m + 1, refs => parallel
      (rows zero c m (fun i => refs i.castSucc))
      (row zero c (refs (Fin.last m)))

@[simp] theorem rows_gates {n : Nat} (zero : Fin n) (c m : Nat)
    (refs : Fin m → Fin c → Fin n) :
    (rows zero c m refs).gates = m * c := by
  induction m with
  | zero => simp [rows]
  | succ m ih => simp only [rows, parallel_gates, ih, row_gates, Nat.succ_mul]

theorem rows_value {n : Nat} (zero : Fin n) (c m : Nat)
    (refs : Fin m → Fin c → Fin n) (x : Word n) (i : Fin m) :
    (rows zero c m refs).toLinear x i = x zero + ∑ j : Fin c, x (refs i j) := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    rw [rows, parallel_linear]
    refine Fin.lastCases ?_ (fun r => ?_) i
    · change Fin.append _ _ (Fin.natAdd m (0 : Fin 1)) = _
      rw [Fin.append_right]
      exact row_value zero c (refs (Fin.last m)) x
    · change Fin.append _ _ (Fin.castAdd 1 r) = _
      rw [Fin.append_left]
      exact ih (fun i => refs i.castSucc) r

/-- The only zero gate in the entire rectangular emitter. -/
def seedZero (n : Nat) : XorProgram n 1 :=
  ⟨1, .zero .nil, fun _ => Fin.last n⟩

/-- Output zero first, then the m row sums. Retention is wiring, not a gate. -/
def emitKeepZero (n m c : Nat) (refs : Fin m → Fin c → Fin (n + 1)) :
    XorProgram n (1 + m) :=
  (seedZero n).keepFollow (rows (Fin.last n) c m refs)

@[simp] theorem emitKeepZero_gates (n m c : Nat)
    (refs : Fin m → Fin c → Fin (n + 1)) :
    (emitKeepZero n m c refs).gates = 1 + m * c := by
  change 1 + (rows (Fin.last n) c m refs).gates = _
  rw [rows_gates]

theorem emitKeepZero_linear (n m c : Nat)
    (refs : Fin m → Fin c → Fin (n + 1)) (x : Word n) :
    (emitKeepZero n m c refs).toLinear x =
      Fin.append (fun _ : Fin 1 => (0 : F))
        (fun i => ∑ j : Fin c, Fin.snoc (α := fun _ => F) x 0 (refs i j)) := by
  rw [emitKeepZero, keepFollow_linear]
  apply congrArg₂ Fin.append
  · funext i
    simp [seedZero, XorProgram.toLinear, XorCircuit.fieldRun]
  · funext i
    have hz : (seedZero n).circuit.fieldRun x (Fin.last n) = 0 := by
      exact Fin.snoc_last (n := n) (α := fun _ => F) 0 x
    rw [rows_value, hz, zero_add]
    rfl

/-- The serialized output table contains literal references, not closures. -/
theorem emitKeepZero_serialized (n m c : Nat)
    (refs : Fin m → Fin c → Fin (n + 1)) :
    (emitKeepZero n m c refs).serialize.Valid ∧
    (emitKeepZero n m c refs).serialize.gates.length = 1 + m * c ∧
    (emitKeepZero n m c refs).serialize.outputs.length = 1 + m := by
  refine ⟨⟨XorProgram.serialize_topological _, ?_⟩, ?_, ?_⟩
  · intro v hv
    have h := XorProgram.serialize_output_bound (emitKeepZero n m c refs) v hv
    simpa only [XorProgram.serialize, XorCircuit.erase_length] using h
  · simp only [XorProgram.serialize, XorCircuit.erase_length, emitKeepZero_gates]
  · simp only [XorProgram.serialize, List.length_ofFn]

end QecReliability.SharedCircuit.FiniteXorRowEmitter
