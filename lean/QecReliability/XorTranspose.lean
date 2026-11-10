import QecReliability.XorCircuitCore
import QecReliability.TransposeAccumulator

/-! Constructive reverse accumulation for acyclic XOR/zero circuits. Arbitrary
fan-out and repeated output wires are allowed and charged per use. -/
namespace QecReliability.SharedCircuit
open CodeHash
open scoped BigOperators

theorem bitsVector_snoc {v : ℕ} (a : BitModels v) (b : Bool) :
    bitsVector (Fin.snoc a b) = Fin.snoc (bitsVector a) (boolBit b) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [bitsVector]

theorem pair_snoc {v : ℕ} (a : Word (v + 1)) (b : Word v) (c : F) :
    pair a (Fin.snoc b c) = pair (fun i => a i.castSucc) b + a (Fin.last v) * c := by
  simp only [pair, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

def reverseXor {n v : ℕ} (P : Program n (v + 1)) (x y : Fin v) : Program n v :=
  ((P.addOutput x.castSucc (Fin.last v)).addOutput y.castSucc (Fin.last v)).select Fin.castSucc

theorem reverseXor_value {n v : ℕ} (P : Program n (v + 1)) (x y : Fin v) (a : BitModels n) :
    bitsVector ((reverseXor P x y).eval a) =
      (fun i => bitsVector (P.eval a) i.castSucc) +
        Pi.single x (bitsVector (P.eval a) (Fin.last v)) +
        Pi.single y (bitsVector (P.eval a) (Fin.last v)) := by
  change (fun i : Fin v => bitsVector (((P.addOutput x.castSucc (Fin.last v)).addOutput
      y.castSucc (Fin.last v)).eval a) i.castSucc) = _
  simp_rw [Program.addOutput_value]
  funext i
  simp [Pi.single_apply]

theorem reverseXor_pair {n v : ℕ} (P : Program n (v + 1)) (x y : Fin v)
    (a : BitModels n) (b : Word v) :
    pair (bitsVector ((reverseXor P x y).eval a)) b =
      pair (bitsVector (P.eval a)) (Fin.snoc b (b x + b y)) := by
  rw [reverseXor_value, pair_add_left, pair_add_left, pair_single_left, pair_single_left]
  simp only [pair, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

namespace XorCircuit

def reverse {n m : ℕ} : {g : ℕ} → (C : XorCircuit n g) → Program m (n + g) → Program m n
  | _, nil, P => P
  | _, zero C, P => C.reverse (P.select Fin.castSucc)
  | _, xor C x y, P => C.reverse (reverseXor P x y)

theorem reverse_gates {n m g : ℕ} (C : XorCircuit n g) (P : Program m (n + g)) :
    (C.reverse P).gates = P.gates + C.toCircuit.edges := by
  induction C with
  | nil => simp [reverse, toCircuit, Circuit.edges]
  | zero C ih => simp [reverse, ih, Program.select, toCircuit, Circuit.edges, Gate.arity]
  | xor C x y ih =>
    simp [reverse, ih, reverseXor, Program.select, Program.addOutput, Program.addWire,
      toCircuit, Circuit.edges, Gate.arity]
    omega

theorem reverse_edges {n m g : ℕ} (C : XorCircuit n g) (P : Program m (n + g)) :
    (C.reverse P).circuit.edges = P.circuit.edges + 2 * C.toCircuit.edges := by
  induction C with
  | nil => simp [reverse, toCircuit, Circuit.edges]
  | zero C ih => simp [reverse, ih, Program.select, toCircuit, Circuit.edges, Gate.arity]
  | xor C x y ih =>
    simp [reverse, ih, reverseXor, Program.select, Program.addOutput, Program.addWire,
      toCircuit, Circuit.edges, Gate.arity]
    omega

theorem reverse_pair {n m g : ℕ} (C : XorCircuit n g) (P : Program m (n + g))
    (a : BitModels m) (b : BitModels n) :
    pair (bitsVector ((C.reverse P).eval a)) (bitsVector b) =
      pair (bitsVector (P.eval a)) (bitsVector (C.toCircuit.run b)) := by
  induction C with
  | nil => rfl
  | zero C ih =>
    rw [reverse, ih]
    change pair (fun i => bitsVector (P.eval a) i.castSucc) (bitsVector (C.toCircuit.run b)) =
      pair (bitsVector (P.eval a)) (bitsVector (Fin.snoc (C.toCircuit.run b) false))
    rw [bitsVector_snoc]
    simpa [boolBit] using (pair_snoc (bitsVector (P.eval a))
      (bitsVector (C.toCircuit.run b)) 0).symm
  | xor C x y ih =>
    rw [reverse, ih, reverseXor_pair]
    change _ = pair (bitsVector (P.eval a))
      (bitsVector (Fin.snoc (C.toCircuit.run b) (Bool.xor (C.toCircuit.run b x) (C.toCircuit.run b y))))
    rw [bitsVector_snoc, boolBit_xor]
    rfl

end XorCircuit

namespace XorProgram

def transposed {n m : ℕ} (P : XorProgram n m) : Program m n :=
  P.circuit.reverse (scatter P.output)

/-- One zero source, one accumulation per output use, and one per gate-input edge. -/
theorem transposed_gates {n m : ℕ} (P : XorProgram n m) :
    P.transposed.gates = 1 + m + P.circuit.toCircuit.edges := by
  rw [transposed, XorCircuit.reverse_gates, scatter_gates]

theorem transposed_edges {n m : ℕ} (P : XorProgram n m) :
    P.transposed.circuit.edges = 2 * (m + P.circuit.toCircuit.edges) := by
  rw [transposed, XorCircuit.reverse_edges, scatter_edges]
  omega

theorem transposed_gates_le {n m : ℕ} (P : XorProgram n m) :
    P.transposed.gates ≤ 1 + m + 2 * P.gates := by
  rw [transposed_gates]
  exact Nat.add_le_add_left P.circuit.toCircuit.edges_le _

/-- All incoming gate edges, primary input sources and output sinks are included. -/
theorem transposed_resources {n m : ℕ} (P : XorProgram n m) :
    m + P.transposed.circuit.edges + n ≤ n + 3 * m + 4 * P.gates + 2 := by
  have h := P.transposed.circuit.edges_le
  have hg := P.transposed_gates_le
  omega

/-- An explicit combined size: input sources, output sinks, all gate nodes
(including the shared zero), and every incoming gate edge. -/
theorem transposed_total_size {n m : ℕ} (P : XorProgram n m) :
    m + n + P.transposed.gates + P.transposed.circuit.edges ≤ n + 4 * m + 6 * P.gates + 1 := by
  have hg := P.transposed_gates
  have he := P.transposed_edges
  have h := P.circuit.toCircuit.edges_le
  omega

theorem transposed_pair {n m : ℕ} (P : XorProgram n m) (a : BitModels m) (b : BitModels n) :
    pair (bitsVector (P.transposed.eval a)) (bitsVector b) =
      pair (bitsVector a) (bitsVector (P.toProgram.eval b)) := by
  rw [transposed, XorCircuit.reverse_pair, scatter_pair]
  rfl

/-- The generated extractor computes the semantic transpose of any linear map
computed by the supplied source DAG. No transpose-circuit premise is assumed. -/
theorem transposed_correct {n m : ℕ} (P : XorProgram n m)
    (G : Word n →ₗ[F] Word m)
    (hG : ∀ b j, boolBit (P.toProgram.eval b j) = G (bitsVector b) j)
    (a : BitModels m) (j : Fin n) :
    boolBit (P.transposed.eval a j) = transpose G (bitsVector a) j := by
  let b := wordBits n (Pi.single j 1)
  have hb : bitsVector b = Pi.single j 1 := by
    funext i
    exact BadEncoding.boolBit_bitBool _
  have h := P.transposed_pair a b
  rw [hb, pair_single_right] at h
  rw [transpose_apply]
  calc
    _ = _ := h
    _ = _ := by
      unfold pair bitsVector
      apply Finset.sum_congr rfl
      intro i _
      rw [hG, hb]

end XorProgram
end QecReliability.SharedCircuit
