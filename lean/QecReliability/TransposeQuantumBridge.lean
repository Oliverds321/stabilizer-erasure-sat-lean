import QecReliability.XorTranspose
import QecReliability.XorCircuitInput
import QecReliability.CodingHashBridge

/-! A supplied forward XOR encoder now constructs the extractor used by the
actual quantum queries. There is no supplied transpose-circuit field. -/
noncomputable section
namespace QecReliability.CodeHash
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

structure ForwardCodingCircuits {A : Type*} {q : ℕ} (P : CodingData A q) (e : A ≃ BitModels q) where
  symbols : Program q (P.M * P.t)
  symbols_correct : ∀ a i j,
    boolBit (symbols.eval (e a) (finProdFinEquiv (i, j))) = P.encode a i j
  code : Program P.k P.L
  code_xor : code.circuit.xorOnly = true
  code_correct : ∀ b j, boolBit (code.eval b j) = P.code (bitsVector b) j

def ForwardCodingCircuits.compiled {A : Type*} {q : ℕ} {P : CodingData A q}
    {e : A ≃ BitModels q} (K : ForwardCodingCircuits P e) : CodingCircuits P e where
  encoder := K.symbols
  encoder_correct := K.symbols_correct
  extractor := (K.code.asXor K.code_xor).transposed
  extractor_correct a j := (K.code.asXor K.code_xor).transposed_correct P.code
    (by intro b i; simpa only [Program.asXor_toProgram] using K.code_correct b i) a j

def ForwardCodingCircuits.hashGateBudget {A : Type*} {q : ℕ} {P : CodingData A q}
    {e : A ≃ BitModels q} (K : ForwardCodingCircuits P e) : ℕ :=
  K.symbols.gates + P.L * (P.t + 1) + (1 + P.L + 2 * K.code.gates)

theorem ForwardCodingCircuits.hash_gates {A : Type*} {q : ℕ} {P : CodingData A q}
    {e : A ≃ BitModels q} (K : ForwardCodingCircuits P e)
    (s : Fin (q + 1)) (ω : Seed P.L P.t) :
    (K.compiled.implementation.program s ω).gates ≤ K.hashGateBudget := by
  have h := K.compiled.gate_bound s ω
  have ht := (K.code.asXor K.code_xor).transposed_gates_le
  dsimp only [ForwardCodingCircuits.compiled, Program.asXor] at h ht
  unfold ForwardCodingCircuits.hashGateBudget
  dsimp only [ForwardCodingCircuits.compiled, Program.asXor]
  omega

theorem transposed_quantum_query_size {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (P : CodingData (Binary.CoefficientKey n r) (keySize n r))
    (K : ForwardCodingCircuits P (keyBits n r)) (i : Binary.CoefficientIndex r)
    (s : Fin (keySize n r + 1)) (ω : Seed P.L P.t) (pre : List Bool) :
    PrefixCNF.Width 3 (PrefixCNF.restrict
      (quantumCell rows C i (K.compiled.implementation.program s ω) (fun _ => false)).projectedFormula pre) ∧
    (PrefixCNF.restrict (quantumCell rows C i (K.compiled.implementation.program s ω)
      (fun _ => false)).projectedFormula pre).length ≤
      18 * rowIncidences rows + 22 * n + 83 * r + 4 * C.gates + 4 * K.hashGateBudget + 53 ∧
    keySize n r + (quantumWitness rows i.1 + (quantumCell rows C i
      (K.compiled.implementation.program s ω) (fun _ => false)).aux) ≤
      21 * r + 8 * n + 4 * rowIncidences rows + C.gates + K.hashGateBudget + 12 := by
  have h := query_size rows C P.system.stages K.compiled.implementation.supplied i s ω pre
  have hg := K.hash_gates s ω
  dsimp only [Implementation.supplied] at h
  exact ⟨h.1, by omega, by omega⟩

theorem transposed_coding_quantum_confidence {n r : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (C : Program r n) (P : CodingData (Binary.CoefficientKey n r) (keySize n r))
    (K : ForwardCodingCircuits P (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1 - δ ≤ (repeatedLaw (uniformLaw (Seed P.L P.t))
      (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ)).prob
      (fun ω =>
        let T := prepare rows C P.system.stages K.compiled.implementation.supplied solver (cellBudget (ε / 3))
          (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ) ω
        T.calls ≤ 2 * (r + 1) *
          (2 * repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ + 1) *
          (1 + (keySize n r + 1) * (1 + 2 * keySize n r * (4 * cellBudget (ε / 3) + 1))) ∧
        ∀ p ∈ Set.Icc (0 : ℝ) 1,
          RelPair ε (latentCurve (circuitMap C) (Binary.score (rowSpace rows)) p) (T.curve p) ∧
          0 ≤ T.curve p ∧ T.curve p ≤ 1) := by
  exact coding_quantum_confidence rows hS C P K.compiled solver hε hε1 hδ

end QecReliability.CodeHash
