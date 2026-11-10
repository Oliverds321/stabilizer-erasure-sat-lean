import QecReliability.DenseHashReference

/-! The conditional code-based family composed with the actual quantum CNFs and
cached evaluator. The conditional linear-size claim and finite confidence are distinct. -/
noncomputable section
namespace QecReliability.CodeHash
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

theorem Implementation.program_linear {A : Type*} {m t q : ℕ} {D : System A m t q}
    {e : A ≃ BitModels q} (K : Implementation D e) (cE cL cX : ℕ)
    (hE : K.encoder.gates ≤ cE * q) (hL : m * (t + 1) ≤ cL * q)
    (hX : K.extractor.gates ≤ cX * q) (s : Fin (q + 1)) (ω : Seed m t) :
    (K.program s ω).gates ≤ (cE + cL + cX) * q := by
  have h := K.program_gates s ω
  nlinarith

theorem quantum_query_size {n r m t : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (D : System (Binary.CoefficientKey n r) m t (keySize n r))
    (K : Implementation D (keyBits n r)) (i : Binary.CoefficientIndex r)
    (s : Fin (keySize n r + 1)) (ω : Seed m t) (pre : List Bool) :
    PrefixCNF.Width 3 (PrefixCNF.restrict
      (quantumCell rows C i (K.program s ω) (fun _ => false)).projectedFormula pre) ∧
    (PrefixCNF.restrict (quantumCell rows C i (K.program s ω) (fun _ => false)).projectedFormula pre).length ≤
      18 * rowIncidences rows + 22 * n + 83 * r + 4 * C.gates +
        4 * (K.encoder.gates + m * (t + 1) + K.extractor.gates) + 53 ∧
    keySize n r + (quantumWitness rows i.1 + (quantumCell rows C i (K.program s ω) (fun _ => false)).aux) ≤
      21 * r + 8 * n + 4 * rowIncidences rows + C.gates +
        (K.encoder.gates + m * (t + 1) + K.extractor.gates) + 12 := by
  have h := query_size rows C D.stages K.supplied i s ω pre
  have hg := K.program_gates s ω
  change PrefixCNF.Width 3 _ ∧ _ ≤ _ ∧ _ ≤ _ at h
  exact ⟨h.1, by dsimp only [Implementation.supplied] at h; omega,
    by dsimp only [Implementation.supplied] at h; omega⟩

/-- Code assumptions imply the hash law; encoder/extractor DAGs imply the actual cell
CNFs. Confidence and decision calls concern one and the same materialized table. -/
theorem cached_quantum_confidence {n r m t : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (C : Program r n) (D : System (Binary.CoefficientKey n r) m t (keySize n r))
    (K : Implementation D (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1 - δ ≤ (repeatedLaw (uniformLaw (Seed m t))
      (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ)).prob
      (fun ω =>
        let T := prepare rows C D.stages K.supplied solver (cellBudget (ε / 3))
          (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ) ω
        T.calls ≤ 2 * (r + 1) *
          (2 * repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ + 1) *
          (1 + (keySize n r + 1) * (1 + 2 * keySize n r * (4 * cellBudget (ε / 3) + 1))) ∧
        ∀ p ∈ Set.Icc (0 : ℝ) 1,
          RelPair ε (latentCurve (circuitMap C) (Binary.score (rowSpace rows)) p) (T.curve p) ∧
          0 ≤ T.curve p ∧ T.curve p ≤ 1) := by
  exact cached_curve_confidence rows hS C D.stages K.supplied solver hε hε1 hδ

end QecReliability.CodeHash
