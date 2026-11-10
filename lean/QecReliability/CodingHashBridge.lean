import QecReliability.DyadicAlignment

/-! Coding parameters, whole-symbol alignment and supplied DAGs instantiate the
quantum hash interface without assuming any surjectivity or probability field. -/
noncomputable section
namespace QecReliability.CodeHash
open SharedCircuit

structure CodingData (A : Type*) (q : ℕ) where
  M : ℕ
  L : ℕ
  t : ℕ
  k : ℕ
  positive : 0 < M
  length_ge : M ≤ L
  length_le : L ≤ 2 * M
  capacity : q ≤ k
  α : ℝ
  alpha_pos : 0 < α
  encode : A → Fin M → Word t
  separation : ∀ x y, x ≠ y → (agreements (encode x) (encode y) : ℝ) < α * M / 4
  code : Word k →ₗ[F] Word L
  distance : ∀ a, a ≠ 0 → α * L ≤ (weight (code a) : ℝ)

def CodingData.system {A : Type*} {q : ℕ} (P : CodingData A q) : System A P.L P.t q :=
  (alignedSystem P.positive P.length_ge P.length_le P.α P.alpha_pos
    P.encode P.separation P.code P.distance).prefix P.capacity

structure CodingCircuits {A : Type*} {q : ℕ} (P : CodingData A q) (e : A ≃ BitModels q) where
  encoder : Program q (P.M * P.t)
  encoder_correct : ∀ a i j,
    boolBit (encoder.eval (e a) (finProdFinEquiv (i, j))) = P.encode a i j
  extractor : Program P.L P.k
  extractor_correct : ∀ a j,
    boolBit (extractor.eval a j) = transpose P.code (fun i => boolBit (a i)) j

def repeatWires (M L t : ℕ) (hM : 0 < M) : Fin (L * t) → Fin (M * t) :=
  fun x => finProdFinEquiv (cyclicRepeat M L hM (finProdFinEquiv.symm x).1,
    (finProdFinEquiv.symm x).2)

def CodingCircuits.implementation {A : Type*} {q : ℕ} {P : CodingData A q}
    {e : A ≃ BitModels q} (K : CodingCircuits P e) : Implementation P.system e where
  encoder := K.encoder.compose (Program.pure (repeatWires P.M P.L P.t P.positive))
  encoder_correct a i j := by
    simp only [Program.compose_eval, Program.pure_eval, Function.comp_apply]
    simp only [repeatWires, Equiv.symm_apply_apply]
    exact K.encoder_correct a _ j
  extractor := K.extractor.compose (Program.pure (Fin.castLE P.capacity))
  extractor_correct a j := by
    simp only [Program.compose_eval, Program.pure_eval, Function.comp_apply]
    exact K.extractor_correct a _

theorem CodingCircuits.gate_bound {A : Type*} {q : ℕ} {P : CodingData A q}
    {e : A ≃ BitModels q} (K : CodingCircuits P e) (r : Fin (q + 1)) (s : Seed P.L P.t) :
    (K.implementation.program r s).gates ≤ K.encoder.gates + P.L * (P.t + 1) + K.extractor.gates := by
  simpa [CodingCircuits.implementation, Program.compose, Program.pure] using K.implementation.program_gates r s

open SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- The final hash premise is now ordinary coding distance and symbol separation.
Small circuits, their existence and the exact SAT solver are still explicit inputs. -/
theorem coding_quantum_confidence {n r : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (C : Program r n) (P : CodingData (Binary.CoefficientKey n r) (keySize n r))
    (K : CodingCircuits P (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1 - δ ≤ (repeatedLaw (uniformLaw (Seed P.L P.t))
      (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ)).prob
      (fun ω =>
        let T := prepare rows C P.system.stages K.implementation.supplied solver (cellBudget (ε / 3))
          (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ) ω
        T.calls ≤ 2 * (r + 1) *
          (2 * repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ + 1) *
          (1 + (keySize n r + 1) * (1 + 2 * keySize n r * (4 * cellBudget (ε / 3) + 1))) ∧
        ∀ p ∈ Set.Icc (0 : ℝ) 1,
          RelPair ε (latentCurve (circuitMap C) (Binary.score (rowSpace rows)) p) (T.curve p) ∧
          0 ≤ T.curve p ∧ T.curve p ≤ 1) := by
  exact cached_quantum_confidence rows hS C P.system K.implementation solver hε hε1 hδ

end QecReliability.CodeHash
