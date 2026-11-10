import TensorPhysicalVectorConfidence
import Final.OutputInjective

/-! Transfer the finite-coin physical guarantee to every output of the actual
deterministic machine, rather than only to a chosen source-level estimator. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape RationalOutput Final QecPhysical QecPhysical.Stabilizer

theorem outputs_unique_runs {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine k Γ Λ} {bits : List Bool} {o : Fin (k+1)} {r : ℕ}
    {a b : Completed M bits} {v w : Vector r}
    (ha : Outputs M a o v) (hb : Outputs M b o w) : v=w := by
  have hf := (Completed.unique a b).1
  have ha' : Outputs M b o v := by
    unfold Outputs at ha ⊢
    rw [← hf]
    exact ha
  exact ha'.unique hb

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
  (C : SharedCircuit.Program ds.sum n) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
  (a b c d : ℕ)

local notation "BB" => rationalCellBudget a b
local notation "MM" => rationalRepetitionBudget (2*slots ds) c d
local notation "NN" => CodeHash.repeatBits (Factory.length hD hd A n ds)
  (Factory.width hD hd A n ds) MM
local notation "VEC" => PhysicalAlgorithm.outputVector hD hd A rows C solver BB MM

theorem physical_output_transfer (lift : Lift (rowSpace rows))
    (hC : Monotone (TensorEncoding.circuitMap C))
    (ha : 0<a) (hab : a≤b) (hc : 0<c) (hd' : 0<d)
    {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    (M : Machine k Γ Λ) (o : Fin (k+1)) (encode : (Fin NN → Bool) → List Bool)
    (hrun : ∀ coins, ∃ run : Completed M (encode coins), Outputs M run o (VEC coins)) :
    (∀ coins (run : Completed M (encode coins)) (v : Vector (slots ds-1)),
      Outputs M run o v → lift.TensorPhysicalStructure (TensorEncoding.circuitMap C)
        (vectorCurve ds v)) ∧
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape NN)).prob
      (fun coins => ∀ (run : Completed M (encode coins)) (v : Vector (slots ds-1)),
        Outputs M run o v → lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C)
          ((a:ℝ)/b) (vectorCurve ds v)) := by
  obtain ⟨hshape,hprob⟩ := PhysicalAlgorithm.vector_confidence hD hd A rows C solver
    lift hC a b c d ha hab hc hd'
  constructor
  · intro coins run v hv
    obtain ⟨canonical,hcanonical⟩ := hrun coins
    have he := outputs_unique_runs hv hcanonical
    rw [he]
    exact hshape coins
  · apply hprob.trans
    apply FiniteProbability.prob_mono
    intro coins hgood run v hv
    obtain ⟨canonical,hcanonical⟩ := hrun coins
    have he := outputs_unique_runs hv hcanonical
    rw [he]
    exact hgood

end QecReliability.TensorMachine
