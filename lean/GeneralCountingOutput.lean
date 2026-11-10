import TensorCountingOutput
import GeneralRepairFL
import TensorGeneralAlgorithm
import TensorMachinePhysicalTransfer

/-! The two concrete forward count tables feed the general-circuit output
(corner replacement, no repair); the flat vector list; and the transfer of the
general physical guarantee to every output of a deterministic machine. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace QecReliability.TensorMachine.GeneralBoundary
open SharedCircuit TensorCoefficientCounting RationalOutput
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate
open QecReliability.TensorMachine.Boundary

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (SharedCircuit.LatentEncoding.keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))
  (m : ℕ) (ω : Fin (2*m+1) → Ω) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  {resource : SATRequest → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T resource)

theorem general_tables (B q seed : ℕ) (coins : List Bool) :
    GeneralRepairFL.generalR (ds,grid ds,n,Trans.Query.encRows rows,Trans.Query.encProg C,q,seed,coins)
      (CountingTrace.sideEntries (SharedCircuit.LatentEncoding.keySize n ds.sum)
        (slots ds-1) B m (external rows C H K m ω density spec) true
        (List.finRange (slots ds-1+1)))
      (CountingTrace.sideEntries (SharedCircuit.LatentEncoding.keySize n ds.sum)
        (slots ds-1) B m (external rows C H K m ω density spec) false
        (List.finRange (slots ds-1+1))) =
      (TensorGeneral.output rows (TensorEncoding.circuitMap C)
        (TensorEncoding.queries ds rows C H K spec.service.solver) B m ω).map
          FL.Lib.LinearRepairFL.toR := by
  rw [table_eq,table_eq,GeneralRepairFL.generalR_eq_cornerPrepare]
  have hc : RepairFL.circuitObservations ds C = TensorEncoding.circuitMap C := rfl
  rw [hc]
  unfold TensorGeneral.output
  apply congrArg (fun estimates =>
    (TensorGeneral.cornerPrepare ds rows (TensorEncoding.circuitMap C) estimates).map
      FL.Lib.LinearRepairFL.toR)
  funext j
  simp only [RationalTensorConfidence.estimateRatios,CachedAnswers.median_eq,cached]

end QecReliability.TensorMachine.GeneralBoundary

namespace QecReliability.TensorMachine.GeneralAlgorithm
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate RationalOutput
open OracleCost OracleCost.MultiTape Final QecPhysical QecPhysical.Stabilizer

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
  (C : SharedCircuit.Program ds.sum n) (solver : ∀ v, PrefixCNF.ExactSAT v 3)

theorem outputVector_list (B m : ℕ)
    (coins : CodeHash.BitTape (CodeHash.repeatBits
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m)) :
    (outputVector hD hd A rows C solver B m coins).entries.toList =
      output hD hd A rows C solver B m coins := by
  simp only [outputVector,List.toList_toArray]

variable (a b c d : ℕ)

local notation "BB" => rationalCellBudget a b
local notation "MM" => rationalRepetitionBudget (2*slots ds) c d
local notation "NN" => CodeHash.repeatBits (Factory.length hD hd A n ds)
  (Factory.width hD hd A n ds) MM
local notation "VEC" => outputVector hD hd A rows C solver BB MM

/-- Transfer of the general-circuit guarantee to every output of any machine
whose canonical run writes `VEC`. No monotonicity hypothesis. -/
theorem general_output_transfer (L : Lift (rowSpace rows))
    (ha : 0<a) (hab : a≤b) (hc : 0<c) (hd' : 0<d)
    {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    (M : Machine k Γ Λ) (o : Fin (k+1)) (encode : (Fin NN → Bool) → List Bool)
    (hrun : ∀ coins, ∃ run : Completed M (encode coins), Outputs M run o (VEC coins)) :
    (∀ coins (run : Completed M (encode coins)) (v : Vector (slots ds-1)),
      Outputs M run o v → v = VEC coins) ∧
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape NN)).prob
      (fun coins => ∀ (run : Completed M (encode coins)) (v : Vector (slots ds-1)),
        Outputs M run o v → L.TensorPhysicalAccuracy (TensorEncoding.circuitMap C)
          ((a:ℝ)/b) (vectorCurve ds v)) := by
  obtain ⟨_,hprob⟩ := vector_guarantee hD hd A rows C solver L a b c d ha hab hc hd'
  constructor
  · intro coins run v hv
    obtain ⟨canonical,hcanonical⟩ := hrun coins
    exact outputs_unique_runs hv hcanonical
  · apply hprob.trans
    apply FiniteProbability.prob_mono
    intro coins hgood run v hv
    obtain ⟨canonical,hcanonical⟩ := hrun coins
    have he := outputs_unique_runs hv hcanonical
    rw [he]
    exact hgood

end QecReliability.TensorMachine.GeneralAlgorithm

#print axioms QecReliability.TensorMachine.GeneralBoundary.general_tables
#print axioms QecReliability.TensorMachine.GeneralAlgorithm.general_output_transfer
