import TensorFixedQuantumClosure

/-! Strengthened closed multiclass theorem. In addition to the conjuncts of
`isotropic_tensor_machine_guarantee`, it states optimality of the physical target
over all recoveries, and deterministic structure of the actual output coefficient
table on every coin string: antitone, unit range, exact corners, and exact
identification of the coefficients equal to one (zero infidelity). The certificate
is the explicit selector `PackedSemanticBridgeCandidate.localCertified`. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

/-! ## Repair retains exactly the coefficients equal to one -/
namespace QecReliability.PosetShapeRepair

variable {ι : Type*} [Fintype ι] [PartialOrder ι]

/-- If the target `f` is antitone in `[0,1]`, the anchors are exact, and every
estimate is at most one and equals one exactly where `f` does, then the repaired
table equals one exactly where `f` does. -/
theorem repair_eq_one_iff (anchors : Finset ι) (anchorValues estimates f : ι → ℝ)
    (hanti : Antitone f) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hanchor : ∀ a ∈ anchors, anchorValues a = f a)
    (hle : ∀ i, estimates i ≤ 1) (hone : ∀ i, estimates i = 1 ↔ f i = 1) (j : ι) :
    repair anchors anchorValues estimates j = 1 ↔ f j = 1 := by
  classical
  have hA : ∀ i, anchoredEstimate anchors anchorValues estimates i ≤ 1 ∧
      (anchoredEstimate anchors anchorValues estimates i = 1 ↔ f i = 1) := by
    intro i
    by_cases hi : i ∈ anchors
    · simp only [anchoredEstimate, hi, ↓reduceIte, hanchor i hi, iff_self, and_true]
      exact (hf i).2
    · simp only [anchoredEstimate, hi, ↓reduceIte, clip, min_eq_right (hle i)]
      refine ⟨max_le (by norm_num) (hle i), ?_⟩
      rw [← hone i]
      constructor
      · intro h
        rcases le_total 0 (estimates i) with h0 | h0
        · rwa [max_eq_right h0] at h
        · rw [max_eq_left h0] at h
          norm_num at h
      · intro h
        rw [h]
        norm_num
  constructor
  · intro h
    by_contra hne
    have hlt : f j < 1 := lt_of_le_of_ne (hf j).2 hne
    have h1 : anchoredEstimate anchors anchorValues estimates j < 1 :=
      lt_of_le_of_ne (hA j).1 (fun e => hne ((hA j).2.mp e))
    have h2 : prefixMinimum (anchoredEstimate anchors anchorValues estimates) j < 1 :=
      (prefixMinimum_le _ le_rfl).trans_lt h1
    have h3 : anchorFloor anchors anchorValues j ≤ f j := by
      apply (anchorFloor_le_iff anchors anchorValues j (f j)).mpr
      refine ⟨(hf j).1, ?_⟩
      intro a ha hja
      rw [hanchor a ha]
      exact hanti hja
    have h4 : repair anchors anchorValues estimates j < 1 :=
      max_lt (h3.trans_lt hlt) h2
    rw [h] at h4
    exact lt_irrefl _ h4
  · intro h
    apply le_antisymm
    · apply max_le
      · apply (anchorFloor_le_iff anchors anchorValues j 1).mpr
        refine ⟨by norm_num, ?_⟩
        intro a ha _
        rw [hanchor a ha]
        exact (hf a).2
      · exact (prefixMinimum_le _ le_rfl).trans (hA j).1
    · apply le_max_of_le_right
      apply (le_prefixMinimum_iff _ j 1).mpr
      intro i hij
      have hfi : f i = 1 := le_antisymm (hf i).2 (h ▸ hanti hij)
      exact ((hA i).2.mpr hfi).ge

end QecReliability.PosetShapeRepair

/-! ## The cached median ratio is one exactly when the true coefficient is one -/
namespace QecReliability.TensorCoefficientCounting
open TensorBernstein TensorLatent Binary
open SharedCircuit.LatentEncoding

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  {S : Submodule Bit (Pauli n)} {C : CausesGrid ds → Finset (Fin n)}
  {H : HashStages Ω (Key n ds) (keySize n ds.sum)}

theorem amplified_nonneg (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ)
    (ω : Fin (2*m+1) → Ω) (i : Index ds) : 0 ≤ ExactTrialOracle.amplified O B m ω i := by
  unfold ExactTrialOracle.amplified medianEstimate oddMedian
  exact Nat.cast_nonneg _

/-- The amplified count is zero exactly when the true count is zero, on every seed. -/
theorem amplified_eq_zero_iff (O : ∀ i, ExactTrialOracle H (coefficientModels S C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (i : Index ds) :
    ExactTrialOracle.amplified O B m ω i = 0 ↔ (coefficientModels S C i).card = 0 := by
  rw [Finset.card_eq_zero]
  constructor
  · intro hz
    by_contra hn
    have hp := ExactTrialOracle.amplified_positive O B m ω i
      (Finset.nonempty_iff_ne_empty.mpr hn)
    linarith
  · exact ExactTrialOracle.amplified_zero O B m ω i

theorem estimates_le_one (O : ∀ i, ExactTrialOracle H (coefficientModels S C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Grid ds) : estimates O B m ω j ≤ 1 := by
  have hg := amplified_nonneg O B m ω (true,j)
  have hb := amplified_nonneg O B m ω (false,j)
  unfold estimates
  exact div_le_one_of_le₀ (by linarith) (by linarith)

/-- Deterministic exactness of the coefficient one, on every seed: the estimated
ratio equals one iff the true normalized coefficient equals one. -/
theorem estimates_eq_one_iff (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Grid ds) :
    estimates O B m ω j = 1 ↔ observedCoefficients C (score S) j = 1 := by
  rw [← coefficient_normalized S hS C j]
  have hcg : (coefficientModels S C (true,j)).card = goodCoefficient S C j := by
    simp only [coefficientModels_card, ↓reduceIte]
  have hcb : (coefficientModels S C (false,j)).card = badCoefficient S C j := by
    simp only [coefficientModels_card, Bool.false_eq_true, ↓reduceIte]
  have hsum := coefficient_total_pos S C j
  have hg0 := amplified_nonneg O B m ω (true,j)
  unfold estimates
  set g := ExactTrialOracle.amplified O B m ω (true,j)
  set b := ExactTrialOracle.amplified O B m ω (false,j)
  rw [div_eq_one_iff_eq hsum.ne']
  by_cases hD : badCoefficient S C j = 0
  · have hb : b = 0 := (amplified_eq_zero_iff O B m ω (false,j)).mpr (hcb.trans hD)
    have hG : goodCoefficient S C j ≠ 0 := by
      intro hG
      rw [hG, hD] at hsum
      simp at hsum
    have hgpos : g ≠ 0 := by
      intro hg
      exact hG (hcg.symm.trans ((amplified_eq_zero_iff O B m ω (true,j)).mp hg))
    rw [hb, add_zero, div_self hgpos, hD]
    simp
  · have hbpos : 0 < b := lt_of_le_of_ne (amplified_nonneg O B m ω (false,j))
      (fun e => hD (hcb.symm.trans ((amplified_eq_zero_iff O B m ω (false,j)).mp e.symm)))
    have hDpos : (0:ℝ) < badCoefficient S C j := by exact_mod_cast Nat.pos_of_ne_zero hD
    constructor
    · intro h
      have hlt : g / (g + b) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      rw [h] at hlt
      exact absurd hlt (lt_irrefl _)
    · intro h
      linarith

end QecReliability.TensorCoefficientCounting

/-! ## Structure of the rational repaired table, for every seed -/
namespace QecReliability.RationalTensorConfidence
open Binary TensorBernstein TensorLatent TensorCoefficientCounting RationalOutput
open QecPhysical QecPhysical.Stabilizer

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  {H : HashStages Ω (Key n ds) (SharedCircuit.LatentEncoding.keySize n ds.sum)}
  (rows : List (List (SharedCircuit.PauliCoord n)))
  (C : CausesGrid ds → Finset (Fin n))

theorem coefficient_table_structure (L : Lift (SharedCircuit.rowSpace rows)) (hC : Monotone C)
    (D : ∀ i, DecisionQueries (keyBits n ds) H
      (coefficientModels (SharedCircuit.rowSpace rows) C i))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    let g := fun j => (RationalTensorRepair.coefficient ds rows C (estimateRatios D B m ω) j).value
    let f := multivariateCoefficients (SharedCircuit.rowSpace rows) C
    Antitone g ∧ (∀ j, 0 ≤ g j ∧ g j ≤ 1) ∧
    (∀ b : Corner ds, g (cornerIndex ds b) = f (cornerIndex ds b) ∧
      g (cornerIndex ds b) = erasureScore (SharedCircuit.rowSpace rows) (C (cornerCauses ds b))) ∧
    (∀ j, g j = 1 ↔ f j = 1) := by
  intro g f
  have hg : g = PosetShapeRepair.repair (MultivariateShapeRepair.cornerAnchors ds)
      (physicalCornerAnchorValues (SharedCircuit.rowSpace rows) C)
      (estimates (fun i => (D i).toTrialOracle) B m ω) := by
    funext j
    simp only [g, RationalTensorRepair.coefficient_value, estimateRatios_value]
  have hex := physicalCornerAnchorValues_exact (SharedCircuit.rowSpace rows) C
  have hanti : Antitone f := L.multivariateCoefficients_antitone C hC
  have hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1 := multivariateCoefficients_range _ C
  have hav : ∀ a ∈ MultivariateShapeRepair.cornerAnchors ds,
      0 ≤ physicalCornerAnchorValues (SharedCircuit.rowSpace rows) C a ∧
      physicalCornerAnchorValues (SharedCircuit.rowSpace rows) C a ≤ 1 := by
    intro a ha
    rw [hex a ha]
    exact hf a
  rw [hg]
  refine ⟨PosetShapeRepair.repair_antitone _ _ _, PosetShapeRepair.repair_range _ _ _ hav, ?_, ?_⟩
  · intro b
    have hmem := MultivariateShapeRepair.cornerIndex_mem ds b
    have hr := PosetShapeRepair.repair_anchor (MultivariateShapeRepair.cornerAnchors ds)
      (physicalCornerAnchorValues (SharedCircuit.rowSpace rows) C)
      (estimates (fun i => (D i).toTrialOracle) B m ω) (fun a ha => (hav a ha).1)
      (fun a ha c hc hac => by rw [hex a ha, hex c hc]; exact hanti hac) hmem
    refine ⟨hr.trans (hex _ hmem), ?_⟩
    rw [hr]
    simp only [physicalCornerAnchorValues, canonicalCauses_corner]
  · intro j
    exact PosetShapeRepair.repair_eq_one_iff _ _ _ f hanti hf hex
      (estimates_le_one _ B m ω)
      (fun i => estimates_eq_one_iff L.isotropic _ B m ω i) j

end QecReliability.RationalTensorConfidence

/-! ## The table read off the flat output vector -/
namespace QecReliability.TensorMachine
open RationalOutput TensorBernstein TensorLatent SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open QecPhysical QecPhysical.Stabilizer

/-- The coefficient table carried by an output vector, in grid coordinates. -/
def vectorTable (ds : List ℕ) (v : RationalOutput.Vector (slots ds-1)) : Grid ds → ℝ :=
  fun j => (v.get (position ds j)).value

theorem vectorCurve_eq_table (ds : List ℕ) (v : RationalOutput.Vector (slots ds-1)) :
    vectorCurve ds v = curve ds (vectorTable ds v) := rfl

namespace PhysicalAlgorithm
variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (solver : ∀ v, PrefixCNF.ExactSAT v 3) (B m : ℕ)
  (coins : CodeHash.BitTape (CodeHash.repeatBits
    (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m))

theorem outputVector_table_structure (L : Lift (rowSpace rows))
    (hC : Monotone (TensorEncoding.circuitMap C)) :
    let g := vectorTable ds (outputVector hD hd A rows C solver B m coins)
    let f := multivariateCoefficients (rowSpace rows) (TensorEncoding.circuitMap C)
    Antitone g ∧ (∀ j, 0 ≤ g j ∧ g j ≤ 1) ∧
    (∀ b : Corner ds, g (cornerIndex ds b) = f (cornerIndex ds b) ∧
      g (cornerIndex ds b) =
        erasureScore (rowSpace rows) (TensorEncoding.circuitMap C (cornerCauses ds b))) ∧
    (∀ j, g j = 1 ↔ f j = 1) := by
  have he : vectorTable ds (outputVector hD hd A rows C solver B m coins) =
      fun j => (RationalTensorRepair.coefficient ds rows (TensorEncoding.circuitMap C)
        (RationalTensorConfidence.estimateRatios (decisions hD hd A rows C solver) B m
          (CodeHash.repeatedSeedTapeEquiv _ _ m coins)) j).value := by
    funext j
    simp only [vectorTable]
    rw [outputVector_get, position_index]
  simp only [he]
  exact RationalTensorConfidence.coefficient_table_structure rows (TensorEncoding.circuitMap C)
    L hC (decisions hD hd A rows C solver) B m _

end PhysicalAlgorithm
end QecReliability.TensorMachine

/-! ## The strengthened closed theorem -/
namespace QecReliability.TensorMachine.Runtime.FixedQuantum
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape RationalOutput Final QecPhysical QecPhysical.Stabilizer
open ExternalSATBridge TensorBernstein TensorLatent
open QecReliability.LatentMachine.Runtime.FixedQuantum

/-- The explicit packed-semantic certificate, without `Classical.choice`. -/
@[irreducible] noncomputable def explicitCertificate :
    CertifiedParity (512 * fixedScale) (64 * fixedScale) fixedScale :=
  PackedSemanticBridgeCandidate.localCertified fixedScale fixedScale_pos

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => explicitCertificate

theorem isotropic_tensor_machine_guarantee_strong :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    Monotone (TensorEncoding.circuitMap C) →
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let f := multivariateCoefficients (rowSpace rows) (TensorEncoding.circuitMap C)
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n ds) (Factory.width HD HS CERT n ds) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    -- (a) the target is the Bernstein curve of `f`, and it is optimal over all recoveries
    (∀ p (hp : cube ds p),
      entanglementFidelity (lift.erasureFlagDecoder.comp
          (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map =
        curve ds f p ∧
      ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
        entanglementFidelity (Q.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map ≤
          entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map) ∧
    -- (b,c) every coin string: completed run, output, resources, curve and table structure
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input ds rows C a b c d (List.ofFn coins))) (v : Vector (slots ds-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed*
            (Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L ∧
        lift.TensorPhysicalStructure (TensorEncoding.circuitMap C) (vectorCurve ds v) ∧
        -- the output table is antitone in the componentwise order
        Antitone (vectorTable ds v) ∧
        -- every output coefficient lies in the unit interval
        (∀ j, 0 ≤ vectorTable ds v j ∧ vectorTable ds v j ≤ 1) ∧
        -- every corner coefficient is the exact physical score
        (∀ b : Corner ds, vectorTable ds v (cornerIndex ds b) = f (cornerIndex ds b) ∧
          vectorTable ds v (cornerIndex ds b) =
            erasureScore (rowSpace rows) (TensorEncoding.circuitMap C (cornerCauses ds b))) ∧
        -- zero-infidelity coefficients are identified exactly
        (∀ j, vectorTable ds v j = 1 ↔ f j = 1)) ∧
    -- (c) one coin event gives two-tail accuracy on the whole parameter cube
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input ds rows C a b c d (List.ofFn coins)))
        (v : Vector (slots ds-1)), Outputs M run outputTape v →
          lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b) (vectorCurve ds v)) := by
  obtain ⟨engine,PtE,PsE,rateConstant,hrate,spec,hT⟩ := ConcreteSolver.exists_resource_machine
  obtain ⟨Ptime,Pspace,hclosed⟩ := tensor_machine_guarantee HD HS CERT 1 spec hT
  refine ⟨engine,rateConstant,Ptime,Pspace,hrate,?_⟩
  intro n ds rows C a b c d ha hab hc hd hS hC
  obtain ⟨hruns,hshape,hprob⟩ := hclosed (n:=n) (ds:=ds) rows C a b c d ha hab hc hd
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS) hC
  refine ⟨?_,?_,hprob⟩
  · intro p hp
    have h := (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).multivariateLatentErasure_optimum
      (TensorEncoding.circuitMap C) p hp
    refine ⟨h.1, fun Q => ?_⟩
    rw [h.1]
    exact h.2 Q
  · intro coins
    obtain ⟨run,hout,htime,hspace⟩ := hruns coins
    obtain ⟨h1,h2,h3,h4⟩ := PhysicalAlgorithm.outputVector_table_structure HD HS CERT rows C
      spec.service.solver (rationalCellBudget a b) (rationalRepetitionBudget (2*slots ds) c d) coins
      (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS) hC
    exact ⟨run,_,hout,htime,hspace,hshape coins run _ hout,h1,h2,h3,h4⟩

end QecReliability.TensorMachine.Runtime.FixedQuantum

