import OracleCost.EnginePhysical
import QecReliability.CodeHashStages
import QecReliability.FiniteRandomTapeExecutionCandidate

/-!


This is a raw finite-bit-word SEMANTIC endpoint, not a physical sampler or a
whole-wrapper machine. It specializes the engine endpoint to the
binary CodeHash seed space and interprets the ACTUAL stored sampler output.
The supplied CodeHash.System and correct hash circuits remain explicit inputs;
no efficient all-length hash factory, table lowering, or total runtime follows.
-/

noncomputable section
namespace QecReliability.OracleCost.StoredCodeHashConfidence

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput QecPhysical QecPhysical.Stabilizer MultiTape
open CodeHash.FiniteRandomTape

/-- The actual binary-code stages, not arbitrary stages with an assumed law.
`CodeHash.F = ZMod 2`; a full seed has exactly L*(t+1) fair bits. -/
def actualCodeHash {n r L t : ℕ}
    (S : CodeHash.System (CoefficientKey n r) L t (keySize n r)) :
    HashStages (CodeHash.Seed L t) (CoefficientKey n r) (keySize n r) :=
  S.stages

@[simp] theorem actualCodeHash_law {n r L t : ℕ}
    (S : CodeHash.System (CoefficientKey n r) L t (keySize n r)) :
    (actualCodeHash S).law = uniformLaw (CodeHash.Seed L t) := rfl

/-- Decode only the loader's final finite store. This function is a ghost
interpretation, not a claim that a function-valued object is materialized. -/
def actualCodeHashSeedTuple (L t m : ℕ)
    (w : InputWord (CodeHash.repeatBits L t m)) :
    Fin (2*m+1) → CodeHash.Seed L t :=
  outputSeeds L t m (sample w).store

/-- Every indexed tuple remains possible, including repeated identical seeds.
No deduplication or without-replacement sampling is performed. -/
theorem actualCodeHashSeedTuple_surjective (L t m : ℕ) :
    Function.Surjective (actualCodeHashSeedTuple L t m) := by
  intro ω
  refine ⟨InputWord.ofTape _ ((CodeHash.repeatedSeedTapeEquiv L t m).symm ω), ?_⟩
  simp only [actualCodeHashSeedTuple, outputSeeds_sample, semanticSeeds,
    InputWord.denote_ofTape, Equiv.apply_symm_apply]

/-- Finite-stack guarantees only: live payload cells are not visited TM cells. -/
def StoredSamplerFacts {N : ℕ} (w : InputWord N) : Prop :=
  (sample w).store = w.cells ∧
  draws (2*N+2) (loadInit w.cells) = N ∧
  (∀ time, loadCells (loadRun time (loadInit w.cells)) = N) ∧
  (∀ time, (loadRun time (loadInit w.cells)).pc = .halt ↔ 2*N+2 ≤ time)

theorem storedSamplerFacts {N : ℕ} (w : InputWord N) : StoredSamplerFacts w := by
  refine ⟨?_, sample_draws_exact w, sample_space w, ?_⟩
  · rw [sample_exact]
  · intro time
    simpa only [InputWord.cells_length] using load_first_halt w.cells time

variable {n r L t : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (S : CodeHash.System (CoefficientKey n r) L t (keySize n r))
    (K : SuppliedHashCircuits (actualCodeHash S) (keyBits n r))

/-- One tuple from one loaded store is supplied to both coefficient families. -/
def rawBitMeasured (service : SATService) (B m : ℕ)
    (w : InputWord (CodeHash.repeatBits L t m)) : QuantumService.MeasuredCoefficients r :=
  QuantumService.prepareMeasured rows C (actualCodeHash S) K service B m
    (actualCodeHashSeedTuple L t m w)

/-- This is exactly the existing repaired output, with the seed tuple obtained
from the stored sampler output. It is not a newly postulated estimator. -/
def rawBitOutput (service : SATService) (a b c d : ℕ)
    (w : InputWord (CodeHash.repeatBits L t
      (rationalRepetitionBudget (2*(r+1)) c d))) : LinearRepair.Output r :=
  QuantumService.output rows C (actualCodeHash S) K service true a b c d
    (actualCodeHashSeedTuple L t (rationalRepetitionBudget (2*(r+1)) c d) w)

/-- Exact raw cache identity: no second cache, second output, or changed budget. -/
theorem rawBitOutput_raw (service : SATService) (a b c d : ℕ)
    (w : InputWord (CodeHash.repeatBits L t
      (rationalRepetitionBudget (2*(r+1)) c d))) :
    (rawBitOutput rows C S K service a b c d w).raw =
      (rawBitMeasured rows C S K service (rationalCellBudget a b)
        (rationalRepetitionBudget (2*(r+1)) c d) w).erase := rfl

/-- Both sides and every coefficient read the SAME full indexed tuple.
This semantic identity does not implement the physical coefficient loop. -/
theorem same_tuple_for_each_coefficient (service : SATService) (B m : ℕ)
    (w : InputWord (CodeHash.repeatBits L t m)) (j : Fin (r+1)) :
    (rawBitMeasured rows C S K service B m w).good.get j =
      QuantumService.coefficient rows C (actualCodeHash S) K service B m
        (actualCodeHashSeedTuple L t m w) (true,j) ∧
    (rawBitMeasured rows C S K service B m w).bad.get j =
      QuantumService.coefficient rows C (actualCodeHash S) K service B m
        (actualCodeHashSeedTuple L t m w) (false,j) := by
  constructor <;>
    simp only [rawBitMeasured, QuantumService.prepareMeasured,
      CachedControl.MeasuredTable.get_build]

/-- The COMPLETE all-p, fidelity-and-infidelity event. The same absolute error
is bounded relative to F and to 1-F, exactly the source RelPair predicate. -/
def AllPhysicalTails (lift : Lift (rowSpace rows)) (ε : ℝ) (R : ℝ → ℝ) : Prop :=
  ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
    let F := entanglementFidelity
      (lift.erasureFlagDecoder.comp (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map
    |R p-F| ≤ ε*F ∧ |R p-F| ≤ ε*(1-F)

theorem allPhysicalTails_iff (lift : Lift (rowSpace rows)) (ε : ℝ) (R : ℝ → ℝ) :
    AllPhysicalTails rows C lift ε R ↔
      lift.PhysicalAccuracy (circuitMap C) ε R := Iff.rfl

/-- Exact event transport through the ACTUAL stored output. No confidence
premise, seed-law equality premise, or fresh-per-coefficient sampling premise. -/
theorem raw_physical_event_law (lift : Lift (rowSpace rows))
    (service : SATService) (a b c d : ℕ) :
    (uniformLaw (InputWord (CodeHash.repeatBits L t
      (rationalRepetitionBudget (2*(r+1)) c d)))).prob
      (fun w => AllPhysicalTails rows C lift ((a:ℝ)/b)
        (rawBitOutput rows C S K service a b c d w).coefficients.curve) =
    (repeatedLaw (actualCodeHash S).law
      (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => lift.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (QuantumService.output rows C (actualCodeHash S) K service true a b c d ω).coefficients.curve) := by
  exact executed_sampler_exact_law L t
    (rationalRepetitionBudget (2*(r+1)) c d)
    (fun ω => lift.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
      (QuantumService.output rows C (actualCodeHash S) K service true a b c d ω).coefficients.curve)

/-- Deterministic target identification and unrestricted all-CPTP optimality.
This predicate is deliberately OUTSIDE the random accuracy event. -/
def PhysicalTargetOptimality (lift : Lift (rowSpace rows)) : Prop :=
  ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
    entanglementFidelity
      (lift.erasureFlagDecoder.comp (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map =
        latentCurve (circuitMap C) (score (rowSpace rows)) p ∧
    ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
      entanglementFidelity (Q.comp (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map ≤
        entanglementFidelity
          (lift.erasureFlagDecoder.comp (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map

theorem physicalTargetOptimality (lift : Lift (rowSpace rows)) :
    PhysicalTargetOptimality rows C lift :=
  lift.cached_target_optimality (circuitMap C)

variable {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine k Γ Λ} {density : ℕ}
    {Ptime Pspace : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT M density Ptime Pspace T) (hT : Monotone T)

include hT

/-- Each individual engine invocation is the existing fixed finite-machine
run. These workspace bounds are NOT a global reusable-tape space bound. -/
theorem codehash_engine_request_bounds (g : ℕ)
    (hg : ∀ s seed, (K.program s seed).gates ≤ g) :
    (∀ i pre,
      (spec.service.run (QuantumService.baseRequest rows C i pre)).time ≤
        Ptime.eval (QuantumService.engineInputBound rows C density g) *
          T (QuantumService.engineVariables rows C density g) ∧
      (spec.service.run (QuantumService.baseRequest rows C i pre)).workspace ≤
        machineCellBits Γ * Pspace.eval (QuantumService.engineInputBound rows C density g) +
          machineControlBits Λ) ∧
    (∀ i s seed pre,
      (spec.service.run (QuantumService.cellRequest rows C (actualCodeHash S) K i s seed pre)).time ≤
        Ptime.eval (QuantumService.engineInputBound rows C density g) *
          T (QuantumService.engineVariables rows C density g) ∧
      (spec.service.run (QuantumService.cellRequest rows C (actualCodeHash S) K i s seed pre)).workspace ≤
        machineCellBits Γ * Pspace.eval (QuantumService.engineInputBound rows C density g) +
          machineControlBits Λ) := by
  constructor
  · intro i pre
    have hb := QuantumService.base_dimensions rows C g i pre
    exact spec.request_bounds hT _ _ _ hb.1 hb.2
  · intro i s seed pre
    have hb := QuantumService.cell_dimensions rows C (actualCodeHash S) K g i s seed pre (hg s seed)
    exact spec.request_bounds hT _ _ _ hb.1 hb.2

/-- RAW-BIT SEMANTIC ENDPOINT.

All-run sampler facts, actual summed SAT time, call bound, retained-output
resources, and shape are deterministic. All-CPTP target optimality is a separate
deterministic conjunct. Only the whole all-p two-tail accuracy event is random.
The positive rational parameters, original integer budgets, layer antitonicity,
fixed finite SAT engine and supplied hash circuits/gate cap are unchanged.

This does NOT bound sampler+wrapper+engine total time or total machine space.
-/
theorem raw_bit_engine_shape_confidence (lift : Lift (rowSpace rows))
    (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hab : a≤b)
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows))))
    (g : ℕ) (hg : ∀ s seed, (K.program s seed).gates ≤ g) :
    (∀ w : InputWord (CodeHash.repeatBits L t
        (rationalRepetitionBudget (2*(r+1)) c d)),
      let B := rationalCellBudget a b
      let m := rationalRepetitionBudget (2*(r+1)) c d
      let O := rawBitOutput rows C S K spec.service a b c d w
      StoredSamplerFacts w ∧
      (rawBitMeasured rows C S K spec.service B m w).oracleTime ≤
        2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B *
          Ptime.eval (QuantumService.engineInputBound rows C density g) *
            T (QuantumService.engineVariables rows C density g) ∧
      O.raw.calls ≤ 2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B ∧
      LinearRepair.Resources n r B m O ∧
      ShapeStructure (rowSpace rows) (circuitMap C) O.coefficients.curve) ∧
    PhysicalTargetOptimality rows C lift ∧
    1-(c:ℝ)/d ≤
      (uniformLaw (InputWord (CodeHash.repeatBits L t
        (rationalRepetitionBudget (2*(r+1)) c d)))).prob
        (fun w => AllPhysicalTails rows C lift ((a:ℝ)/b)
          (rawBitOutput rows C S K spec.service a b c d w).coefficients.curve) := by
  have h := QuantumService.engine_shape_confidence rows C (actualCodeHash S) K spec hT
    lift a b c d ha hb hc hd hab hanti g hg
  refine ⟨?_, physicalTargetOptimality rows C lift, ?_⟩
  · intro w
    have hw := h.1 (actualCodeHashSeedTuple L t
      (rationalRepetitionBudget (2*(r+1)) c d) w)
    exact ⟨storedSamplerFacts w, hw.1, hw.2.1.1.1, hw.2.1, hw.2.2⟩
  · rw [raw_physical_event_law rows C S K lift spec.service a b c d]
    exact h.2

end QecReliability.OracleCost.StoredCodeHashConfidence
