import OracleCost.StoredCodeHashEngineConfidenceCandidate
import PhysicalBridge.ZeroLengthDispatchCandidate

/-!


One branchwise semantic endpoint: n=0 takes Unit and returns the literal
one-entry vector; n>0 consumes the finite stored-word interface and returns
the existing machine-backed cached/repaired coefficients. The reported SAT
time is the existing sum of actual isolated engine run times, NOT linked
whole-machine runtime. No factory, probability, or wrapper-cost field is added.

The dependent zero branch contains no budget, factory application, sample,
cache, or SAT call. Physical early branching still needs the finite frontend
refinement: this noncomputable semantic module is not that implementation.
-/

noncomputable section
namespace QecReliability.OracleCost.StoredBitDispatch

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput QecPhysical QecPhysical.Stabilizer MultiTape
open CodeHash.FiniteRandomTape StoredCodeHashConfidence

/- Families are indexed ONLY by positive physical sizes k+1. A supplied
family is not a certified efficient uniform factory. -/
variable {length width : ℕ → ℕ}
    (S : ∀ k, CodeHash.System (CoefficientKey (k+1) (k+1))
      (length k) (width k) (keySize (k+1) (k+1)))
    (K : ∀ k, SuppliedHashCircuits (actualCodeHash (S k)) (keyBits (k+1) (k+1)))

/-- Unlike a zero-length InputWord, Unit does not enter the two-step loader. -/
def RawInput (length width : ℕ → ℕ) (c d : ℕ) : ℕ → Type
  | 0 => Unit
  | k+1 => InputWord (CodeHash.repeatBits (length k) (width k)
      (rationalRepetitionBudget (2*((k+1)+1)) c d))

instance rawInputFintype (length width : ℕ → ℕ) (c d n : ℕ) :
    Fintype (RawInput length width c d n) := by
  cases n <;> dsimp [RawInput] <;> infer_instance

def inputLaw (length width : ℕ → ℕ) (c d : ℕ) :
    (n : ℕ) → FiniteProbability (RawInput length width c d n)
  | 0 => ZeroLengthDispatch.unitLaw
  | k+1 => uniformLaw (InputWord (CodeHash.repeatBits (length k) (width k)
      (rationalRepetitionBudget (2*((k+1)+1)) c d)))

def randomBits (length width : ℕ → ℕ) (c d : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => CodeHash.repeatBits (length k) (width k)
      (rationalRepetitionBudget (2*((k+1)+1)) c d)

/-- Actual stored output is decoded only in the successor arm. -/
def seedTuple (length width : ℕ → ℕ) (c d : ℕ) :
    (n : ℕ) → RawInput length width c d n →
      ZeroLengthDispatch.Seed (fun k => CodeHash.Seed (length k) (width k)) c d n
  | 0, _ => ()
  | k+1, w => actualCodeHashSeedTuple (length k) (width k)
      (rationalRepetitionBudget (2*((k+1)+1)) c d) w

def run (service : SATService) (a b c d : ℕ) :
    (n : ℕ) → List (List (PauliCoord n)) → RawInput length width c d n → Vector n
  | 0, _, _ => ZeroLengthDispatch.zeroVector
  | k+1, rows, w =>
      (rawBitOutput rows (ZeroLengthDispatch.iidProgram (k+1)) (S k) (K k)
        service a b c d w).coefficients

/-- Ghost measurement of exactly the same positive raw cache; no invented
zero-case raw cache/report is manufactured just to share an output type. -/
def calls (service : SATService) (a b c d : ℕ) :
    (n : ℕ) → List (List (PauliCoord n)) → RawInput length width c d n → ℕ
  | 0, _, _ => 0
  | k+1, rows, w =>
      (rawBitOutput rows (ZeroLengthDispatch.iidProgram (k+1)) (S k) (K k)
        service a b c d w).raw.calls

def oracleTime (service : SATService) (a b c d : ℕ) :
    (n : ℕ) → List (List (PauliCoord n)) → RawInput length width c d n → ℕ
  | 0, _, _ => 0
  | k+1, rows, w =>
      (rawBitMeasured rows (ZeroLengthDispatch.iidProgram (k+1)) (S k) (K k)
        service (rationalCellBudget a b)
        (rationalRepetitionBudget (2*((k+1)+1)) c d) w).oracleTime

def callCap (a b c d : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*((n+1)+1)*(2*rationalRepetitionBudget (2*((n+1)+1)) c d+1)*
      trialCallBound (keySize (n+1) (n+1)) (rationalCellBudget a b)

/-- The zero branch has no phantom positive-branch resource record. -/
def retainedFacts (service : SATService) (a b c d : ℕ) :
    (n : ℕ) → List (List (PauliCoord n)) → RawInput length width c d n → Prop
  | 0, _, _ => True
  | k+1, rows, w => StoredSamplerFacts w ∧
      LinearRepair.Resources (k+1) (k+1) (rationalCellBudget a b)
        (rationalRepetitionBudget (2*((k+1)+1)) c d)
        (rawBitOutput rows (ZeroLengthDispatch.iidProgram (k+1)) (S k) (K k)
          service a b c d w)

@[simp] theorem zero_branch (service : SATService) (a b c d : ℕ)
    (rows : List (List (PauliCoord 0))) (w : RawInput length width c d 0) :
    run S K service a b c d 0 rows w = ZeroLengthDispatch.zeroVector ∧
    calls S K service a b c d 0 rows w = 0 ∧
    oracleTime S K service a b c d 0 rows w = 0 ∧
    randomBits length width c d 0 = 0 := ⟨rfl, rfl, rfl, rfl⟩

/-- Literal coefficient identity with the semantic dispatcher.
This uses the SAME output and tuple, not a distributionally equivalent output. -/
theorem run_eq_source_dispatch (service : SATService) (a b c d : ℕ)
    (n : ℕ) (rows : List (List (PauliCoord n))) (w : RawInput length width c d n) :
    run S K service a b c d n rows w =
      ZeroLengthDispatch.run (fun k => actualCodeHash (S k)) K service.solver
        a b c d n rows (seedTuple length width c d n w) := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [run, rawBitOutput, ZeroLengthDispatch.run, seedTuple,
      QuantumService.output_eq]

theorem run_retainedFacts (service : SATService) (a b c d : ℕ)
    (n : ℕ) (rows : List (List (PauliCoord n))) (w : RawInput length width c d n) :
    retainedFacts S K service a b c d n rows w := by
  cases n with
  | zero => exact True.intro
  | succ k =>
    refine ⟨storedSamplerFacts w, ?_⟩
    simp only [rawBitOutput, QuantumService.output_eq]
    exact LinearRepair.prepare_resources true rows (ZeroLengthDispatch.iidProgram (k+1))
      (actualCodeHash (S k)) (K k) service.solver a b c d
      (actualCodeHashSeedTuple (length k) (width k)
        (rationalRepetitionBudget (2*((k+1)+1)) c d) w)

theorem run_calls_le (service : SATService) (a b c d : ℕ)
    (n : ℕ) (rows : List (List (PauliCoord n))) (w : RawInput length width c d n) :
    calls S K service a b c d n rows w ≤ callCap a b c d n := by
  cases n with
  | zero => exact Nat.le_refl 0
  | succ k =>
    exact (run_retainedFacts S K service a b c d (k+1) rows w).2.1.1

theorem run_structure (service : SATService) (a b c d : ℕ)
    (n : ℕ) (rows : List (List (PauliCoord n))) (lift : Lift (rowSpace rows))
    (w : RawInput length width c d n) :
    ShapeStructure (rowSpace rows) (circuitMap (ZeroLengthDispatch.iidProgram n))
      (run S K service a b c d n rows w).curve := by
  rw [run_eq_source_dispatch]
  exact ZeroLengthDispatch.run_structure (fun k => actualCodeHash (S k)) K
    service.solver a b c d n rows lift (seedTuple length width c d n w)

theorem run_tails (service : SATService) (a b c d : ℕ)
    (n : ℕ) (rows : List (List (PauliCoord n))) (lift : Lift (rowSpace rows))
    (w : RawInput length width c d n) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    TailExact (entanglementFidelity (lift.erasureFlagDecoder.comp
      (lift.iidLatentErasure (circuitMap (ZeroLengthDispatch.iidProgram n))
        p hp.1 hp.2)).map) ((run S K service a b c d n rows w).curve p) := by
  rw [run_eq_source_dispatch]
  exact ZeroLengthDispatch.run_tails (fun k => actualCodeHash (S k)) K
    service.solver a b c d n rows lift (seedTuple length width c d n w) p hp

/-- Deterministic all-CPTP target theorem; not inside any random event. -/
theorem target_optimality (n : ℕ) (rows : List (List (PauliCoord n)))
    (lift : Lift (rowSpace rows)) :
    PhysicalTargetOptimality rows (ZeroLengthDispatch.iidProgram n) lift :=
  physicalTargetOptimality rows (ZeroLengthDispatch.iidProgram n) lift

/-- Exact zero-branch event mass, not merely a vacuous confidence bound. -/
theorem zero_event_probability (service : SATService) (a b c d : ℕ)
    (rows : List (List (PauliCoord 0))) (lift : Lift (rowSpace rows)) :
    (inputLaw length width c d 0).prob (fun w =>
      AllPhysicalTails rows (ZeroLengthDispatch.iidProgram 0) lift ((a:ℝ)/b)
        (run S K service a b c d 0 rows w).curve) = 1 := by
  exact ZeroLengthDispatch.zeroPhysical_success_probability rows lift
    (circuitMap (ZeroLengthDispatch.iidProgram 0)) ((a:ℝ)/b)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Exact whole-event transport in the positive branch, exact success one in
the zero branch. No c≤d restriction, independent resampling, or extra union bound. -/
theorem run_confidence (service : SATService) (a b c d : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hab : a≤b)
    (n : ℕ) (rows : List (List (PauliCoord n))) (lift : Lift (rowSpace rows)) :
    1-(c:ℝ)/d ≤ (inputLaw length width c d n).prob (fun w =>
      AllPhysicalTails rows (ZeroLengthDispatch.iidProgram n) lift ((a:ℝ)/b)
        (run S K service a b c d n rows w).curve) := by
  cases n with
  | zero =>
    change 1-(c:ℝ)/d ≤ ZeroLengthDispatch.unitLaw.prob (fun _ =>
      lift.PhysicalAccuracy (circuitMap (ZeroLengthDispatch.iidProgram 0))
        ((a:ℝ)/b) ZeroLengthDispatch.zeroVector.curve)
    rw [ZeroLengthDispatch.zeroPhysical_success_probability rows lift _ _
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact sub_le_self _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  | succ k =>
    change 1-(c:ℝ)/d ≤
      (uniformLaw (InputWord (CodeHash.repeatBits (length k) (width k)
        (rationalRepetitionBudget (2*((k+1)+1)) c d)))).prob (fun w =>
          AllPhysicalTails rows (ZeroLengthDispatch.iidProgram (k+1)) lift ((a:ℝ)/b)
            (rawBitOutput rows (ZeroLengthDispatch.iidProgram (k+1))
              (S k) (K k) service a b c d w).coefficients.curve)
    rw [raw_physical_event_law rows (ZeroLengthDispatch.iidProgram (k+1))
      (S k) (K k) lift service a b c d]
    have h := QecPhysical.Stabilizer.Lift.linear_shape_confidence rows lift
      (ZeroLengthDispatch.iidProgram (k+1)) (actualCodeHash (S k)) (K k)
      service.solver a b c d ha hb hc hd hab
      (ZeroLengthDispatch.iid_layers_antitone rows lift)
    simpa only [QuantumService.output_eq] using h.2

def timeCap (Ptime : PolynomialEnvelope) (T : ℕ → ℕ) (density : ℕ)
    (g : ℕ → ℕ) (a b c d : ℕ) : (n : ℕ) → List (List (PauliCoord n)) → ℕ
  | 0, _ => 0
  | k+1, rows => callCap a b c d (k+1) *
      Ptime.eval (QuantumService.engineInputBound rows
        (ZeroLengthDispatch.iidProgram (k+1)) density (g k)) *
      T (QuantumService.engineVariables rows
        (ZeroLengthDispatch.iidProgram (k+1)) density (g k))

variable {tapes : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine tapes Γ Λ} {density : ℕ}
    {Ptime Pspace : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT M density Ptime Pspace T) (hT : Monotone T)

include hT

/-- All tapes, including unsuccessful statistical runs. Only isolated engine
time is measured; engine initialization/copy/reset/linking are NOT supplied. -/
theorem run_engine_time_le (g : ℕ → ℕ)
    (hg : ∀ k s seed, ((K k).program s seed).gates ≤ g k)
    (a b c d : ℕ) (n : ℕ) (rows : List (List (PauliCoord n)))
    (w : RawInput length width c d n) :
    oracleTime S K spec.service a b c d n rows w ≤
      timeCap Ptime T density g a b c d n rows := by
  cases n with
  | zero => exact Nat.le_refl 0
  | succ k =>
    exact QuantumService.prepare_engine_time rows (ZeroLengthDispatch.iidProgram (k+1))
      (actualCodeHash (S k)) (K k) spec hT (rationalCellBudget a b)
      (rationalRepetitionBudget (2*((k+1)+1)) c d) (g k) (hg k)
      (actualCodeHashSeedTuple (length k) (width k)
        (rationalRepetitionBudget (2*((k+1)+1)) c d) w)

/-- Composed endpoint: all-run facts and physical optimum precede the sole
random conjunction. No whole-estimator cost or success premise appears. -/
theorem engine_dispatch_shape_confidence (g : ℕ → ℕ)
    (hg : ∀ k s seed, ((K k).program s seed).gates ≤ g k)
    (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hab : a≤b)
    (n : ℕ) (rows : List (List (PauliCoord n))) (lift : Lift (rowSpace rows)) :
    (∀ w : RawInput length width c d n,
      retainedFacts S K spec.service a b c d n rows w ∧
      calls S K spec.service a b c d n rows w ≤ callCap a b c d n ∧
      oracleTime S K spec.service a b c d n rows w ≤
        timeCap Ptime T density g a b c d n rows ∧
      ShapeStructure (rowSpace rows) (circuitMap (ZeroLengthDispatch.iidProgram n))
        (run S K spec.service a b c d n rows w).curve) ∧
    PhysicalTargetOptimality rows (ZeroLengthDispatch.iidProgram n) lift ∧
    1-(c:ℝ)/d ≤ (inputLaw length width c d n).prob (fun w =>
      AllPhysicalTails rows (ZeroLengthDispatch.iidProgram n) lift ((a:ℝ)/b)
        (run S K spec.service a b c d n rows w).curve) := by
  refine ⟨?_, target_optimality n rows lift,
    run_confidence S K spec.service a b c d ha hb hc hd hab n rows lift⟩
  intro w
  exact ⟨run_retainedFacts S K spec.service a b c d n rows w,
    run_calls_le S K spec.service a b c d n rows w,
    run_engine_time_le S K spec hT g hg a b c d n rows w,
    run_structure S K spec.service a b c d n rows lift w⟩

end QecReliability.OracleCost.StoredBitDispatch
