import WholeWrapperFactoryInputRun
import OracleCost.StoredBitDispatchCandidate

/-! Source-level finite-word confidence instantiated by the actual one-certificate
all-length factory. No supplied hash system, compiler or gate-bound premise is
retained. The zero dispatch is semantic; finite tape front-end lowering remains
open, as does lowering the loader's first-order stack transitions. -/
noncomputable section
namespace QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open Binary SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open CodeHash UniformAdapter ExpanderWalk FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape
open RationalOutput QecPhysical QecPhysical.Stabilizer StoredCodeHashConfidence StoredBitDispatch

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
    (A : CertifiedParity (512*t) (64*t) t)

def positiveWalk (k : ℕ) :=
  (data hD hd A).walkCode (base_ge_eight hD hd A) actualMGG (keySize (k+1) (k+1))

def positiveLength (k : ℕ) : ℕ := (positiveWalk hD hd A k).L
def positiveWidth (k : ℕ) : ℕ := (positiveWalk hD hd A k).steps+1

def positiveSystem (k : ℕ) : CodeHash.System (CoefficientKey (k+1) (k+1))
    (positiveLength hD hd A k) (positiveWidth hD hd A k) (keySize (k+1) (k+1)) :=
  ((positiveWalk hD hd A k).codingData (keyBits (k+1) (k+1))).system

def positiveCircuits (k : ℕ) :
    SuppliedHashCircuits (actualCodeHash (positiveSystem hD hd A k)) (keyBits (k+1) (k+1)) :=
  (((data hD hd A).walkCircuits (base_ge_eight hD hd A) actualMGG
    (keySize (k+1) (k+1))).forward (keyBits (k+1) (k+1))).compiled.implementation.supplied

/-- Exact interface identity, not replacement by a distributionally equivalent
hash family. The proof fields differ only by proof irrelevance. -/
theorem positiveSystem_stages (k : ℕ) :
    actualCodeHash (positiveSystem hD hd A k)=
      stagesFor hD hd A (keyBits (k+1) (k+1)) := by
  have reindex {q : ℕ} (W : WalkCode q) {X : Type} (e : X ≃ BitModels q) :
      (W.codingData e).system.stages =
        stagesOn (W.codingData (Equiv.refl (BitModels q))).system.stages e := by
    rfl
  change ((positiveWalk hD hd A k).codingData (keyBits (k+1) (k+1))).system.stages =
    stagesOn ((positiveWalk hD hd A k).codingData
      (Equiv.refl (BitModels (keySize (k+1) (k+1))))).system.stages (keyBits (k+1) (k+1))
  exact reindex (positiveWalk hD hd A k) (keyBits (k+1) (k+1))

theorem positiveCircuits_program (k : ℕ) (scale : Fin (keySize (k+1) (k+1)+1))
    (seed : CodeHash.Seed (positiveLength hD hd A k) (positiveWidth hD hd A k)) :
    (positiveCircuits hD hd A k).program scale seed=
      (circuitsFor hD hd A (keyBits (k+1) (k+1))).program scale seed := by
  rfl

theorem positiveCircuits_gates (k : ℕ) (scale : Fin (keySize (k+1) (k+1)+1))
    (seed : CodeHash.Seed (positiveLength hD hd A k) (positiveWidth hD hd A k)) :
    ((positiveCircuits hD hd A k).program scale seed).gates≤
      gateConstant hD hd A*keySize (k+1) (k+1) := by
  rw [positiveCircuits_program]
  exact circuitsFor_gates_input hD hd A (keyBits (k+1) (k+1)) scale seed

/-- The sampler's local-affine payload is literally the factory's seed
budget, including the intercept bit at each position. -/
theorem positive_seedBits (k : ℕ) :
    CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k)=
      seedBits hD hd A (keySize (k+1) (k+1)) := by
  rfl

/-- All repeated seeds may be retained once in a quadratic-in-input bit word.
There is no query-count or epsilon-inverse multiplier and no fresh random
allocation on later queries. This is payload, not an unproved tape simulation. -/
theorem randomBits_input_polynomial (a b c d : ℕ) (ha : 0<a) (hc : 0<c)
    (n : ℕ) (rows : List (List (PauliCoord n))) :
    let L := InputEncoding.paperLength rows (ZeroLengthDispatch.iidProgram n) a b c d
    randomBits (positiveLength hD hd A) (positiveWidth hD hd A) c d n≤
      (6*L+5)*(seedConstant hD hd A*(2*L)) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ k =>
      obtain ⟨hn,hq,hr,hR,hB⟩ := InputEncoding.budget_parameters rows
        (ZeroLengthDispatch.iidProgram (k+1)) a b c d ha hc
      have hs := seed_linear hD hd A (keySize (k+1) (k+1))
      change (2*rationalRepetitionBudget (2*((k+1)+1)) c d+1)*
        CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k)≤_
      rw [positive_seedBits]
      exact Nat.mul_le_mul hR (hs.trans (Nat.mul_le_mul_left _ hq))

/-- For each positive stored input word, the actual native macro trace returns
literally the same coefficient vector as the source dispatcher. This is not
merely equality in law. The boundary equality is explicit pending physical
frontend/endpoint lowering; the zero branch remains a separate early dispatch. -/
theorem positive_macro_stored_output (service : SATService) (a b c d k : ℕ)
    (rows : List (List (PauliCoord (k+1))))
    (w : RawInput (positiveLength hD hd A) (positiveWidth hD hd A) c d (k+1))
    (density : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows (ZeroLengthDispatch.iidProgram (k+1))
      (actualCodeHash (positiveSystem hD hd A k)) (positiveCircuits hD hd A k) service
      (rationalRepetitionBudget (2*((k+1)+1)) c d)
      (actualCodeHashSeedTuple (positiveLength hD hd A k) (positiveWidth hD hd A k)
        (rationalRepetitionBudget (2*((k+1)+1)) c d) w) density ext) :
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*((k+1)+1)) c d
    ∃ final totals events,
      Trace (keySize (k+1) (k+1)) (k+1) B m true ext
        (initial (keySize (k+1) (k+1)) (k+1) m) totals events final ∧
      final.pc=.done ∧
      final.output=(run (positiveSystem hD hd A) (positiveCircuits hD hd A)
        service a b c d (k+1) rows w).entries.toList ∧
      totals.calls=calls (positiveSystem hD hd A) (positiveCircuits hD hd A)
        service a b c d (k+1) rows w ∧
      totals.oracleTime=oracleTime (positiveSystem hD hd A) (positiveCircuits hD hd A)
        service a b c d (k+1) rows w := by
  let omegaSeed := actualCodeHashSeedTuple (positiveLength hD hd A k) (positiveWidth hD hd A k)
    (rationalRepetitionBudget (2*((k+1)+1)) c d) w
  obtain ⟨final,totals,events,htrace,hout,hcalls,htime,hep,hcap,hdispatch⟩ :=
    initial_output_trace rows (ZeroLengthDispatch.iidProgram (k+1))
      (actualCodeHash (positiveSystem hD hd A k)) (positiveCircuits hD hd A k) service
      (rationalCellBudget a b) (rationalRepetitionBudget (2*((k+1)+1)) c d)
      omegaSeed density ext hboundary true
  refine ⟨final,totals,events,htrace,hout.1,?_,?_,?_⟩
  · simpa only [run,rawBitOutput,QuantumService.output_eq,LinearRepair.prepare,
      Array.toArray_toList,prepareRational,omegaSeed] using hout.2.2.2.1
  · simpa only [calls,rawBitOutput,QuantumService.output_eq,LinearRepair.prepare,
      prepareRational,omegaSeed] using hcalls
  · exact htime

/-- All supplied family/compiler/gate-bound premises of the source confidence
composition are discharged. One fixed A occurs before all input dimensions.
The actual stored finite word is preserved by the source loader, and the
physical optimum is outside the sole randomized approximation event. -/
theorem fixed_factory_dispatch_confidence
    {tapes : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine tapes Γ Λ} {density : ℕ}
    {Ptime Pspace : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT M density Ptime Pspace T) (hT : Monotone T)
    (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd' : 0<d) (hab : a≤b)
    (n : ℕ) (rows : List (List (PauliCoord n))) (lift : Lift (rowSpace rows)) :
    let S := positiveSystem hD hd A
    let K := positiveCircuits hD hd A
    let lengths := positiveLength hD hd A
    let widths := positiveWidth hD hd A
    (∀ w : RawInput lengths widths c d n,
      retainedFacts S K spec.service a b c d n rows w ∧
      calls S K spec.service a b c d n rows w≤callCap a b c d n ∧
      oracleTime S K spec.service a b c d n rows w≤
        timeCap Ptime T density (fun k => gateConstant hD hd A*keySize (k+1) (k+1)) a b c d n rows ∧
      ShapeStructure (rowSpace rows) (circuitMap (ZeroLengthDispatch.iidProgram n))
        (run S K spec.service a b c d n rows w).curve) ∧
    PhysicalTargetOptimality rows (ZeroLengthDispatch.iidProgram n) lift ∧
    1-(c:ℝ)/d≤(inputLaw lengths widths c d n).prob (fun w =>
      AllPhysicalTails rows (ZeroLengthDispatch.iidProgram n) lift ((a:ℝ)/b)
        (run S K spec.service a b c d n rows w).curve) := by
  exact engine_dispatch_shape_confidence (positiveSystem hD hd A) (positiveCircuits hD hd A)
    spec hT (fun k => gateConstant hD hd A*keySize (k+1) (k+1))
    (fun k scale seed => positiveCircuits_gates hD hd A k scale seed)
    a b c d ha hb hc hd' hab n rows lift

end QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
