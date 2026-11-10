import WholeWrapperRepresentation

/-! Every declaration ending `Claim` below is a named PROPOSITION,
not a theorem, not a postulate, and not an instance asserted to exist. These
make the exact remaining obligations auditable rather than hiding them in an
opaque `wrapperTime` hypothesis. No `Claim` is used to claim completion. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput PrefixEnumeration MultiTape

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))
    (service : SATService) (B m : ℕ) (ω : Fin (2*m+1) → Ω)

def ValidKey (q r m : ℕ) : RequestKey → Prop
  | .base _ j rep => j<r+1 ∧ rep<2*m+1
  | .cell _ j rep scale pre =>
      j<r+1 ∧ rep<2*m+1 ∧ scale<q+1 ∧ pre.length≤q

/-- The precise query target is the existing concrete quantum request; no
new encoder/CNF, surrogate counting predicate, or alternate hash is inserted. -/
def resolveRequest (key : RequestKey)
    (valid : ValidKey (keySize n r) r m key) : SATRequest :=
  match key with
  | .base side j _ =>
      QuantumService.baseRequest rows C (side,⟨j,valid.1⟩) []
  | .cell side j rep scale pre =>
      QuantumService.cellRequest rows C H K (side,⟨j,valid.1⟩)
        ⟨scale,valid.2.2.1⟩ (ω ⟨rep,valid.2.1⟩) pre

/-- Semantic boundary fidelity; this alone supplies NO runtime bound. -/
structure BoundaryCorrect (D : ℕ) (ext : External) : Prop where
  query : ∀ key valid,
    (ext.compileQuery key).bits=
      QueryCodec.encode (padRequest D (resolveRequest rows C H K m ω key valid))
  answer : ∀ key valid,
    ext.sat (ext.compileQuery key).bits=
      service.run (resolveRequest rows C H K m ω key valid)
  endpoint0 : (ext.endpoint false).value=Ratio.dyadic rows (circuitMap C ∅)
  endpoint1 : (ext.endpoint true).value=Ratio.dyadic rows (circuitMap C Finset.univ)

/-- A prefix request sequence must be emitted by the existing operational
prefix controller, ending at its existing recursive evaluator's result. -/
def SourceCellEvents (side : Bool) (j : Fin (r+1)) (rep : Fin (2*m+1))
    (scale : Fin (keySize n r+1)) (prefixes : List (List Bool)) : Prop :=
  let oracle := fun pre => service.run (QuantumService.cellRequest rows C H K
    (side,j) scale (ω rep) pre)
  ∃ steps, PrefixTransitions.EmissionTrace oracle
    ⟨.enter (keySize n r) [] (4*B+1),[]⟩ steps prefixes
    ⟨.ret (PrefixMachine.execute (keySize n r) oracle [] (4*B+1)).control.count,[]⟩

/-- All q+1 scales occur in increasing order on the true branch. The finite
function here is a GHOST family of traces, not a runtime table or callback. -/
def SourceTrialEvents (side : Bool) (j : Fin (r+1)) (rep : Fin (2*m+1))
    (events : List RequestKey) : Prop :=
  if (service.run (QuantumService.baseRequest rows C (side,j) [])).value then
    ∃ prefixes : Fin (keySize n r+1) → List (List Bool),
      (∀ scale, SourceCellEvents rows C H K service B m ω side j rep scale (prefixes scale)) ∧
      events=RequestKey.base side j.val rep.val ::
        (List.ofFn (fun scale => (prefixes scale).map
          (RequestKey.cell side j.val rep.val scale.val))).flatten
  else events=[RequestKey.base side j.val rep.val]

def SourceCoefficientEvents (side : Bool) (j : Fin (r+1))
    (events : List RequestKey) : Prop :=
  ∃ trials : Fin (2*m+1) → List RequestKey,
    (∀ rep, SourceTrialEvents rows C H K service B m ω side j rep (trials rep)) ∧
    events=(List.ofFn trials).flatten

/-- Same chosen logical materialization order as the source's two CountTable.builds:
good j ascending, bad j ascending; each coefficient's odd repetitions ascending.
Pure source terms do not themselves assert a native language evaluation order. -/
def SourceWholeEvents (events : List RequestKey) : Prop :=
  ∃ good bad : Fin (r+1) → List RequestKey,
    (∀ j, SourceCoefficientEvents rows C H K service B m ω true j (good j)) ∧
    (∀ j, SourceCoefficientEvents rows C H K service B m ω false j (bad j)) ∧
    events=(List.ofFn good).flatten++(List.ofFn bad).flatten

/-- OPEN: simultaneous full controller trace, exact old prepared cache,
exact source repair INCLUDING REPORT, same logical call order, exact call total,
exact measured service time, and a polynomial control-dispatch bound. -/
def WholeRefinementClaim (D : ℕ) (shape : Bool) (ext : External) : Prop :=
  BoundaryCorrect rows C H K service m ω D ext →
  ∃ final totals events,
    Trace (keySize n r) r B m shape ext (initial (keySize n r) r m) totals events final ∧
    HasOutput final
      (prepare rows C H K service.solver B m ω).good.entries
      (prepare rows C H K service.solver B m ω).bad.entries
      (LinearRepair.fromCache shape rows C (prepare rows C H K service.solver B m ω)) ∧
    SourceWholeEvents rows C H K service B m ω events ∧
    totals.calls=(prepare rows C H K service.solver B m ω).calls ∧
    totals.oracleTime=(QuantumService.prepareMeasured rows C H K service B m ω).oracleTime ∧
    totals.calls≤totalCallCap (keySize n r) r B m ∧
    totals.dispatches≤dispatchBound (keySize n r) r B m

/-- OPEN: retained-state bounds at EVERY intermediate control state, not
merely a payload bound on the final answer. `V` may be exponentially large,
provided its bit length is polynomial; T must never enter this state bound. -/
def ReachableRepresentationClaim (D Q Kfields L V : ℕ) (shape : Bool) (ext : External) : Prop :=
  BoundaryCorrect rows C H K service m ω D ext →
  ∀ state totals events,
    Trace (keySize n r) r B m shape ext (initial (keySize n r) r m) totals events state →
    RepresentationInvariant (keySize n r) B Q Kfields L V state

/-- This equality bridge uses the actual
adapter; it adds NO runtime theorem. The same cache, not a new estimator, is
what the physical-confidence statement observes. -/
theorem source_output_eq (shape : Bool) (a b c d : ℕ)
    (seeds : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω) :
    QuantumService.output rows C H K service shape a b c d seeds=
      LinearRepair.prepare shape rows C H K service.solver a b c d seeds :=
  QuantumService.output_eq rows C H K service shape a b c d seeds

/-- Existing finite SAT-engine executions are reusable; this is NOT a wrapper
simulation theorem and does NOT establish reset/fresh-start composition. -/
theorem encoded_service_realizes
    {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine k Γ Λ} {D : ℕ} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT M D Pt Ps T) (request : SATRequest) :
    ∃ run : Completed M (QueryCodec.encode (padRequest D request)),
      run.output=(spec.service.run request).value ∧
      run.time=(spec.service.run request).time ∧
      machineCellBits Γ*run.cells+machineControlBits Λ=(spec.service.run request).workspace :=
  spec.realizes request

end QecReliability.OracleCost.WholeWrapperCandidate
