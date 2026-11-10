import WholeWrapperBroadContract
import WholeWrapperInputBounds

/-! Actual macro termination and unchanged output, together with representation
bounds derived from the actual encoded source. This joins proved traces and
proved reachable-state invariants; no whole-run or resource premise is added.
The macro primitive operations are NOT yet finite tape subroutines. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- The existing partial interpreter terminates with any fuel strictly above
an actual trace's dispatch count, when that trace ends at a genuine terminal
state. Fuel is derived from a trace, not assumed sufficient. -/
theorem Trace.drive_of_terminal {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t : Config} {totals : Totals} {events : List RequestKey}
    (h : Trace q r B m shape ext s totals events t)
    (ht : step q r B m shape ext t=none) :
    ∀ fuel, totals.dispatches<fuel → drive q r B m shape ext fuel s=some t := by
  induction h with
  | nil s =>
      intro fuel hf
      cases fuel with
      | zero => simp at hf
      | succ fuel => simp only [drive,ht]
  | @cons s edge t totals events he tail ih =>
      intro fuel hf
      cases fuel with
      | zero => simp at hf
      | succ fuel =>
          simp only [drive,he]
          exact ih ht fuel (by dsimp only [Totals.cons] at hf; omega)

/-- The literal initial controller halts and returns exactly the frozen source
cache, rational output, and report. Every reachable prefix, not merely the
final configuration, has degree-six represented storage in the genuine input
measure. Source SAT time is preserved linearly as an exact equality. Boundary
implementations, sampler/seed storage, input parsing, and bit-operation cost
remain separate physical obligations. -/
theorem initial_output_with_input_representation
    {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (a b c d : ℕ) (ha : 0<a) (hc : 0<c)
    (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω)
    (h D : ℕ) (shape : Bool) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service
      (rationalRepetitionBudget (2*(r+1)) c d) ω D ext)
    (hg : ∀ scale seed, (K.program scale seed).gates≤h*keySize n r) :
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    let cache := prepare rows C H K service.solver B m ω
    ∃ final totals events,
      Trace (keySize n r) r B m shape ext (initial (keySize n r) r m) totals events final ∧
      HasOutput final cache.good.entries cache.bad.entries
        (RationalOutput.LinearRepair.fromCache shape rows C cache) ∧
      drive (keySize n r) r B m shape ext
        (macroDispatchBound (keySize n r) r B m+1) (initial (keySize n r) r m)=some final ∧
      totals.calls=cache.calls ∧
      totals.oracleTime=(QuantumService.prepareMeasured rows C H K service B m ω).oracleTime ∧
      totals.endpointTime=(ext.endpoint false).time+(ext.endpoint true).time ∧
      totals.calls≤totalCallCap (keySize n r) r B m ∧
      totals.dispatches≤macroDispatchBound (keySize n r) r B m ∧
      (∀ s, Reachable (keySize n r) r B m shape ext s →
        (representedBits s).length≤InputEncoding.retainedPolynomial h D L) ∧
      (representedBits final).length≤InputEncoding.retainedPolynomial h D L ∧
      (InputEncoding.problemBits rows C a b c d).length+(representedBits final).length≤
        L+InputEncoding.retainedPolynomial h D L := by
  let B := rationalCellBudget a b
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let L := InputEncoding.paperLength rows C a b c d
  obtain ⟨final,totals,events,htrace,hout,hcalls,htime,hendpoint,hcap,hdispatch⟩ :=
    whole_output_refinement rows C H K service B m ω D shape ext hboundary
  have hterminal : step (keySize n r) r B m shape ext final=none := by
    simp only [step,hout.1]
  have hall : ∀ s, Reachable (keySize n r) r B m shape ext s →
      (representedBits s).length≤InputEncoding.retainedPolynomial h D L := by
    intro s hs
    exact InputEncoding.reachable_input_representation rows C H K service
      a b c d ha hc ω h D shape ext hboundary hg hs
  have hfinal := hall final ⟨totals,events,htrace⟩
  refine ⟨final,totals,events,htrace,hout,?_,hcalls,htime,hendpoint,hcap,hdispatch,hall,hfinal,?_⟩
  · exact htrace.drive_of_terminal hterminal _ (Nat.lt_succ_of_le hdispatch)
  · have hinput : (InputEncoding.problemBits rows C a b c d).length≤L := by
      dsimp only [L,InputEncoding.paperLength]
      omega
    exact Nat.add_le_add hinput hfinal

end QecReliability.OracleCost.WholeWrapperCandidate
