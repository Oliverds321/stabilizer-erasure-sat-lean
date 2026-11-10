import LatentResourceRuntime
import LatentFactoryResourceBounds
import Final.Macro
import Assembly.Loop

/-! Discharged fault-freedom and actual stored-query oracle facts for register
assembly. The oracle cost includes real time PLUS visited cells for cleanup;
only the latter is absorbed into the per-iteration polynomial. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

/-- An actual trace ending done cannot start fault, for either repair mode. -/
theorem trace_ne_fault {q r B m : ℕ} {shape : Bool} {ext : External}
    {s final : Config} {totals : Totals} {events : List RequestKey}
    (h : Trace q r B m shape ext s totals events final) (hd : final.pc = .done) :
    s.pc ≠ .fault := by
  intro hf
  cases h with
  | nil => have hh := hf.symm.trans hd; cases hh
  | cons he _ => simp only [WholeWrapperCandidate.step,hf] at he; contradiction

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}

/-- Fault exclusion follows from the actual terminal trace, not a new invariant premise. -/
theorem resource_reachable_ne_fault {resource : SATRequest → ℕ}
    (spec : ResourceEncodedSAT E density PtE PsE T resource)
    {n r : ℕ} (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (B m : ℕ) (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) m) → Bool) {s : Config}
    (hs : Reachable (keySize n r) r B m false
      (resourceExternal hD hd A density spec rows C m coins) s) : s.pc ≠ .fault := by
  obtain ⟨final,totals,events,htrace,hout,_,_,_,_,_⟩ :=
    resource_macro_output hD hd A density spec rows C B m coins
  obtain ⟨ts,es,hprefix⟩ := hs
  obtain ⟨_,_,hrest⟩ := Final.trace_reaches_terminal hprefix htrace
    (Assembly.step_eq_none_of_done hout.1)
  exact trace_ne_fault hrest hout.1

/-- Actual retained query, actual E reply, and cleanup-aware oracle cost. The
positive latent branch alone needs the linear-in-q hash gate bound. -/
theorem resource_invoke_correct
    (spec : ResourceEncodedSAT E density PtE PsE T requestExtent)
    {n r : ℕ} (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (hr : 0<r) (B m a b c d : ℕ)
    (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) m) → Bool) {s : Config}
    (hs : Reachable (keySize n r) r B m false
      (resourceExternal hD hd A density spec rows C m coins) s) (hpc : s.pc = .invoke) :
    let cap := InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density
      (InputEncoding.paperLength rows C a b c d)
    let O := RegMachine.resourceSatOracle E density requestExtent cap
    O.qok s.query ∧
    O.oracle s.query = ((resourceExternal hD hd A density spec rows C m coins).sat s.query).value ∧
    O.ocost s.query ≤ ((resourceExternal hD hd A density spec rows C m coins).sat s.query).time+
      PsE.eval cap := by
  let cap := InputEncoding.queryExtentPolynomial (gateConstant hD hd A) density
    (InputEncoding.paperLength rows C a b c d)
  let O := RegMachine.resourceSatOracle E density requestExtent cap
  have hk := (reachable_request_invariant hs).request
  have hq := Final.reachable_invoke_query hs hpc
  change s.query = Final.concreteQuery rows C (actualCodeHash (Factory.system hD hd A n r))
    (Factory.circuits hD hd A n r) m
    (decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins) density s.request at hq
  have hok : O.qok s.query := by
    rw [hq]
    exact Factory.concreteQuery_resource_qok hD hd A E rows C hr m coins a b c d density s.request hk
  have hpadded : Final.IsPaddedQuery density s.query := by
    rw [hq]
    exact Final.concreteQuery_padded rows C _ _ m _ density s.request hk
  obtain ⟨run,hanswer,_,hcells⟩ := RegMachine.resourceSatOracle_realizes spec cap s.query hok
  have hrun := RegMachine.resourceSatOracle_run E density requestExtent cap run
  have hobs := Final.Resource.satReply_of_completed spec hpadded run
  refine ⟨hok,?_,?_⟩
  · change O.oracle s.query = (Final.Resource.satReply spec s.query).value
    exact hanswer.symm.trans hobs.1.symm
  · change O.ocost s.query ≤ (Final.Resource.satReply spec s.query).time+PsE.eval cap
    rw [hrun.2,hobs.2.1]
    exact Nat.add_le_add_left hcells _

end QecReliability.LatentMachine.Runtime
