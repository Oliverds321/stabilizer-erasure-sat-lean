import LatentRuntimeAgreement
import WholeWrapperInputRun

/-! Actual false-mode macro termination/output and reachable installed-step
agreement. No sufficient-fuel or external agreement premise is assumed. Macro
edge counts are not bit time or visited-tape cells. The separate r=0 initializer
short-circuits to exact rank; this generic macro theorem itself admits all n,r,
including q=0 and q=1, without the iid dispatch-bound shortcut. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : EncodedSAT E density PtE PsE T)
  {n r : ℕ} (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
  (B m : ℕ) (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
    (Factory.width hD hd A n r) m) → Bool)

local notation "EXT" => external hD hd A density spec rows C m coins
local notation "HH" => actualCodeHash (Factory.system hD hd A n r)
local notation "KK" => Factory.circuits hD hd A n r
local notation "SS" => decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins
local notation "CX" => controller hD hd A density
local notation "XX" => contextData hD hd A rows C m coins

theorem reachable_agreement {s : Config}
    (hs : Reachable (keySize n r) r B m false EXT s) : ExtAgrees CX XX EXT s :=
  extAgrees hD hd A density spec rows C m coins s (reachable_request_invariant hs).request

/-- Every reachable non-invocation edge is the actual installed false step. -/
theorem reachable_step {s : Config} (hs : Reachable (keySize n r) r B m false EXT s)
    (hn : s.pc ≠ .invoke) (e : Edge)
    (he : WholeWrapperCandidate.step (keySize n r) r B m false EXT s = some e) :
    (EndpointControllerFL.stepF CX).den (encCtx (keySize n r) r B m XX,encCfg s) =
      (encCtx (keySize n r) r B m XX,encCfg e.next) :=
  EndpointControllerFL.step_correct CX (keySize n r) r B m XX EXT s hn
    (reachable_agreement hD hd A density spec rows C B m coins hs) e he

/-- Macro trace, exact cached output, exact calls and oracle time, and sufficient
fuel derived from the trace. Both tails and every latent tuple are unchanged. -/
theorem macro_output :
    let cache := prepare rows C HH KK spec.service.solver B m SS
    ∃ final totals events,
      Trace (keySize n r) r B m false EXT (initial (keySize n r) r m) totals events final ∧
      HasOutput final cache.good.entries cache.bad.entries
        (RationalOutput.LinearRepair.fromCache false rows C cache) ∧
      drive (keySize n r) r B m false EXT
        (macroDispatchBound (keySize n r) r B m+1) (initial (keySize n r) r m) = some final ∧
      totals.calls = cache.calls ∧
      totals.oracleTime = (QuantumService.prepareMeasured rows C HH KK spec.service B m SS).oracleTime ∧
      totals.calls ≤ totalCallCap (keySize n r) r B m ∧
      totals.dispatches ≤ macroDispatchBound (keySize n r) r B m := by
  have hb : BoundaryCorrect rows C HH KK spec.service m SS density EXT :=
    Final.concreteExternal_boundary rows C HH KK m SS density spec
  obtain ⟨final,totals,events,htrace,hout,hcalls,htime,_,hcap,hdispatch⟩ :=
    whole_output_refinement rows C HH KK spec.service B m SS density false EXT hb
  refine ⟨final,totals,events,htrace,hout,?_,hcalls,htime,hcap,hdispatch⟩
  apply htrace.drive_of_terminal
  · simp only [WholeWrapperCandidate.step,hout.1]
  · exact Nat.lt_succ_of_le hdispatch

end QecReliability.LatentMachine.Runtime
