import OracleCost.EncodedSAT
import OracleCost.PrefixEmissions
import OracleCost.PrefixExecution

/-! Explicit finite prefix-controller executions with their emitted serialized
SAT invocations. Every emitted request is in the canonical density domain and
has an actual finite run of the same fixed engine. The emitted history is ghost
data only. Calls start from the standard fresh input configuration; realizing
successive fresh starts on reused private tapes remains a separate reset proof.
The controller steps and serializer are still macros, not unit bit operations.
-/
namespace QecReliability.OracleCost.PrefixSAT
open PrefixEnumeration PrefixCNF MultiTape PrefixTransitions

variable {q w k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine k Γ Λ} {D : ℕ} {Ptime Pspace : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT M D Ptime Pspace T)
    (F : Formula (q+w)) (hF : Width 3 F)

def engineVars (D : ℕ) : ℕ := max (q+w) (D*(F.length+q))

def engineBits (D : ℕ) : ℕ := QueryCodec.sizeBound (engineVars F D) (F.length+q)

theorem generated_bounds (pre : List Bool) (hp : pre.length≤q) :
    CanonicalDensityInput D (QueryCodec.encode (padRequest D (request F hF pre))) ∧
    (padRequest D (request F hF pre)).varCount≤engineVars F D ∧
    (QueryCodec.encode (padRequest D (request F hF pre))).length≤engineBits F D := by
  have hd := request_dimensions F hF pre hp
  exact ⟨padRequest_canonical _ _,padRequest_size _ hd.1.le hd.2.2⟩

theorem engine_time_bound (hT : Monotone T) (cap : ℕ) :
    (measured spec.service F hF cap).oracleTime≤
      (1+2*q*cap)*Ptime.eval (engineBits F D)*T (engineVars F D) := by
  have hcharge : ∀ pre : List Bool, pre.length≤q →
      (spec.service.run (request F hF pre)).time≤
        Ptime.eval (engineBits F D)*T (engineVars F D) := by
    intro pre hp
    have hd := request_dimensions F hF pre hp
    exact (spec.request_bounds hT _ _ _ hd.1.le hd.2.2).1
  have ht := PrefixControl.oracleTime_le q (decision spec.service F hF).answer
    (fun pre => (spec.service.run (request F hF pre)).time) cap _ hcharge
  have hc := (structural_bounds spec.service F hF cap).1
  change (measured spec.service F hF cap).oracleTime≤
    (measured spec.service F hF cap).calls*
      (Ptime.eval (engineBits F D)*T (engineVars F D)) at ht
  exact ht.trans (by
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_right (Ptime.eval (engineBits F D)*T (engineVars F D)) hc)

/-- Total finite execution, exact projected count, exact emitted-call count,
and the sum of actual engine-run times. No terminating-run premise, assumed
success event, or non-exact-oracle polynomial call bound is used. -/
theorem serialized_run (hT : Monotone T) (cap : ℕ) :
    ∃ (result : RunResult) (requests : List (List Bool)),
      PrefixTransitions.run q (fun pre => spec.service.run (request F hF pre)) cap=some result ∧
      result.final=⟨.ret (min cap (modelCount (Projected F))),[]⟩ ∧
      EmissionTrace (fun pre => spec.service.run (request F hF pre))
        ⟨.enter q [] cap,[]⟩ result.steps requests result.final ∧
      requests.length=result.calls ∧
      (requests.map (fun pre => (spec.run (request F hF pre)).time)).sum=result.serviceTime ∧
      result.calls≤1+2*q*cap ∧ result.steps≤5*(1+2*q*cap)+1 ∧
      result.serviceTime≤(1+2*q*cap)*Ptime.eval (engineBits F D)*T (engineVars F D) ∧
      ∀ pre∈requests, pre.length≤q ∧
        CanonicalDensityInput D (QueryCodec.encode (padRequest D (request F hF pre))) ∧
        (QueryCodec.encode (padRequest D (request F hF pre))).length≤engineBits F D ∧
        ∃ engineRun : Completed M (QueryCodec.encode (padRequest D (request F hF pre))),
          engineRun.output=(spec.service.run (request F hF pre)).value ∧
          engineRun.time=(spec.service.run (request F hF pre)).time ∧
          engineRun.cells≤Pspace.eval (engineBits F D) := by
  obtain ⟨result,hr,hfinal,hcalls,htime,hsteps⟩ :=
    PrefixTransitions.run_spec q (fun pre => spec.service.run (request F hF pre)) cap
  have heq := execute_control spec.service F hF cap
  change (PrefixMachine.execute q (fun pre => spec.service.run (request F hF pre)) [] cap).control=
    measured spec.service F hF cap at heq
  rw [heq] at hfinal hcalls htime
  have hcount := (exact_count spec.service F hF cap).1
  rw [hcount] at hfinal
  have hcalls' : result.calls≤1+2*q*cap := by
    rw [hcalls]; exact (structural_bounds spec.service F hF cap).1
  have htrace := (drive_trace hr).1
  obtain ⟨requests,hemitted,hlen,hsum⟩ := htrace.emissions
  refine ⟨result,requests,hr,hfinal,hemitted,hlen,hsum,hcalls',by omega,?_,?_⟩
  · rw [htime]
    exact engine_time_bound spec F hF hT cap
  · intro pre hp
    have plen := hemitted.valid_prefixes (initial_valid q cap) pre hp
    have hb := generated_bounds F hF pre plen (D:=D)
    refine ⟨plen,hb.1,hb.2.2,spec.run (request F hF pre),rfl,rfl,?_⟩
    exact (spec.run_spec _).2.2.trans (Pspace.monotone hb.2.2)

end QecReliability.OracleCost.PrefixSAT
