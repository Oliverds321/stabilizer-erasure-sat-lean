import ExternalSATObservedTransport
import ExternalSATRuntimeEnvelope
import OAI.Algorithms.SubexponentialSAT.SqrtLog.StatementScale

/-! Per-run resource conversion against the real external numerical definition.
No algorithm-existence axiom is introduced: the caller supplies an actual
external located trace and its proved bounds. Final.lean is not imported here.
This is still same-word transport, not binary-query preprocessing. -/
namespace QecReliability.ExternalSATBridge.PrimitiveTransport

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

@[simp] theorem external_runtimeScale_eq (n : ℕ) :
    SqrtLog.Statement.runtimeScale n = RateMajorant.runtimeScale n := rfl

theorem external_rate_dominated (A : ℝ) {n v : ℕ} (hnv : n ≤ v) :
    (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n) ≤
      (RateMajorant.runtimeEnvelope A v : ℝ) := by
  rw [external_runtimeScale_eq]
  exact RateMajorant.runtimeEnvelope_dominates A hnv

/-- Natural constants absorb the single halt inspection and single idle cell.
The scale envelope is the checked natural monotone hull, not a hypothesis
about monotonicity of the raw external logarithmic expression. -/
theorem same_word_resources (M : Computation.PrimitiveMachine) (bits : List Bool)
    (answer : Bool) (steps n v d e : ℕ) (C A S : ℝ)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hnv : n ≤ v) (final : LocatedCfg M)
    (tr : Computation.Trace (locatedStep M) steps (locatedInit M bits) final)
    (halt : final.config.state = .inl answer)
    (htime : (steps : ℝ) ≤ SqrtLog.Statement.runtimeBound C A d bits.length n)
    (hspace : (visitedSpace final : ℝ) ≤ S * ((bits.length : ℝ) + 1) ^ e) :
    ∃ run : MultiTape.Completed (machine M) bits,
      run.output = answer ∧
      run.time ≤ (Nat.ceil C + 1) * (bits.length + 1) ^ d *
        RateMajorant.runtimeEnvelope A v ∧
      run.cells ≤ (Nat.ceil S + 1) * (bits.length + 1) ^ e := by
  obtain ⟨run, hout, htimeEq, hcells⟩ := completed_run M bits answer steps final tr halt
  have hrate := external_rate_dominated A hnv
  have hCp :
      C * ((bits.length : ℝ) + 1) ^ d ≤
        (Nat.ceil C : ℝ) * ((bits.length : ℝ) + 1) ^ d :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity)
  have htReal : (steps : ℝ) ≤
      (Nat.ceil C : ℝ) * ((bits.length : ℝ) + 1) ^ d *
        (RateMajorant.runtimeEnvelope A v : ℝ) := by
    exact htime.trans (mul_le_mul hCp hrate (by positivity) (by positivity))
  have htNat : steps ≤ Nat.ceil C * (bits.length + 1) ^ d *
      RateMajorant.runtimeEnvelope A v := by
    exact_mod_cast htReal
  have hsReal : (visitedSpace final : ℝ) ≤
      (Nat.ceil S : ℝ) * ((bits.length : ℝ) + 1) ^ e :=
    hspace.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil S) (by positivity))
  have hsNat : visitedSpace final ≤ Nat.ceil S * (bits.length + 1) ^ e := by
    exact_mod_cast hsReal
  have hpTime : 1 ≤ (bits.length + 1) ^ d * RateMajorant.runtimeEnvelope A v := by
    have hp : 0 < (bits.length + 1) ^ d := by positivity
    exact Nat.succ_le_of_lt (Nat.mul_pos hp (RateMajorant.runtimeEnvelope_pos A v))
  have hpSpace : 1 ≤ (bits.length + 1) ^ e :=
    Nat.succ_le_of_lt (by positivity : 0 < (bits.length + 1) ^ e)
  refine ⟨run, hout, ?_, ?_⟩
  · rw [htimeEq]
    calc
      steps + 1 ≤ Nat.ceil C * (bits.length + 1) ^ d * RateMajorant.runtimeEnvelope A v +
          (bits.length + 1) ^ d * RateMajorant.runtimeEnvelope A v :=
        Nat.add_le_add htNat hpTime
      _ = (Nat.ceil C + 1) * (bits.length + 1) ^ d * RateMajorant.runtimeEnvelope A v := by ring
  · calc
      run.cells ≤ visitedSpace final + 1 := hcells
      _ ≤ Nat.ceil S * (bits.length + 1) ^ e + (bits.length + 1) ^ e :=
        Nat.add_le_add hsNat hpSpace
      _ = (Nat.ceil S + 1) * (bits.length + 1) ^ e := by ring

end QecReliability.ExternalSATBridge.PrimitiveTransport
