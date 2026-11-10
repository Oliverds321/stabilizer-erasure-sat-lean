import ExternalSATCanonicalQueryBounds
import ExternalSATResourceTransport
import ResourceEncodedSAT

/-! Polynomial envelopes for the canonical frontend followed by the SAT engine.
The size parameter includes both the binary query and its ambient dimension. -/
namespace QecReliability.ExternalSATBridge.ConcreteSolver

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT

def pipelineEnvelope (overhead coefficient degree : ℕ) : PolynomialEnvelope :=
  ⟨overhead + coefficient * 65 ^ degree, max 5 (2 * degree)⟩

theorem encoding_power_bound (q : SATRequest) (degree : ℕ) :
    (Encoding.formulaBitLength (FormulaBridge.formula q.formula) + 1) ^ degree ≤
      65 ^ degree * (requestExtent q + 1) ^ (2 * degree) := by
  have hlength := CanonicalQueryBounds.canonical_length_le q
  change Encoding.formulaBitLength (FormulaBridge.formula q.formula) ≤
    64 * (requestExtent q + 1) ^ 2 at hlength
  have hpositive : 0 < (requestExtent q + 1) ^ 2 := by positivity
  have hbase : Encoding.formulaBitLength (FormulaBridge.formula q.formula) + 1 ≤
      65 * (requestExtent q + 1) ^ 2 := by omega
  have hpower := Nat.pow_le_pow_left hbase degree
  simpa only [mul_pow, ← pow_mul] using hpower

theorem pipelineEnvelope_bound (q : SATRequest) (overhead coefficient degree : ℕ) :
    overhead * (requestExtent q + 1) ^ 5 +
      coefficient * (Encoding.formulaBitLength (FormulaBridge.formula q.formula) + 1) ^ degree ≤
    (pipelineEnvelope overhead coefficient degree).eval (requestExtent q) := by
  have hfront : (requestExtent q + 1) ^ 5 ≤
      (requestExtent q + 1) ^ max 5 (2 * degree) :=
    pow_le_pow_right' (by omega) (Nat.le_max_left _ _)
  have hengine : (requestExtent q + 1) ^ (2 * degree) ≤
      (requestExtent q + 1) ^ max 5 (2 * degree) :=
    pow_le_pow_right' (by omega) (Nat.le_max_right _ _)
  have hpower := (encoding_power_bound q degree).trans
    (Nat.mul_le_mul_left (65 ^ degree) hengine)
  calc
    _ ≤ overhead * (requestExtent q + 1) ^ max 5 (2 * degree) +
        coefficient * (65 ^ degree * (requestExtent q + 1) ^ max 5 (2 * degree)) :=
      Nat.add_le_add (Nat.mul_le_mul_left overhead hfront)
        (Nat.mul_le_mul_left coefficient hpower)
    _ = _ := by simp only [pipelineEnvelope, PolynomialEnvelope.eval]; ring

end QecReliability.ExternalSATBridge.ConcreteSolver
