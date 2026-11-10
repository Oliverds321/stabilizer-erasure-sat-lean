import PhysicalBridge.BellFidelity

/-! Range of the actual Bell overlap for every all-ancilla CPTP channel. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder
open Matrix
variable {a : Type*} [Fintype a] [DecidableEq a]

omit [DecidableEq a] in
theorem trace_mul_projection_nonneg (X P : Square a) (hX : X.PosSemidef)
    (hP : P.IsHermitian) (hPP : P * P = P) : 0 ≤ (X * P).trace := by
  have h := (hX.conjTranspose_mul_mul_same P).trace_nonneg
  rw [hP.eq, Matrix.trace_mul_cycle, hPP, Matrix.trace_mul_comm] at h
  exact h

theorem projection_complement_idempotent (P : Square a) (hP : P * P = P) :
    (1-P) * (1-P) = 1-P := by
  calc
    (1-P) * (1-P) = 1-P-P+P*P := by noncomm_ring
    _ = 1-P := by rw [hP]; abel

theorem trace_mul_projection_le_one (X P : Square a) (hX : X.PosSemidef)
    (htr : X.trace = 1) (hP : P.IsHermitian) (hPP : P * P = P) :
    (X * P).trace.re ≤ 1 := by
  have h := trace_mul_projection_nonneg X (1-P) hX
    (Matrix.isHermitian_one.sub hP) (projection_complement_idempotent P hPP)
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, htr] at h
  have hr := h.1
  change 0 ≤ 1 - (X * P).trace.re at hr
  linarith

/-- The overlap is a probability for every CPTP map, with no Kraus hypothesis. -/
theorem entanglementFidelity_bounds [Nonempty a] (Φ : Channel a a) :
    0 ≤ entanglementFidelity Φ.map ∧ entanglementFidelity Φ.map ≤ 1 := by
  have hX := IsCompletelyPositive.amplify_pos Φ.map Φ.completelyPositive
    (bellProjector a) bellProjector_posSemidef
  have ht : (amplify Φ.map (bellProjector a)).trace = 1 := by
    rw [IsTracePreserving.amplify_trace Φ.map Φ.tracePreserving, bellProjector_trace]
  exact ⟨(trace_mul_projection_nonneg _ _ hX bellProjector_posSemidef.isHermitian
      bellProjector_idempotent).1,
    trace_mul_projection_le_one _ _ hX ht bellProjector_posSemidef.isHermitian
      bellProjector_idempotent⟩

end QecPhysical
