import PhysicalBridge.ChannelSums

/-! A CPTP left inverse for every finite-dimensional isometry, completed on
the entire physical output using an explicit trace-and-prepare branch. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators
open Matrix
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] [Nonempty a]

def fillChannel : Channel b a :=
  (basisPreparation (Classical.choice (inferInstance : Nonempty a))).comp completeErasure

def isometryComplement (V : Matrix b a ℂ) : Square b := 1 - V*Vᴴ

omit [Fintype b] [DecidableEq a] [Nonempty a] in
theorem isometryComplement_hermitian (V : Matrix b a ℂ) : (isometryComplement V).IsHermitian := by
  change (isometryComplement V)ᴴ = isometryComplement V
  simp [isometryComplement, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]

omit [Nonempty a] in
theorem isometryComplement_idempotent (V : Matrix b a ℂ) (hV : Vᴴ*V=1) :
    isometryComplement V * isometryComplement V = isometryComplement V := by
  have hp : (V*Vᴴ)*(V*Vᴴ)=V*Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  unfold isometryComplement
  noncomm_ring [hp]

omit [Nonempty a] in
theorem isometryComplement_mul (V : Matrix b a ℂ) (hV : Vᴴ*V=1) :
    isometryComplement V * V = 0 := by
  rw [isometryComplement, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]

def isometryDecoder (V : Matrix b a ℂ) (hV : Vᴴ*V=1) : Channel b a where
  map := conjugateMap Vᴴ + fillChannel.map.comp (conjugateMap (isometryComplement V))
  completelyPositive := completelyPositive_add _ _ (conjugateMap_cp _) (
    completelyPositive_comp _ _ (conjugateMap_cp _) fillChannel.completelyPositive)
  tracePreserving X := by
    rw [LinearMap.add_apply]
    change (Vᴴ*X*(Vᴴ)ᴴ + fillChannel.map (isometryComplement V * X * (isometryComplement V)ᴴ)).trace = X.trace
    rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_add, fillChannel.tracePreserving, (isometryComplement_hermitian V).eq,
      Matrix.trace_mul_cycle, Matrix.trace_mul_cycle (isometryComplement V),
      isometryComplement_idempotent V hV, ← Matrix.trace_add, ← Matrix.add_mul]
    simp [isometryComplement]

theorem isometryDecoder_left_inverse (V : Matrix b a ℂ) (hV : Vᴴ*V=1) :
    (isometryDecoder V hV).map.comp (conjugateMap V) = LinearMap.id := by
  change (conjugateMap Vᴴ + fillChannel.map.comp (conjugateMap (isometryComplement V))).comp
    (conjugateMap V) = _
  simp only [LinearMap.add_comp, LinearMap.comp_assoc, conjugateMap_comp,
    isometryComplement_mul V hV, conjugateMap_zero, LinearMap.comp_zero, add_zero, hV]
  ext X i j
  simp [conjugateMap]

end QecPhysical
