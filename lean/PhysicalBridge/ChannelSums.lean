import PhysicalBridge.EncodedNormalizerNoise

/-! Completely positive finite sums and a globally trace-preserving
projective recovery instrument with arbitrary CPTP branch recoveries. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder
open Matrix
variable {a b c ι : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype ι]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

omit [DecidableEq a] [DecidableEq b] in
theorem completelyPositive_add (Φ Ψ : MatrixMap a b) (hΦ : IsCompletelyPositive Φ)
    (hΨ : IsCompletelyPositive Ψ) : IsCompletelyPositive (Φ+Ψ) := by
  intro k X hX
  change (amplify Φ X + amplify Ψ X).PosSemidef
  exact (hΦ k X hX).add (hΨ k X hX)

omit [DecidableEq a] [DecidableEq b] in
theorem completelyPositive_sum (Φ : ι → MatrixMap a b)
    (hΦ : ∀ i, IsCompletelyPositive (Φ i)) : IsCompletelyPositive (∑ i, Φ i) := by
  intro k X hX
  have h : amplify (∑ i, Φ i) X = ∑ i, amplify (Φ i) X := by
    ext x y
    simp [amplify, Matrix.sum_apply]
  rw [h]
  exact posSemidef_sum _ (fun i => hΦ i k X hX)

omit [DecidableEq a] [DecidableEq b] [DecidableEq c] in
theorem completelyPositive_comp (Φ : MatrixMap a b) (Ψ : MatrixMap b c)
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (Ψ.comp Φ) := by
  intro k X hX
  rw [amplify_comp]
  exact hΨ k _ (hΦ k X hX)

def projectiveRecovery (P : ι → Square b) (hP : ∑ i, (P i)ᴴ * P i = 1)
    (R : ι → Channel b a) : Channel b a where
  map := ∑ i, (R i).map.comp (conjugateMap (P i))
  completelyPositive := completelyPositive_sum _ (fun i =>
    completelyPositive_comp _ _ (conjugateMap_cp _) (R i).completelyPositive)
  tracePreserving X := by
    rw [LinearMap.sum_apply]
    change (∑ i, (R i).map (conjugateMap (P i) X)).trace = X.trace
    rw [Matrix.trace_sum]
    have ht (i : ι) := (R i).tracePreserving (conjugateMap (P i) X)
    simp_rw [ht]
    simpa only [krausMap, LinearMap.sum_apply, Matrix.trace_sum] using krausMap_trace P hP X

omit [Fintype b] [DecidableEq a] [DecidableEq b] in
theorem conjugateMap_zero : conjugateMap (0 : Matrix b a ℂ) = 0 := by
  ext X i j
  simp [conjugateMap]

omit [DecidableEq a] [DecidableEq c] in
theorem projectiveRecovery_branch [DecidableEq ι]
    (P : ι → Square b) (hP : ∑ i, (P i)ᴴ * P i = 1) (R : ι → Channel b a)
    (i : ι) (W : Matrix b c ℂ)
    (hW : ∀ j, P j * W = if j=i then W else 0) :
    (projectiveRecovery P hP R).map.comp (conjugateMap W) =
      (R i).map.comp (conjugateMap W) := by
  change (∑ j, (R j).map.comp (conjugateMap (P j))).comp (conjugateMap W) = _
  have hs : (∑ j, (R j).map.comp (conjugateMap (P j))).comp (conjugateMap W) =
      ∑ j, ((R j).map.comp (conjugateMap (P j))).comp (conjugateMap W) := by
    ext X u v
    simp
  rw [hs]
  have ht (j : ι) : ((R j).map.comp (conjugateMap (P j))).comp (conjugateMap W) =
      if j=i then (R i).map.comp (conjugateMap W) else 0 := by
    rw [LinearMap.comp_assoc, conjugateMap_comp, hW]
    by_cases h : j=i
    · simp [h]
    · simp [h, conjugateMap_zero]
  simp_rw [ht]
  simp

end QecPhysical
