import PhysicalBridge.BellFidelity

-- Retain matrix/function coercion reduction for the original proofs.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Finite Kraus representations: channel construction and fidelity formula.
This file does not assert that every CPTP map has such a representation. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder
open Matrix
variable {a b ι : Type*} [Fintype a] [Fintype b] [Fintype ι]
  [DecidableEq a] [DecidableEq b]

def krausMap (K : ι → Matrix b a ℂ) : MatrixMap a b := ∑ t, conjugateMap (K t)

omit [Fintype b] [DecidableEq a] [DecidableEq b] in
theorem krausMap_apply (K : ι → Matrix b a ℂ) (X : Square a) :
    krausMap K X = ∑ t, K t * X * (K t)ᴴ := by
  simp [krausMap, conjugateMap]

omit [Fintype b] [DecidableEq a] [DecidableEq b] in
theorem amplify_krausMap {r : Type*} [Fintype r] (K : ι → Matrix b a ℂ)
    (X : Square (r × a)) :
    amplify (krausMap K) X = ∑ t, amplify (conjugateMap (K t)) X := by
  ext p q
  simp [amplify, krausMap, Matrix.sum_apply]

omit [DecidableEq a] [DecidableEq b] in
theorem krausMap_cp (K : ι → Matrix b a ℂ) : IsCompletelyPositive (krausMap K) := by
  intro k X hX
  rw [amplify_krausMap]
  exact posSemidef_sum _ (fun t => conjugateMap_cp (K t) k X hX)

omit [DecidableEq b] in
theorem krausMap_trace (K : ι → Matrix b a ℂ) (hK : ∑ t, (K t)ᴴ * K t = 1) :
    IsTracePreserving (krausMap K) := by
  intro X
  rw [krausMap_apply, Matrix.trace_sum]
  calc
    (∑ t, (K t * X * (K t)ᴴ).trace) = ∑ t, ((K t)ᴴ * K t * X).trace := by
      apply Finset.sum_congr rfl
      intro t _
      exact Matrix.trace_mul_cycle _ _ _
    _ = X.trace := by rw [← Matrix.trace_sum, ← Matrix.sum_mul, hK, Matrix.one_mul]

def krausChannel (K : ι → Matrix b a ℂ) (hK : ∑ t, (K t)ᴴ * K t = 1) : Channel a b where
  map := krausMap K
  completelyPositive := krausMap_cp K
  tracePreserving := krausMap_trace K hK

theorem conjugateMap_single (K : Square a) (i j : a) :
    conjugateMap K (Matrix.single i j 1) i j = K i i * star (K j j) := by
  simp [conjugateMap, Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, ite_and]

theorem entanglementFidelity_conjugate (K : Square a) :
    entanglementFidelity (conjugateMap K) =
      (Fintype.card a : ℝ)⁻¹ ^ 2 * Complex.normSq K.trace := by
  rw [entanglementFidelity_eq]
  simp_rw [conjugateMap_single]
  have h : (∑ i : a, ∑ j : a, K i i * star (K j j)) = K.trace * star K.trace := by
    change (∑ i : a, ∑ j : a, K i i * star (K j j)) =
      (∑ i : a, K i i) * star (∑ j : a, K j j)
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [h, Complex.star_def, Complex.mul_conj]
  simp

theorem entanglementFidelity_sum (Φ : ι → MatrixMap a a) :
    entanglementFidelity (∑ t, Φ t) = ∑ t, entanglementFidelity (Φ t) := by
  have h : amplify (∑ t, Φ t) (bellProjector a) = ∑ t, amplify (Φ t) (bellProjector a) := by
    ext p q
    simp [amplify, Matrix.sum_apply]
  simp only [entanglementFidelity]
  rw [h, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem entanglementFidelity_kraus (K : ι → Square a) :
    entanglementFidelity (krausMap K) =
      (Fintype.card a : ℝ)⁻¹ ^ 2 * ∑ t, Complex.normSq (K t).trace := by
  rw [krausMap, entanglementFidelity_sum]
  simp only [entanglementFidelity_conjugate, Finset.mul_sum]

end QecPhysical
