import PhysicalBridge.KrausFidelity
import PhysicalBridge.FullErasure
import PhysicalBridge.FidelityBounds

/-! Standard all-finite-ancilla CP and positive mixtures of genuine channels. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder Kronecker
open Matrix
variable {a b c r ι : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype r]
  [Fintype ι] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq r]

omit [Fintype a] [Fintype b] [Fintype r] [DecidableEq a] [DecidableEq b] [DecidableEq r] in
theorem amplify_kronecker (Φ : MatrixMap a b) (A : Square r) (X : Square a) :
    amplify Φ (A ⊗ₖ X) = A ⊗ₖ Φ X := by
  ext p q
  change Φ (A p.1 q.1 • X) p.2 q.2 = A p.1 q.1 * Φ X p.2 q.2
  rw [map_smul]
  rfl

omit [DecidableEq a] [DecidableEq b] in
/-- The definition is equivalent to positivity at every finite matrix amplification. -/
theorem completelyPositive_iff_all_finite (Φ : MatrixMap a b) :
    IsCompletelyPositive Φ ↔ ∀ (r : Type) [Fintype r],
      ∀ X : Square (r × a), X.PosSemidef → (amplify Φ X).PosSemidef := by
  constructor
  · intro h r _ X hX
    exact IsCompletelyPositive.amplify_pos Φ h X hX
  · intro h k X hX
    exact h (Fin k) X hX

def mixtureMap (p : ι → ℝ) (Φ : ι → MatrixMap a b) : MatrixMap a b :=
  ∑ t, (p t : ℂ) • Φ t

omit [Fintype a] [Fintype b] [Fintype r] [DecidableEq a] [DecidableEq b] [DecidableEq r] in
theorem amplify_mixtureMap (p : ι → ℝ) (Φ : ι → MatrixMap a b) (X : Square (r × a)) :
    amplify (mixtureMap p Φ) X = ∑ t, (p t : ℂ) • amplify (Φ t) X := by
  ext u v
  simp [amplify, mixtureMap, Matrix.sum_apply]

omit [DecidableEq a] [DecidableEq b] in
theorem mixtureMap_cp (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t) (Φ : ι → MatrixMap a b)
    (hΦ : ∀ t, IsCompletelyPositive (Φ t)) : IsCompletelyPositive (mixtureMap p Φ) := by
  intro k X hX
  rw [amplify_mixtureMap]
  exact posSemidef_sum _ (fun t => (hΦ t k X hX).smul (Complex.zero_le_real.mpr (hp t)))

omit [DecidableEq a] [DecidableEq b] in
theorem mixtureMap_trace (p : ι → ℝ) (hp : ∑ t, p t = 1) (Φ : ι → MatrixMap a b)
    (hΦ : ∀ t, IsTracePreserving (Φ t)) : IsTracePreserving (mixtureMap p Φ) := by
  intro X
  simp only [mixtureMap, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.trace_sum]
  have ht (t : ι) : (Φ t X).trace = X.trace := hΦ t X
  simp_rw [Matrix.trace_smul, ht]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, hp]
  simp

def mixtureChannel (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t) (hpsum : ∑ t, p t = 1)
    (Φ : ι → Channel a b) : Channel a b where
  map := mixtureMap p (fun t => (Φ t).map)
  completelyPositive := mixtureMap_cp p hp _ (fun t => (Φ t).completelyPositive)
  tracePreserving := mixtureMap_trace p hpsum _ (fun t => (Φ t).tracePreserving)

theorem entanglementFidelity_real_smul (t : ℝ) (Φ : MatrixMap a a) :
    entanglementFidelity ((t : ℂ) • Φ) = t * entanglementFidelity Φ := by
  have h : amplify ((t : ℂ) • Φ) (bellProjector a) =
      (t : ℂ) • amplify Φ (bellProjector a) := by ext p q; rfl
  simp only [entanglementFidelity, h, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem entanglementFidelity_mixture (p : ι → ℝ) (Φ : ι → MatrixMap a a) :
    entanglementFidelity (mixtureMap p Φ) = ∑ t, p t * entanglementFidelity (Φ t) := by
  rw [mixtureMap, entanglementFidelity_sum]
  simp only [entanglementFidelity_real_smul]

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
theorem comp_mixtureMap (R : MatrixMap b c) (p : ι → ℝ) (Φ : ι → MatrixMap a b) :
    R.comp (mixtureMap p Φ) = mixtureMap p (fun t => R.comp (Φ t)) := by
  ext X i j
  simp [mixtureMap, map_sum]

omit [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
theorem comp_sum_maps (R : MatrixMap b c) (Φ : ι → MatrixMap a b) :
    R.comp (∑ t, Φ t) = ∑ t, R.comp (Φ t) := by
  ext X i j
  simp [map_sum]

omit [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
theorem comp_replacementMap (R : MatrixMap b c) (σ : Square b) :
    R.comp (replacementMap (b := a) σ) = replacementMap (R σ) := by
  ext X i j
  simp [replacementMap]

omit [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] in
theorem conjugateMap_comp (A : Matrix b a ℂ) (B : Matrix c b ℂ) :
    (conjugateMap B).comp (conjugateMap A) = conjugateMap (B * A) := by
  ext X i j
  simp [conjugateMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end QecPhysical
