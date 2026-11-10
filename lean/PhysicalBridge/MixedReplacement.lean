import PhysicalBridge.UniformMixtures

/-! Ordinary partial trace and trace followed by maximally mixed replacement
have exactly the same attainable recovered channels. The replacement channel
is constructed as a uniform mixture of basis-state insertions. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators
open Matrix
variable {a b c e : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
  [DecidableEq a] [DecidableEq e] [Nonempty e]

def insertBasis (t : e) : Matrix (a × e) a ℂ :=
  fun p i => if p.1=i ∧ p.2=t then 1 else 0

omit [Fintype b] [Fintype c] [Nonempty e] in
theorem insertBasis_isometry (t : e) :
    (insertBasis (a:=a) t)ᴴ * insertBasis (a:=a) t = (1 : Square a) := by
  ext i j
  simp [insertBasis, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, ite_and, eq_comm]

def insertBasisChannel (t : e) : Channel a (a × e) :=
  isometryChannel (insertBasis t) (insertBasis_isometry t)

omit [Fintype b] [Fintype c] [Fintype e] [Nonempty e] in
theorem insertBasis_apply (t : e) (X : Square a) (p q : a × e) :
    conjugateMap (insertBasis t) X p q = if p.2=t ∧ q.2=t then X p.1 q.1 else 0 := by
  by_cases hp : p.2=t <;> by_cases hq : q.2=t <;>
    simp [conjugateMap, insertBasis, Matrix.mul_apply, Matrix.conjTranspose_apply,
      ite_mul, hp, hq, apply_ite]

omit [Fintype b] [Fintype c] [Nonempty e] in
theorem discardRight_insertBasis (t : e) :
    (discardRight : MatrixMap (a × e) a).comp (insertBasisChannel t).map = LinearMap.id := by
  ext X i j
  change (∑ u : e, conjugateMap (insertBasis t) X (i,u) (j,u)) = X i j
  simp_rw [insertBasis_apply]
  simp

def appendMixed : Channel a (a × e) := uniformChannel insertBasisChannel

omit [Fintype b] [Fintype c] in
theorem appendMixed_apply (X : Square a) (p q : a × e) :
    (appendMixed : Channel a (a × e)).map X p q =
      if p.2=q.2 then (Fintype.card e : ℂ)⁻¹ * X p.1 q.1 else 0 := by
  change (uniformMap (fun t : e => conjugateMap (insertBasis t))) X p q = _
  simp only [uniformMap, mixtureMap, LinearMap.sum_apply, LinearMap.smul_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [insertBasis_apply]
  by_cases h : p.2=q.2
  · simp [h]
  · have hne : ∀ t : e, ¬ (p.2=t ∧ q.2=t) := by
      intro t ht
      exact h (ht.1.trans ht.2.symm)
    simp [hne, h]

omit [Fintype b] [Fintype c] in
theorem discardRight_appendMixed :
    (discardRight : MatrixMap (a × e) a).comp (appendMixed : Channel a (a × e)).map =
      LinearMap.id := by
  change discardRight.comp (uniformMap (fun t : e => (insertBasisChannel (a:=a) t).map)) = _
  rw [comp_uniformMap]
  simp_rw [discardRight_insertBasis]
  exact uniformMap_const _

def mixedReplacement : Channel (a × e) (a × e) := appendMixed.comp erasureChannel

omit [Fintype b] [Fintype c] in
theorem mixedReplacement_apply (X : Square (a × e)) (p q : a × e) :
    (mixedReplacement : Channel (a × e) (a × e)).map X p q =
      if p.2=q.2 then (Fintype.card e : ℂ)⁻¹ * (∑ t : e, X (p.1,t) (q.1,t)) else 0 :=
  appendMixed_apply _ p q

/-- Every recovery after replacement is a recovery after ordinary erasure. -/
theorem recover_replacement_via_erasure (N : Channel b (a × e))
    (R : Channel (a × e) c) :
    ∃ Q : Channel a c,
      (Q.comp (erasureChannel.comp N)).map =
        (R.comp (mixedReplacement.comp N)).map := by
  refine ⟨R.comp appendMixed, ?_⟩
  rfl

/-- Conversely, discarding the inserted mixed subsystem implements any
ordinary-erasure recovery on the replacement output. -/
theorem recover_erasure_via_replacement (N : Channel b (a × e))
    (Q : Channel a c) :
    ∃ R : Channel (a × e) c,
      (R.comp (mixedReplacement.comp N)).map =
        (Q.comp (erasureChannel.comp N)).map := by
  refine ⟨Q.comp erasureChannel, ?_⟩
  change (Q.map.comp discardRight).comp ((appendMixed.map.comp discardRight).comp N.map) = _
  have h : (discardRight : MatrixMap (a×e) a).comp
      ((appendMixed.map.comp discardRight).comp N.map) = discardRight.comp N.map := by
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, discardRight_appendMixed,
      LinearMap.id_comp]
  rw [LinearMap.comp_assoc, h]
  rfl

omit [Fintype c] in
/-- Equality of the attained all-CPTP optimum is a consequence of equality
of attainable recovered maps, not an assumed data-processing property. -/
theorem erasure_optimum_iff_replacement [DecidableEq b]
    (N : Channel b (a × e)) (v : ℝ) :
    (∃ Q : Channel a b,
      entanglementFidelity (Q.comp (erasureChannel.comp N)).map = v ∧
      ∀ Q' : Channel a b,
        entanglementFidelity (Q'.comp (erasureChannel.comp N)).map ≤ v) ↔
    (∃ R : Channel (a × e) b,
      entanglementFidelity (R.comp (mixedReplacement.comp N)).map = v ∧
      ∀ R' : Channel (a × e) b,
        entanglementFidelity (R'.comp (mixedReplacement.comp N)).map ≤ v) := by
  constructor
  · rintro ⟨Q, hQ, hb⟩
    obtain ⟨R,hR⟩ := recover_erasure_via_replacement N Q
    refine ⟨R, by rw [hR]; exact hQ, ?_⟩
    intro R'
    obtain ⟨Q',hQ'⟩ := recover_replacement_via_erasure N R'
    rw [← hQ']
    exact hb Q'
  · rintro ⟨R,hR,hb⟩
    obtain ⟨Q,hQ⟩ := recover_replacement_via_erasure N R
    refine ⟨Q, by rw [hQ]; exact hR, ?_⟩
    intro Q'
    obtain ⟨R',hR'⟩ := recover_erasure_via_replacement N Q'
    rw [← hR']
    exact hb R'

end QecPhysical
