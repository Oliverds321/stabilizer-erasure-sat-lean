import PhysicalBridge.MixedReplacement

/-! Unitary computational-basis reindexing as an explicit all-CPTP channel.
No loss of recovery options occurs under this change of output coordinates. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder
open Matrix
variable {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]

def reindexMap (e : a ≃ b) : MatrixMap a b where
  toFun X := X.submatrix e.symm e.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def reindexChannel (e : a ≃ b) : Channel a b where
  map := reindexMap e
  completelyPositive k X hX :=
    hX.submatrix (fun p : Fin k × b => (p.1,e.symm p.2))
  tracePreserving X := by
    change (∑ i : b, X (e.symm i) (e.symm i)) = ∑ i : a, X i i
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

omit [Fintype a] [Fintype b] [Fintype c] in
theorem reindexMap_comp (e : a ≃ b) (f : b ≃ c) :
    (reindexMap f).comp (reindexMap e) = reindexMap (e.trans f) := rfl

omit [Fintype a] [Fintype b] in
theorem reindexMap_inverse (e : a ≃ b) :
    (reindexMap e.symm).comp (reindexMap e) = LinearMap.id := by
  ext X i j
  simp [reindexMap, Matrix.submatrix]

omit [Fintype c] [Fintype d] in
theorem reindexMap_conjugate (e : a ≃ b) (A : Square a) :
    (reindexMap e).comp (conjugateMap A) =
      (conjugateMap (A.submatrix e.symm e.symm)).comp (reindexMap e) := by
  ext X i j
  change (A*X*Aᴴ).submatrix e.symm e.symm i j =
    (A.submatrix e.symm e.symm * X.submatrix e.symm e.symm *
      (A.submatrix e.symm e.symm)ᴴ) i j
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]

omit [Fintype d] in
theorem reindex_optimum_iff [DecidableEq a] (N : Channel a b) (e : b ≃ c) (v : ℝ) :
    (∃ R : Channel b a, entanglementFidelity (R.comp N).map = v ∧
      ∀ Q : Channel b a, entanglementFidelity (Q.comp N).map ≤ v) ↔
    (∃ R : Channel c a, entanglementFidelity (R.comp ((reindexChannel e).comp N)).map = v ∧
      ∀ Q : Channel c a,
        entanglementFidelity (Q.comp ((reindexChannel e).comp N)).map ≤ v) := by
  have h (R : Channel b a) :
      ((R.comp (reindexChannel e.symm)).comp ((reindexChannel e).comp N)).map =
        (R.comp N).map := by
    change (R.map.comp (reindexMap e.symm)).comp ((reindexMap e).comp N.map) = _
    have hi : (reindexMap e.symm).comp ((reindexMap e).comp N.map) = N.map := by
      rw [← LinearMap.comp_assoc, reindexMap_inverse, LinearMap.id_comp]
    rw [LinearMap.comp_assoc, hi]
    rfl
  constructor
  · rintro ⟨R,hR,hb⟩
    refine ⟨R.comp (reindexChannel e.symm), by rw [h]; exact hR, ?_⟩
    intro Q
    exact hb (Q.comp (reindexChannel e))
  · rintro ⟨R,hR,hb⟩
    refine ⟨R.comp (reindexChannel e), hR, ?_⟩
    intro Q
    have hh := hb (Q.comp (reindexChannel e.symm))
    rw [h] at hh
    exact hh

end QecPhysical
