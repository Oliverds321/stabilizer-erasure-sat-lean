import PhysicalBridge.BellFidelity

-- Retain matrix/function coercion reduction for the original proofs.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Complete erasure: every trace-preserving recovery has the same Bell
fidelity, and an explicit CPTP recovery attains that value. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder
open Matrix
variable {a b r : Type*} [Fintype a] [Fintype b] [Fintype r]
  [DecidableEq a] [DecidableEq b] [DecidableEq r]

/-- The one-dimensional output retains only trace. -/
def traceOut : MatrixMap a Unit where
  toFun X _ _ := X.trace
  map_add' X Y := by ext i j; exact Matrix.trace_add X Y
  map_smul' z X := by ext i j; exact Matrix.trace_smul z X

omit [Fintype r] [DecidableEq a] [DecidableEq r] in
theorem amplify_traceOut (X : Square (r × a)) :
    amplify (traceOut : MatrixMap a Unit) X =
      ∑ t : a, X.submatrix (fun p : r × Unit => (p.1,t))
        (fun p : r × Unit => (p.1,t)) := by
  ext p q
  simp [amplify, traceOut, Matrix.trace, Matrix.diag, Matrix.sum_apply, Matrix.submatrix]

def completeErasure : Channel a Unit where
  map := traceOut
  completelyPositive _ X hX := by
    rw [amplify_traceOut]
    exact posSemidef_sum _ (fun t => hX.submatrix _)
  tracePreserving X := by simp [traceOut, Matrix.trace, Matrix.diag]

def replacementMap (σ : Square a) : MatrixMap b a where
  toFun X := X.trace • σ
  map_add' X Y := by simp [Matrix.trace_add, add_smul]
  map_smul' z X := by simp [Matrix.trace_smul, smul_smul]

omit [Fintype a] [DecidableEq a] [DecidableEq b] in
theorem recover_completeErasure (R : MatrixMap Unit a) :
    R.comp (traceOut : MatrixMap b Unit) = replacementMap (R 1) := by
  ext X i j
  change R (traceOut X) i j = (X.trace • R 1) i j
  have h : traceOut X = X.trace • (1 : Square Unit) := by
    ext u v
    simp [traceOut]
  rw [h, map_smul]

theorem entanglementFidelity_replacement (σ : Square a) :
    entanglementFidelity (replacementMap (b := a) σ) =
      (Fintype.card a : ℝ)⁻¹ ^ 2 * σ.trace.re := by
  have h (i j : a) : (Matrix.single i j (1 : ℂ)).trace = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  have hs : (∑ i : a, ∑ j : a, replacementMap (b := a) σ (Matrix.single i j 1) i j) =
      σ.trace := by
    change (∑ i : a, ∑ j : a, (Matrix.single i j (1 : ℂ)).trace * σ i j) = _
    simp_rw [h]
    simp [Matrix.trace, Matrix.diag]
  rw [entanglementFidelity_eq, hs]

/-- No Kraus representation assumption is used. TP alone suffices for this endpoint. -/
theorem entanglementFidelity_completeErasure (R : Channel Unit a) :
    entanglementFidelity (R.comp (completeErasure : Channel a Unit)).map =
      (Fintype.card a : ℝ)⁻¹ ^ 2 := by
  change entanglementFidelity (R.map.comp traceOut) = _
  rw [recover_completeErasure, entanglementFidelity_replacement, R.tracePreserving]
  simp

omit [DecidableEq a] [DecidableEq b] in
theorem traceOut_comp_of_tracePreserving (Φ : MatrixMap a b)
    (hΦ : IsTracePreserving Φ) :
    (traceOut : MatrixMap b Unit).comp Φ = traceOut := by
  ext X u v
  exact hΦ X

omit [DecidableEq b] in
/-- Includes an arbitrary fixed isometric encoding before all physical systems are erased. -/
theorem entanglementFidelity_encodedCompleteErasure
    (V : Matrix b a ℂ) (hV : Vᴴ * V = 1) (R : Channel Unit a) :
    entanglementFidelity (R.comp (completeErasure.comp (isometryChannel V hV))).map =
      (Fintype.card a : ℝ)⁻¹ ^ 2 := by
  change entanglementFidelity (R.map.comp (traceOut.comp (conjugateMap V))) = _
  rw [traceOut_comp_of_tracePreserving _ (conjugateMap_trace V hV)]
  exact entanglementFidelity_completeErasure R

def basisPreparation (i₀ : a) : Channel Unit a :=
  isometryChannel (fun i _ => if i = i₀ then 1 else 0) (by
    ext u v
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply])

omit [DecidableEq b] in
/-- Exact attained optimum over all finite-dimensional CPTP recoveries after full erasure. -/
theorem fullErasure_optimum [Nonempty a] (V : Matrix b a ℂ) (hV : Vᴴ * V = 1) :
    ∃ R : Channel Unit a,
      entanglementFidelity (R.comp (completeErasure.comp (isometryChannel V hV))).map =
        (Fintype.card a : ℝ)⁻¹ ^ 2 ∧
      ∀ R' : Channel Unit a,
        entanglementFidelity (R'.comp (completeErasure.comp (isometryChannel V hV))).map ≤
          (Fintype.card a : ℝ)⁻¹ ^ 2 := by
  refine ⟨basisPreparation (Classical.choice ‹Nonempty a›),
    entanglementFidelity_encodedCompleteErasure V hV _, ?_⟩
  intro R'
  exact (entanglementFidelity_encodedCompleteErasure V hV R').le

end QecPhysical
