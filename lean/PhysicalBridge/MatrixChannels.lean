import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basis

-- Preserve the original matrix/function coercion reductions in these proofs.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Finite-dimensional channels with positivity quantified over every finite
ancilla dimension. The matrix-map/channel shape is chosen to support an adapter
to Lean-QIT; no external package is imported here. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder Kronecker
open Matrix

abbrev Square (a : Type*) := Matrix a a ℂ
abbrev MatrixMap (a b : Type*) := Square a →ₗ[ℂ] Square b

variable {a b c r e : Type*} [Fintype a] [Fintype b] [Fintype c]
  [Fintype r] [Fintype e] [DecidableEq a] [DecidableEq b] [DecidableEq c]
  [DecidableEq r] [DecidableEq e]

def amplify (Φ : MatrixMap a b) : MatrixMap (r × a) (r × b) where
  toFun X p q := Φ (fun i j => X (p.1,i) (q.1,j)) p.2 q.2
  map_add' X Y := by
    ext p q
    change Φ ((fun i j => X (p.1,i) (q.1,j)) + (fun i j => Y (p.1,i) (q.1,j))) p.2 q.2 = _
    rw [map_add]; rfl
  map_smul' z X := by
    ext p q
    change Φ (z • (fun i j => X (p.1,i) (q.1,j))) p.2 q.2 = _
    rw [map_smul]; rfl

def IsCompletelyPositive (Φ : MatrixMap a b) : Prop :=
  ∀ k : ℕ, ∀ X : Square (Fin k × a), X.PosSemidef → (amplify Φ X).PosSemidef

def IsTracePreserving (Φ : MatrixMap a b) : Prop := ∀ X, (Φ X).trace = X.trace

structure Channel (a b : Type*) [Fintype a] [Fintype b] where
  map : MatrixMap a b
  completelyPositive : IsCompletelyPositive map
  tracePreserving : IsTracePreserving map

omit [Fintype a] [Fintype b] [Fintype c] [Fintype r] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq r] in
theorem amplify_comp (Φ : MatrixMap a b) (Ψ : MatrixMap b c) :
    amplify (r := r) (Ψ.comp Φ) = (amplify Ψ).comp (amplify Φ) := rfl

def Channel.comp (Ψ : Channel b c) (Φ : Channel a b) : Channel a c where
  map := Ψ.map.comp Φ.map
  completelyPositive k X hX := by
    rw [amplify_comp]
    exact Ψ.completelyPositive k _ (Φ.completelyPositive k X hX)
  tracePreserving X := (Ψ.tracePreserving (Φ.map X)).trans (Φ.tracePreserving X)

def Channel.identity (a : Type*) [Fintype a] : Channel a a where
  map := LinearMap.id
  completelyPositive _ _ hX := hX
  tracePreserving _ := rfl

omit [DecidableEq a] in
theorem posSemidef_sum {ι : Type*} [Fintype ι] (X : ι → Square a)
    (hX : ∀ i, (X i).PosSemidef) : (∑ i, X i).PosSemidef := by
  classical
  have h : ∀ s : Finset ι, (∑ i ∈ s, X i).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : Square a).PosSemidef)
    | @insert i s hi ih => simpa [hi] using (hX i).add ih
  simpa using h Finset.univ

/-- Trace out exactly the second tensor factor. -/
def discardRight : MatrixMap (a × e) a where
  toFun X i j := ∑ t, X (i,t) (j,t)
  map_add' X Y := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' z X := by ext i j; simp [Finset.mul_sum]

omit [DecidableEq a] [DecidableEq e] in
theorem discardRight_trace (X : Square (a × e)) : (discardRight X).trace = X.trace := by
  simp [discardRight, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

omit [Fintype a] [Fintype r] [DecidableEq a] [DecidableEq r] [DecidableEq e] in
theorem amplify_discardRight (X : Square (r × (a × e))) :
    amplify (discardRight : MatrixMap (a × e) a) X =
      ∑ t : e, X.submatrix (fun p : r × a => (p.1,(p.2,t)))
        (fun p : r × a => (p.1,(p.2,t))) := by
  ext p q
  simp [amplify, discardRight, Matrix.sum_apply, Matrix.submatrix]

def erasureChannel : Channel (a × e) a where
  map := discardRight
  completelyPositive _ X hX := by
    rw [amplify_discardRight]
    exact posSemidef_sum _ (fun t => hX.submatrix _)
  tracePreserving := discardRight_trace

/-- A physical encoding/recovery matrix; isometry is stated separately. -/
def conjugateMap (V : Matrix b a ℂ) : MatrixMap a b where
  toFun X := V * X * Vᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' z X := by simp

omit [Fintype b] [DecidableEq a] [DecidableEq b] in
theorem amplify_conjugate (V : Matrix b a ℂ) (X : Square (r × a)) :
    amplify (conjugateMap V) X = ((1 : Square r) ⊗ₖ V) * X * ((1 : Square r) ⊗ₖ V)ᴴ := by
  ext p q
  simp [amplify, conjugateMap, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite, ite_mul]

omit [DecidableEq a] [DecidableEq b] in
theorem conjugateMap_cp (V : Matrix b a ℂ) : IsCompletelyPositive (conjugateMap V) := by
  intro k X hX
  rw [amplify_conjugate]
  exact hX.mul_mul_conjTranspose_same _

omit [DecidableEq b] in
theorem conjugateMap_trace (V : Matrix b a ℂ) (hV : Vᴴ * V = 1) :
    IsTracePreserving (conjugateMap V) := by
  intro X
  change (V*X*Vᴴ).trace = X.trace
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

def isometryChannel (V : Matrix b a ℂ) (hV : Vᴴ * V = 1) : Channel a b where
  map := conjugateMap V
  completelyPositive := conjugateMap_cp V
  tracePreserving := conjugateMap_trace V hV

/-- Fixed encoded input, then a specified subsystem is erased. -/
def encodedErasure (V : Matrix (b × e) a ℂ) (hV : Vᴴ * V = 1) : Channel a b :=
  erasureChannel.comp (isometryChannel V hV)


omit [DecidableEq a] [DecidableEq b] [DecidableEq r] in
/-- The Fin-indexed CP definition covers every finite ancilla type by reindexing. -/
theorem IsCompletelyPositive.amplify_pos (Φ : MatrixMap a b)
    (hΦ : IsCompletelyPositive Φ) (X : Square (r × a)) (hX : X.PosSemidef) :
    (amplify Φ X).PosSemidef := by
  let f := (Fintype.equivFin r).symm
  let Y := X.submatrix (fun p : Fin (Fintype.card r) × a => (f p.1,p.2))
    (fun p : Fin (Fintype.card r) × a => (f p.1,p.2))
  have hY := hΦ (Fintype.card r) Y (hX.submatrix _)
  have h := hY.submatrix (fun p : r × b => ((Fintype.equivFin r) p.1,p.2))
  have he : (amplify Φ Y).submatrix
      (fun p : r × b => ((Fintype.equivFin r) p.1, p.2))
      (fun p : r × b => ((Fintype.equivFin r) p.1, p.2)) = amplify Φ X := by
    ext p q
    change Φ (fun i j => X (f ((Fintype.equivFin r) p.1), i)
      (f ((Fintype.equivFin r) q.1), j)) p.2 q.2 =
      Φ (fun i j => X (p.1, i) (q.1, j)) p.2 q.2
    simp only [f, Equiv.symm_apply_apply]
  rw [he] at h
  exact h

omit [DecidableEq a] [DecidableEq b] [DecidableEq r] in
theorem IsTracePreserving.amplify_trace (Φ : MatrixMap a b)
    (hΦ : IsTracePreserving Φ) (X : Square (r × a)) :
    (amplify Φ X).trace = X.trace := by
  change (∑ p : r × b, Φ (fun i j => X (p.1,i) (p.1,j)) p.2 p.2) = _
  rw [Fintype.sum_prod_type]
  change (∑ t : r, (Φ (fun i j => X (t,i) (t,j))).trace) = _
  calc
    (∑ t : r, (Φ (fun i j => X (t,i) (t,j))).trace) =
        ∑ t : r, Matrix.trace (fun i j => X (t,i) (t,j)) := by
      apply Finset.sum_congr rfl
      intro t _
      exact hΦ _
    _ = X.trace := by simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

end QecPhysical
