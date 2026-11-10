import PhysicalBridge.UnitaryResolution

/-! A complete trace-orthogonal unitary family supplies the coefficient
resolution. Cardinality is proved separately at the application site. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators
open Matrix
variable {a ι : Type*} [Fintype a] [Fintype ι] [DecidableEq a] [DecidableEq ι] [Nonempty a]

def coefficientMatrix (U : ι → Square a) : Matrix (a × a) ι ℂ :=
  fun ij t => U t ij.1 ij.2

omit [Fintype ι] [DecidableEq a] [DecidableEq ι] [Nonempty a] in
theorem coefficientMatrix_gram (U : ι → Square a) (s t : ι) :
    ((coefficientMatrix U)ᴴ * coefficientMatrix U) s t = ((U s)ᴴ * U t).trace := by
  simp only [coefficientMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag]
  exact Finset.sum_comm

theorem trace_orthogonal_resolution (U : ι → Square a)
    (hcard : Fintype.card ι = Fintype.card a * Fintype.card a)
    (horth : ∀ s t, ((U s)ᴴ * U t).trace =
      if s=t then (Fintype.card a : ℂ) else 0) :
    ∀ i j k l : a, ∑ t, U t i k * star (U t j l) =
      (Fintype.card a : ℂ) * (if i=j then 1 else 0) * (if k=l then 1 else 0) := by
  let C := coefficientMatrix U
  let D : ℂ := Fintype.card a
  have hD : D ≠ 0 := by
    change (Fintype.card a : ℂ) ≠ 0
    exact_mod_cast (Fintype.card_ne_zero (α := a))
  have hg : Cᴴ * C = D • (1 : Square ι) := by
    ext s t
    rw [coefficientMatrix_gram, horth]
    simp [Matrix.one_apply, D]
  have hi : (D⁻¹ • Cᴴ) * C = 1 := by
    rw [Matrix.smul_mul, hg, smul_smul, inv_mul_cancel₀ hD, one_smul]
  let e : ι ≃ a×a := Fintype.equivOfCardEq (hcard.trans (Fintype.card_prod a a).symm)
  have hr : C * (D⁻¹ • Cᴴ) = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp hi
  have hf := congrArg (fun M : Square (a×a) => D • M) hr
  rw [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hD, one_smul] at hf
  intro i j k l
  have hij := congrFun (congrFun hf (i,k)) (j,l)
  by_cases hi : i=j <;> by_cases hk : k=l <;>
    simpa [C, coefficientMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Prod.mk.injEq, D, hi, hk] using hij

def UnitaryResolution.ofTraceOrthogonal (U : ι → Square a)
    (hunitary : ∀ t, (U t)ᴴ * U t = 1)
    (hcard : Fintype.card ι = Fintype.card a * Fintype.card a)
    (horth : ∀ s t, ((U s)ᴴ * U t).trace =
      if s=t then (Fintype.card a : ℂ) else 0) : UnitaryResolution a ι where
  op := U
  unitary := hunitary
  resolution := trace_orthogonal_resolution U hcard horth

end QecPhysical
