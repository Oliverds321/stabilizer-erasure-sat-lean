import PhysicalBridge.BinaryPauliResolution
import PhysicalBridge.MixedReplacement

/-! A normalized complete Pauli twirl on one tensor factor is exactly
partial trace followed by maximally mixed insertion, on every matrix input. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators Kronecker
open Matrix
variable {a e ι : Type*} [Fintype a] [Fintype e] [Fintype ι]
  [DecidableEq a] [DecidableEq e] [Nonempty e]

omit [Fintype a] [DecidableEq a] in
theorem UnitaryResolution.uniform_resolution (U : UnitaryResolution e ι)
    (hcard : Fintype.card ι = Fintype.card e * Fintype.card e) (i j k l : e) :
    (∑ t, (((Fintype.card ι : ℝ)⁻¹ : ℂ) * (U.op t i k * star (U.op t j l)))) =
      (Fintype.card e : ℂ)⁻¹ * (if i=j then 1 else 0) * (if k=l then 1 else 0) := by
  rw [← Finset.mul_sum, U.resolution]
  have hn : (Fintype.card e : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α:=e))
  simp only [hcard, Nat.cast_mul, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  field_simp

omit [Fintype a] [Fintype ι] [Nonempty e] in
theorem discardRight_single (k l : a × e) :
    discardRight (Matrix.single k l (1:ℂ)) =
      if k.2=l.2 then Matrix.single k.1 l.1 1 else (0 : Square a) := by
  ext i j
  by_cases hi : i=k.1 <;> by_cases hj : j=l.1 <;> by_cases h : k.2=l.2 <;>
    simp [discardRight, Matrix.single, Prod.ext_iff, hi, hj, h, ite_and, eq_comm]

omit [Fintype ι] in
theorem mixedReplacement_single (k l p q : a × e) :
    (mixedReplacement : Channel (a×e) (a×e)).map (Matrix.single k l 1) p q =
      (Fintype.card e : ℂ)⁻¹ * (if p.1=k.1 then 1 else 0) *
        (if q.1=l.1 then 1 else 0) * (if p.2=q.2 then 1 else 0) *
        (if k.2=l.2 then 1 else 0) := by
  change appendMixed.map (discardRight (Matrix.single k l 1)) p q = _
  rw [discardRight_single]
  by_cases hk : k.2=l.2 <;> by_cases hp : p.1=k.1 <;>
    by_cases hq : q.1=l.1 <;> by_cases he : p.2=q.2 <;>
    simp [hk, hp, hq, he, appendMixed_apply, Matrix.single, eq_comm]

theorem UnitaryResolution.twirlRight (U : UnitaryResolution e ι)
    (hcard : Fintype.card ι = Fintype.card e * Fintype.card e) :
    uniformMap (fun t => conjugateMap ((1 : Square a) ⊗ₖ U.op t)) =
      (mixedReplacement : Channel (a×e) (a×e)).map := by
  apply matrixMap_ext
  intro k l
  ext p q
  rw [mixedReplacement_single]
  simp only [uniformMap, mixtureMap, LinearMap.sum_apply, LinearMap.smul_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, conjugateMap_single_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases hp : p.1=k.1 <;> by_cases hq : q.1=l.1
  · simpa [hp,hq] using U.uniform_resolution hcard p.2 q.2 k.2 l.2
  · simp [hp,hq]
  · simp [hp,hq]
  · simp [hp,hq]

end QecPhysical
