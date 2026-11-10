import PhysicalBridge.UnitaryResolution

/-! Global phase cancellation is derived from unitarity, rather than assumed
when quotient representatives are changed. -/
noncomputable section
namespace QecPhysical
open Matrix
variable {a : Type*} [Fintype a] [DecidableEq a] [Nonempty a]

theorem unitary_same_channel_of_smul (U V : Square a)
    (hU : Uᴴ*U=1) (hV : Vᴴ*V=1) (c : ℂ) (h : V=c•U) :
    conjugateMap V = conjugateMap U := by
  classical
  have hn := hV
  rw [h, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hU] at hn
  let i : a := Classical.choice inferInstance
  have hc := congrFun (congrFun hn i) i
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hc
  ext M j k
  simp only [conjugateMap, h, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hc, one_smul]

end QecPhysical
