import PhysicalBridge.ChannelSums
import Mathlib.Data.Fintype.Sigma

/-! A genuine finite classical flag is a direct sum of quantum output spaces.
Block inclusions are isometries and block extractions are completely positive. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical
open scoped BigOperators ComplexOrder
open Matrix
variable {ι a : Type*} (b : ι → Type*) [Fintype ι] [∀ i, Fintype (b i)]

def flagInclusion (i : ι) : Matrix (Sigma b) (b i) ℂ :=
  fun p j => if p=⟨i,j⟩ then 1 else 0

theorem flagInclusion_isometry (i : ι) :
    (flagInclusion b i)ᴴ * flagInclusion b i = (1 : Square (b i)) := by
  classical
  ext j k
  simp [flagInclusion, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, eq_comm]

def flagInclusionChannel (i : ι) : Channel (b i) (Sigma b) :=
  isometryChannel (flagInclusion b i) (flagInclusion_isometry b i)

def flagBlock (i : ι) : MatrixMap (Sigma b) (b i) where
  toFun X := X.submatrix (Sigma.mk i) (Sigma.mk i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flagBlock_cp (i : ι) : IsCompletelyPositive (flagBlock b i) := by
  intro k X hX
  exact hX.submatrix (fun p : Fin k × b i => (p.1,⟨i,p.2⟩))

theorem flagBlock_inclusion_self (i : ι) :
    (flagBlock b i).comp (flagInclusionChannel b i).map = LinearMap.id := by
  classical
  ext X j k
  simp [flagBlock, flagInclusionChannel, isometryChannel, conjugateMap,
    flagInclusion, Matrix.submatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    apply_ite]

theorem flagBlock_inclusion_ne (i j : ι) (h : j≠i) :
    (flagBlock b j).comp (flagInclusionChannel b i).map = 0 := by
  classical
  have hn (x : b j) (y : b i) : (Sigma.mk j x : Sigma b) ≠ ⟨i,y⟩ :=
    fun hh => h (congrArg Sigma.fst hh)
  ext X x y
  simp [flagBlock, flagInclusionChannel, isometryChannel, conjugateMap,
    flagInclusion, Matrix.submatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, hn]

variable [Fintype a]

/-- Measure the flag and apply its branch decoder. Off-diagonal flag blocks
are discarded, and every branch is defined regardless of its probability. -/
def flagRecovery (R : ∀ i, Channel (b i) a) : Channel (Sigma b) a where
  map := ∑ i, (R i).map.comp (flagBlock b i)
  completelyPositive := completelyPositive_sum _ (fun i =>
    completelyPositive_comp _ _ (flagBlock_cp b i) (R i).completelyPositive)
  tracePreserving X := by
    rw [LinearMap.sum_apply]
    change (∑ i, (R i).map (flagBlock b i X)).trace = X.trace
    rw [Matrix.trace_sum]
    have ht (i : ι) := (R i).tracePreserving (flagBlock b i X)
    simp_rw [ht]
    simp [flagBlock, Matrix.trace, Matrix.diag, Matrix.submatrix, Fintype.sum_sigma]

theorem flagRecovery_inclusion (R : ∀ i, Channel (b i) a) (i : ι) :
    (flagRecovery b R).map.comp (flagInclusionChannel b i).map = (R i).map := by
  classical
  change (∑ j, (R j).map.comp (flagBlock b j)).comp (flagInclusionChannel b i).map = _
  have hs : (∑ j, (R j).map.comp (flagBlock b j)).comp (flagInclusionChannel b i).map =
      ∑ j, (R j).map.comp ((flagBlock b j).comp (flagInclusionChannel b i).map) := by
    ext X u v
    simp
  rw [hs, Finset.sum_eq_single i]
  · rw [flagBlock_inclusion_self, LinearMap.comp_id]
  · intro j _ hj
    rw [flagBlock_inclusion_ne b i j hj, LinearMap.comp_zero]
  · simp

end QecPhysical
