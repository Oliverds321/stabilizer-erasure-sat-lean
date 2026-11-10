import PhysicalBridge.Mixtures

/-! A coefficient resolution for a unitary operator basis and its exact twirl.
The finite Pauli tensor family is constructed separately. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder Kronecker
open Matrix
variable {a b ι κ : Type*} [Fintype a] [Fintype b] [Fintype ι] [Fintype κ]
  [DecidableEq a] [DecidableEq b]

/-- Unitary matrices whose vectorized outer products resolve D times identity. -/
structure UnitaryResolution (a ι : Type*) [Fintype a] [Fintype ι] [DecidableEq a] where
  op : ι → Square a
  unitary : ∀ t, (op t)ᴴ * op t = 1
  resolution : ∀ i j k l : a, ∑ t, op t i k * star (op t j l) =
    (Fintype.card a : ℂ) * (if i = j then 1 else 0) * (if k = l then 1 else 0)

omit [Fintype b] [DecidableEq b] in
theorem conjugateMap_single_apply (U : Matrix b a ℂ) (k l : a) (i j : b) :
    conjugateMap U (Matrix.single k l 1) i j = U i k * star (U j l) := by
  simp [conjugateMap, Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, ite_and]

omit [Fintype b] [DecidableEq b] in
theorem matrixMap_ext (Φ Ψ : MatrixMap a b)
    (h : ∀ i j : a, Φ (Matrix.single i j 1) = Ψ (Matrix.single i j 1)) : Φ = Ψ := by
  apply LinearMap.ext
  intro X
  rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by simp
  rw [hs, map_smul, map_smul, h]

namespace UnitaryResolution
variable (U : UnitaryResolution a ι)

def errorChannel (t : ι) : Channel a a := isometryChannel (U.op t) (U.unitary t)

theorem twirl : (∑ t, conjugateMap (U.op t)) =
    (Fintype.card a : ℂ) • replacementMap (b := a) (1 : Square a) := by
  apply matrixMap_ext
  intro k l
  ext i j
  simp only [LinearMap.sum_apply, Matrix.sum_apply, conjugateMap_single_apply]
  rw [U.resolution]
  change _ = (Fintype.card a : ℂ) * ((Matrix.single k l (1 : ℂ)).trace * (1 : Square a) i j)
  have ht : (Matrix.single k l (1 : ℂ)).trace = if k = l then 1 else 0 := by
    by_cases h : k = l <;> simp [h]
  rw [ht, Matrix.one_apply]
  ring

/-- Total fidelity mass is one for every CPTP recovery, without a Kraus premise. -/
theorem sum_recovered_fidelity [Nonempty a] (R : Channel a a) :
    ∑ t, entanglementFidelity (R.comp (U.errorChannel t)).map = 1 := by
  change (∑ t, entanglementFidelity (R.map.comp (conjugateMap (U.op t)))) = 1
  rw [← entanglementFidelity_sum, ← comp_sum_maps, U.twirl, LinearMap.comp_smul,
    comp_replacementMap]
  have hc : (Fintype.card a : ℂ) = ((Fintype.card a : ℝ) : ℂ) := rfl
  rw [hc, entanglementFidelity_real_smul, entanglementFidelity_replacement, R.tracePreserving]
  simp only [Matrix.trace_one, Complex.natCast_re]
  have hn : (Fintype.card a : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

def inverseChannel (t : ι) : Channel a a :=
  isometryChannel (U.op t)ᴴ (by
    rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp (U.unitary t))

theorem inverse_corrects (t : ι) :
    ((U.inverseChannel t).comp (U.errorChannel t)).map = (Channel.identity a).map := by
  change (conjugateMap (U.op t)ᴴ).comp (conjugateMap (U.op t)) = LinearMap.id
  rw [conjugateMap_comp, U.unitary]
  ext X i j
  simp [conjugateMap]

end UnitaryResolution
end QecPhysical
