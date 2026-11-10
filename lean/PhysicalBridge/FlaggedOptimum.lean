import PhysicalBridge.FlagBlocks
import PhysicalBridge.Mixtures

/-! Exact optimum of a classical-flagged family of channels. The upper
bound is for every CPTP recovery, not only flag-measuring recoveries. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators
open Matrix
variable {ι a : Type*} {b : ι → Type*} [Fintype ι] [Fintype a]
  [∀ i, Fintype (b i)]

def flaggedChannel (p : ι → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i, p i=1)
    (N : ∀ i, Channel a (b i)) : Channel a (Sigma b) :=
  mixtureChannel p hp hs (fun i => (flagInclusionChannel b i).comp (N i))

theorem flagRecovery_flagged (p : ι → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i, p i=1)
    (N : ∀ i, Channel a (b i)) (R : ∀ i, Channel (b i) a) :
    ((flagRecovery b R).comp (flaggedChannel p hp hs N)).map =
      mixtureMap p (fun i => ((R i).comp (N i)).map) := by
  change (flagRecovery b R).map.comp
    (mixtureMap p (fun i => (flagInclusionChannel b i).map.comp (N i).map)) = _
  rw [comp_mixtureMap]
  congr 1
  funext i
  rw [← LinearMap.comp_assoc, flagRecovery_inclusion]
  rfl

variable [DecidableEq a]

theorem flagged_upper_bound (p : ι → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i, p i=1)
    (N : ∀ i, Channel a (b i)) (v : ι → ℝ)
    (hb : ∀ i, ∀ Q : Channel (b i) a, entanglementFidelity (Q.comp (N i)).map ≤ v i)
    (R : Channel (Sigma b) a) :
    entanglementFidelity (R.comp (flaggedChannel p hp hs N)).map ≤ ∑ i, p i*v i := by
  change entanglementFidelity (R.map.comp
    (mixtureMap p (fun i => (flagInclusionChannel b i).map.comp (N i).map))) ≤ _
  rw [comp_mixtureMap, entanglementFidelity_mixture]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (hb i (R.comp (flagInclusionChannel b i))) (hp i)

theorem flagged_optimum (p : ι → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i, p i=1)
    (N : ∀ i, Channel a (b i)) (v : ι → ℝ)
    (hv : ∀ i, ∃ R : Channel (b i) a,
      entanglementFidelity (R.comp (N i)).map = v i ∧
      ∀ Q : Channel (b i) a, entanglementFidelity (Q.comp (N i)).map ≤ v i) :
    ∃ R : Channel (Sigma b) a,
      entanglementFidelity (R.comp (flaggedChannel p hp hs N)).map = (∑ i, p i*v i) ∧
      ∀ Q : Channel (Sigma b) a,
        entanglementFidelity (Q.comp (flaggedChannel p hp hs N)).map ≤ ∑ i, p i*v i := by
  let R i := Classical.choose (hv i)
  have hR i : entanglementFidelity ((R i).comp (N i)).map = v i :=
    (Classical.choose_spec (hv i)).1
  have hb i := (Classical.choose_spec (hv i)).2
  refine ⟨flagRecovery b R, ?_, flagged_upper_bound p hp hs N v hb⟩
  rw [flagRecovery_flagged, entanglementFidelity_mixture]
  simp_rw [hR]

end QecPhysical
