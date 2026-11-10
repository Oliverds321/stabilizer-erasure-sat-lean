import PhysicalBridge.FlaggedOptimum
import PhysicalBridge.MixturePushforward

/-! Latent causes are not output flags. Repeated causes are retained in the
source mixture, then their probabilities are summed over the actual observed flag. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical
open scoped BigOperators
variable {τ ι a : Type*} {b : ι → Type*} [Fintype τ] [Fintype ι]

omit [Fintype ι] in
theorem pushforwardWeights_nonneg (f : τ → ι) (p : τ → ℝ) (hp : ∀ t, 0≤p t) (i : ι) :
    0≤pushforwardWeights f p i := by
  apply Finset.sum_nonneg
  intro t _
  by_cases h : f t=i <;> simp [h,hp t]

theorem pushforwardWeights_sum (f : τ → ι) (p : τ → ℝ) :
    ∑ i, pushforwardWeights f p i = ∑ t, p t := by
  unfold pushforwardWeights
  rw [Finset.sum_comm]
  simp

theorem pushforwardWeights_average (f : τ → ι) (p : τ → ℝ) (v : ι → ℝ) :
    (∑ i, pushforwardWeights f p i * v i) = ∑ t, p t * v (f t) := by
  unfold pushforwardWeights
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

variable [Fintype a] [∀ i, Fintype (b i)]

def latentFlaggedChannel (C : τ → ι) (p : τ → ℝ) (hp : ∀ t, 0≤p t)
    (hs : ∑ t, p t=1) (N : ∀ i, Channel a (b i)) : Channel a (Sigma b) :=
  mixtureChannel p hp hs (fun t => (flagInclusionChannel b (C t)).comp (N (C t)))

theorem latentFlaggedChannel_eq (C : τ → ι) (p : τ → ℝ) (hp : ∀ t, 0≤p t)
    (hs : ∑ t, p t=1) (N : ∀ i, Channel a (b i)) :
    (latentFlaggedChannel C p hp hs N).map =
      (flaggedChannel (pushforwardWeights C p) (pushforwardWeights_nonneg C p hp)
        ((pushforwardWeights_sum C p).trans hs) N).map :=
  mixtureMap_pushforward C p (fun i => (flagInclusionChannel b i).map.comp (N i).map)

theorem latentFlagRecovery (C : τ → ι) (p : τ → ℝ) (hp : ∀ t, 0≤p t)
    (hs : ∑ t, p t=1) (N : ∀ i, Channel a (b i)) (R : ∀ i, Channel (b i) a) :
    ((flagRecovery b R).comp (latentFlaggedChannel C p hp hs N)).map =
      mixtureMap p (fun t => ((R (C t)).comp (N (C t))).map) := by
  change (flagRecovery b R).map.comp (latentFlaggedChannel C p hp hs N).map = _
  rw [latentFlaggedChannel_eq]
  change ((flagRecovery b R).comp (flaggedChannel _ _ _ N)).map = _
  rw [flagRecovery_flagged, ← mixtureMap_pushforward]

theorem latentFlagged_optimum [DecidableEq a] (C : τ → ι) (p : τ → ℝ)
    (hp : ∀ t, 0≤p t) (hs : ∑ t, p t=1) (N : ∀ i, Channel a (b i)) (v : ι → ℝ)
    (hv : ∀ i, ∃ R : Channel (b i) a,
      entanglementFidelity (R.comp (N i)).map = v i ∧
      ∀ Q : Channel (b i) a, entanglementFidelity (Q.comp (N i)).map ≤ v i) :
    ∃ R : Channel (Sigma b) a,
      entanglementFidelity (R.comp (latentFlaggedChannel C p hp hs N)).map =
        (∑ t, p t*v (C t)) ∧
      ∀ Q : Channel (Sigma b) a,
        entanglementFidelity (Q.comp (latentFlaggedChannel C p hp hs N)).map ≤
          ∑ t, p t*v (C t) := by
  have h := flagged_optimum (pushforwardWeights C p) (pushforwardWeights_nonneg C p hp)
    ((pushforwardWeights_sum C p).trans hs) N v hv
  rw [pushforwardWeights_average] at h
  simpa only [Channel.comp, latentFlaggedChannel_eq] using h

end QecPhysical
