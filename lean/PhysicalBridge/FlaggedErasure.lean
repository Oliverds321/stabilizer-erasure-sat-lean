import PhysicalBridge.LatentFlaggedChannel
import PhysicalBridge.ErasureOptimum

/-! Actual flagged and latent erasure channels. Only E is exposed in the
classical output, and one fixed CPTP decoder attains the optimum for every
input-independent probability distribution and every latent map. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open QecReliability.Binary
open QecPhysical.BinaryPauli

abbrev ErasureFlagOutput (n : ℕ) := Σ E : Finset (Fin n), SurvivorWord E

def erasureScore {n : ℕ} (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) : ℝ :=
  ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S (supported E))⁻¹

namespace Lift
variable {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

def erasureBranchRecovery (E : Finset (Fin n)) : Channel (SurvivorWord E) L.LogicalIndex :=
  Classical.choose (L.ordinaryErasure_optimum E)

theorem erasureBranchRecovery_fidelity (E : Finset (Fin n)) :
    entanglementFidelity ((L.erasureBranchRecovery E).comp (L.ordinaryErasure E)).map =
      erasureScore S E := (Classical.choose_spec (L.ordinaryErasure_optimum E)).1

theorem erasureBranch_upper_bound (E : Finset (Fin n)) (Q : Channel (SurvivorWord E) L.LogicalIndex) :
    entanglementFidelity (Q.comp (L.ordinaryErasure E)).map ≤ erasureScore S E :=
  (Classical.choose_spec (L.ordinaryErasure_optimum E)).2 Q

def erasureFlagDecoder : Channel (ErasureFlagOutput n) L.LogicalIndex :=
  flagRecovery SurvivorWord L.erasureBranchRecovery

def flaggedErasure (p : Finset (Fin n) → ℝ) (hp : ∀ E, 0≤p E) (hs : ∑ E, p E=1) :
    Channel L.LogicalIndex (ErasureFlagOutput n) :=
  flaggedChannel p hp hs L.ordinaryErasure

theorem flaggedErasure_optimum (p : Finset (Fin n) → ℝ) (hp : ∀ E, 0≤p E) (hs : ∑ E, p E=1) :
    entanglementFidelity (L.erasureFlagDecoder.comp (L.flaggedErasure p hp hs)).map =
      (∑ E, p E * erasureScore S E) ∧
    ∀ Q : Channel (ErasureFlagOutput n) L.LogicalIndex,
      entanglementFidelity (Q.comp (L.flaggedErasure p hp hs)).map ≤
        ∑ E, p E * erasureScore S E := by
  constructor
  · change entanglementFidelity ((flagRecovery SurvivorWord L.erasureBranchRecovery).comp
      (flaggedChannel p hp hs L.ordinaryErasure)).map = _
    rw [flagRecovery_flagged, entanglementFidelity_mixture]
    simp_rw [L.erasureBranchRecovery_fidelity]
  · exact flagged_upper_bound p hp hs L.ordinaryErasure (erasureScore S) L.erasureBranch_upper_bound

variable {τ : Type*} [Fintype τ]

def latentErasure (C : τ → Finset (Fin n)) (p : τ → ℝ) (hp : ∀ t, 0≤p t)
    (hs : ∑ t, p t=1) : Channel L.LogicalIndex (ErasureFlagOutput n) :=
  latentFlaggedChannel C p hp hs L.ordinaryErasure

theorem latentErasure_grouped (C : τ → Finset (Fin n)) (p : τ → ℝ) (hp : ∀ t, 0≤p t)
    (hs : ∑ t, p t=1) :
    (L.latentErasure C p hp hs).map =
      (L.flaggedErasure (pushforwardWeights C p) (pushforwardWeights_nonneg C p hp)
        ((pushforwardWeights_sum C p).trans hs)).map :=
  latentFlaggedChannel_eq C p hp hs L.ordinaryErasure

theorem latentErasure_optimum (C : τ → Finset (Fin n)) (p : τ → ℝ) (hp : ∀ t, 0≤p t)
    (hs : ∑ t, p t=1) :
    entanglementFidelity (L.erasureFlagDecoder.comp (L.latentErasure C p hp hs)).map =
      (∑ t, p t * erasureScore S (C t)) ∧
    ∀ Q : Channel (ErasureFlagOutput n) L.LogicalIndex,
      entanglementFidelity (Q.comp (L.latentErasure C p hp hs)).map ≤
        ∑ t, p t * erasureScore S (C t) := by
  have h := L.flaggedErasure_optimum (pushforwardWeights C p)
    (pushforwardWeights_nonneg C p hp) ((pushforwardWeights_sum C p).trans hs)
  rw [pushforwardWeights_average] at h
  simpa only [Channel.comp, L.latentErasure_grouped] using h

end Lift
end QecPhysical.Stabilizer
