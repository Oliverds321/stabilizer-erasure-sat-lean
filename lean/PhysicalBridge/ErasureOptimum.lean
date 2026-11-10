import PhysicalBridge.SupportedTwirl
import PhysicalBridge.SubspaceRecoveryOptimum

/-! Exact ordinary-erasure optimum, with physical output consisting only
of survivor coordinates. Recovery is quantified over every CPTP channel.
The exponent is the original M12 combinatorial ambiguity, unchanged. -/
noncomputable section
namespace QecPhysical.Stabilizer.Lift
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

def splitEncodingChannel (E : Finset (Fin n)) :
    Channel L.LogicalIndex (SurvivorWord E × ErasedWord E) :=
  (reindexChannel (wordSplit E)).comp L.encodingChannel

/-- The actual encoded partial trace of E, with no replacement subsystem
and no latent cause supplied to the recovery. E is a fixed parameter. -/
def ordinaryErasure (E : Finset (Fin n)) : Channel L.LogicalIndex (SurvivorWord E) :=
  erasureChannel.comp (L.splitEncodingChannel E)

theorem encoded_supportedTwirl (E : Finset (Fin n)) :
    (supportedTwirl E).map.comp L.encodingChannel.map =
      (L.subspaceNoise (supported E)).map := by
  change (uniformMap (fun u : supported E => conjugateMap (pauli u.val))).comp
    (conjugateMap L.encoding) =
      uniformMap (fun u : supported E => conjugateMap (pauli u.val * L.encoding))
  rw [uniformMap_comp]
  simp_rw [conjugateMap_comp]

theorem split_subspaceNoise (E : Finset (Fin n)) :
    (reindexChannel (wordSplit E)).map.comp (L.subspaceNoise (supported E)).map =
      (mixedReplacement : Channel (SurvivorWord E × ErasedWord E)
        (SurvivorWord E × ErasedWord E)).map.comp (L.splitEncodingChannel E).map := by
  rw [← L.encoded_supportedTwirl, ← LinearMap.comp_assoc, supportedTwirl_split,
    LinearMap.comp_assoc]
  rfl

theorem ordinaryErasure_optimum (E : Finset (Fin n)) :
    ∃ R : Channel (SurvivorWord E) L.LogicalIndex,
      entanglementFidelity (R.comp (L.ordinaryErasure E)).map =
        ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S (supported E))⁻¹ ∧
      ∀ Q : Channel (SurvivorWord E) L.LogicalIndex,
        entanglementFidelity (Q.comp (L.ordinaryErasure E)).map ≤
          ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S (supported E))⁻¹ := by
  have hs := (reindex_optimum_iff (L.subspaceNoise (supported E)) (wordSplit E)
    (((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S (supported E))⁻¹)).mp
      (L.subspaceNoise_optimum (supported E))
  apply (erasure_optimum_iff_replacement (L.splitEncodingChannel E) _).mpr
  obtain ⟨R,hR,hb⟩ := hs
  refine ⟨R, ?_, ?_⟩
  · change entanglementFidelity (R.map.comp (mixedReplacement.map.comp
      (L.splitEncodingChannel E).map)) = _
    rw [← L.split_subspaceNoise]
    exact hR
  · intro Q
    change entanglementFidelity (Q.map.comp (mixedReplacement.map.comp
      (L.splitEncodingChannel E).map)) ≤ _
    rw [← L.split_subspaceNoise]
    exact hb Q

/-- Direct theorem map to M12's projected cleaning count. The same
normalizer and supported submodule occur on both sides. -/
theorem ordinaryErasure_optimum_counted (E : Finset (Fin n)) :
    ∃ R : Channel (SurvivorWord E) L.LogicalIndex,
      entanglementFidelity (R.comp (L.ordinaryErasure E)).map =
        (Nat.card {z : Normalizer S // (z : Pauli n) ∈ S ⊔ supported Eᶜ} : ℝ) /
          Nat.card (Normalizer S) ∧
      ∀ Q : Channel (SurvivorWord E) L.LogicalIndex,
        entanglementFidelity (Q.comp (L.ordinaryErasure E)).map ≤
          (Nat.card {z : Normalizer S // (z : Pauli n) ∈ S ⊔ supported Eᶜ} : ℝ) /
            Nat.card (Normalizer S) := by
  have hf : (Nat.card {z : Normalizer S // (z : Pauli n) ∈ S ⊔ supported Eᶜ} : ℝ) /
      Nat.card (Normalizer S) =
        ((2 : ℝ) ^ QecReliability.ambiguity (symplectic n) S (supported E))⁻¹ := by
    have hc := congrArg (fun q : ℚ => (q : ℝ)) (counted_good_fraction S L.isotropic E)
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] using hc
  rw [hf]
  exact L.ordinaryErasure_optimum E

end QecPhysical.Stabilizer.Lift
