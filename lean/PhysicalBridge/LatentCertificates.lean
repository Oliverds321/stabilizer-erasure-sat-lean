import PhysicalBridge.FlaggedErasure
import QecReliability.Latent

/-! The physical flagged optimum is identified with the original M12
Good/Bad predicates. Joint counts retain (cause,z), not only (E,z). -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} (S : Submodule Bit (Pauli n))

abbrev ErasureGood (E : Finset (Fin n)) (z : Normalizer S) : Prop :=
  QecReliability.Good (symplectic n) S (supported E) z.val

abbrev ErasureBad (E : Finset (Fin n)) (z : Normalizer S) : Prop :=
  QecReliability.Bad (symplectic n) S (supported E) z.val

theorem erasureBad_iff_not_good (E : Finset (Fin n)) (z : Normalizer S) :
    ErasureBad S E z ↔ ¬ErasureGood S E z :=
  QecReliability.bad_iff_not_good (symplectic n) (symplectic_nondegenerate n)
    (symplectic_refl n) S (supported E) z.val

variable {τ : Type*} [Fintype τ]

def latentGoodCount (C : τ → Finset (Fin n)) : ℕ :=
  Nat.card {tz : τ × Normalizer S // ErasureGood S (C tz.1) tz.2}

def latentBadCount (C : τ → Finset (Fin n)) : ℕ :=
  Nat.card {tz : τ × Normalizer S // ErasureBad S (C tz.1) tz.2}

theorem latentGoodCount_eq_sum (C : τ → Finset (Fin n)) :
    latentGoodCount S C = ∑ t, Nat.card {z : Normalizer S // ErasureGood S (C t) z} :=
  QecReliability.pair_predicate_card (fun t z => ErasureGood S (C t) z)

theorem latentBadCount_eq_sum (C : τ → Finset (Fin n)) :
    latentBadCount S C = ∑ t, Nat.card {z : Normalizer S // ErasureBad S (C t) z} :=
  QecReliability.pair_predicate_card (fun t z => ErasureBad S (C t) z)

theorem latentCount_partition (C : τ → Finset (Fin n)) :
    latentGoodCount S C + latentBadCount S C = Nat.card τ * Nat.card (Normalizer S) := by
  have h := QecReliability.finite_predicate_partition
    (fun tz : τ × Normalizer S => ErasureGood S (C tz.1) tz.2)
    (fun tz : τ × Normalizer S => ErasureBad S (C tz.1) tz.2)
    (fun tz => erasureBad_iff_not_good S (C tz.1) tz.2)
  simpa only [latentGoodCount, latentBadCount, Nat.card_prod] using h

namespace Lift
variable {S} (L : Lift S)

omit [Fintype τ] in
include L in
theorem erasureGood_fraction (E : Finset (Fin n)) :
    (Nat.card {z : Normalizer S // ErasureGood S E z} : ℝ) /
      Nat.card (Normalizer S) = erasureScore S E := by
  have hc := congrArg (fun q : ℚ => (q : ℝ)) (counted_good_fraction S L.isotropic E)
  simpa only [ErasureGood, QecReliability.Good, orthogonal_supported, erasureScore,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] using hc

omit [Fintype τ] in
include L in
theorem erasureBad_fraction (E : Finset (Fin n)) :
    (Nat.card {z : Normalizer S // ErasureBad S E z} : ℝ) /
      Nat.card (Normalizer S) = 1-erasureScore S E := by
  have h := QecReliability.bad_card_fraction (symplectic n) (symplectic_nondegenerate n)
    (symplectic_refl n) S (supported E) L.isotropic
  have hc := congrArg (fun q : ℚ => (q : ℝ)) h
  simpa only [ErasureBad, Normalizer, erasureScore, Rat.cast_div, Rat.cast_natCast, Rat.cast_inv,
    Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Nat.card_eq_fintype_card, Bit, ZMod.card,
    Nat.cast_ofNat, Rat.cast_ofNat] using hc

theorem latentErasure_counted (C : τ → Finset (Fin n)) (p : τ → ℝ) (hp : ∀ t, 0≤p t)
    (hs : ∑ t, p t=1) :
    entanglementFidelity (L.erasureFlagDecoder.comp (L.latentErasure C p hp hs)).map =
      (∑ t, p t * (Nat.card {z : Normalizer S // ErasureGood S (C t) z} : ℝ)) /
        Nat.card (Normalizer S) ∧
    1-entanglementFidelity (L.erasureFlagDecoder.comp (L.latentErasure C p hp hs)).map =
      (∑ t, p t * (Nat.card {z : Normalizer S // ErasureBad S (C t) z} : ℝ)) /
        Nat.card (Normalizer S) := by
  rw [(L.latentErasure_optimum C p hp hs).1]
  constructor
  · simp_rw [← L.erasureGood_fraction]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    ring
  · have hc := QecReliability.average_complement p (fun t => erasureScore S (C t)) hs
    change (∑ t, p t*(1-erasureScore S (C t))) = 1-∑ t, p t*erasureScore S (C t) at hc
    rw [← hc]
    simp_rw [← L.erasureBad_fraction]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    ring

theorem latentErasure_uniform_counted [Nonempty τ] (C : τ → Finset (Fin n)) :
    let N := L.latentErasure C (fun _ => (Fintype.card τ : ℝ)⁻¹)
      uniformWeightsAll_nonneg uniformWeightsAll_sum
    entanglementFidelity (L.erasureFlagDecoder.comp N).map =
      (latentGoodCount S C : ℝ) / ((Nat.card τ : ℝ) * Nat.card (Normalizer S)) ∧
    1-entanglementFidelity (L.erasureFlagDecoder.comp N).map =
      (latentBadCount S C : ℝ) / ((Nat.card τ : ℝ) * Nat.card (Normalizer S)) := by
  have h := L.latentErasure_counted C (fun _ => (Fintype.card τ : ℝ)⁻¹)
    uniformWeightsAll_nonneg uniformWeightsAll_sum
  simp only [← Finset.mul_sum, ← Nat.cast_sum, ← latentGoodCount_eq_sum,
    ← latentBadCount_eq_sum] at h
  simpa only [Nat.card_eq_fintype_card, div_eq_mul_inv, _root_.mul_inv_rev,
    mul_comm, mul_left_comm, mul_assoc] using h

end Lift
end QecPhysical.Stabilizer
