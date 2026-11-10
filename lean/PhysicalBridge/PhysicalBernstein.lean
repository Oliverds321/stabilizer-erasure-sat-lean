import PhysicalBridge.LatentCertificates

/-! Iid latent bits yield the actual physical Bernstein reliability curve.
The observed flag is C(b), never b. Coefficients count every (b,z) pair. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open QecReliability
open QecReliability.Binary
open QecPhysical.BinaryPauli

def causeMass {r : ℕ} (p : ℝ) (b : Causes r) : ℝ :=
  p ^ b.card * (1-p) ^ (r-b.card)

theorem causeMass_nonneg {r : ℕ} {p : ℝ} (hp : 0≤p) (hp1 : p≤1) (b : Causes r) :
    0≤causeMass p b := mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem layerAverage_one (r : ℕ) (j : Fin (r+1)) :
    layerAverage (fun _ : Causes r => ()) (fun _ => (1 : ℝ)) j = 1 := by
  classical
  unfold layerAverage
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  have hc : Fintype.card {b : Causes r // hammingLayer b=j} = r.choose j.val := by
    simpa only [Nat.card_eq_fintype_card] using hamming_layer_card r j
  rw [hc, div_self]
  exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ j.isLt)).ne'

theorem causeMass_sum (r : ℕ) (p : ℝ) : ∑ b : Causes r, causeMass p b = 1 := by
  have h := latentCurve_eq_bernstein (fun _ : Causes r => ()) (fun _ => (1 : ℝ)) p
  have hb : bernsteinCurve r (layerAverage (fun _ : Causes r => ()) (fun _ => (1 : ℝ))) p = 1 := by
    unfold bernsteinCurve
    rw [funext (layerAverage_one r)]
    exact average_const _ (bernsteinWeight_sum r p) 1
  simpa only [latentCurve, causeMass, mul_one] using h.trans hb

variable {n r : ℕ} (S : Submodule Bit (Pauli n))

def layerGoodCount (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) : ℕ :=
  latentGoodCount S (fun b : {b : Causes r // hammingLayer b=j} => C b.val)

def layerBadCount (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) : ℕ :=
  latentBadCount S (fun b : {b : Causes r // hammingLayer b=j} => C b.val)

theorem layerCount_partition (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) :
    layerGoodCount S C j + layerBadCount S C j = r.choose j.val * Nat.card (Normalizer S) := by
  simpa only [layerGoodCount, layerBadCount, hamming_layer_card] using
    latentCount_partition S (fun b : {b : Causes r // hammingLayer b=j} => C b.val)

theorem layerCount_total_pos (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) :
    0 < (layerGoodCount S C j : ℝ) + layerBadCount S C j := by
  have hc : (layerGoodCount S C j : ℝ) + layerBadCount S C j =
      (r.choose j.val : ℝ) * Nat.card (Normalizer S) := by
    exact_mod_cast layerCount_partition S C j
  rw [hc]
  apply mul_pos
  · exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt)
  · exact_mod_cast (Nat.card_pos (α:=Normalizer S))

namespace Lift
variable {S} (L : Lift S)

def iidLatentErasure (C : Causes r → Finset (Fin n)) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    Channel L.LogicalIndex (ErasureFlagOutput n) :=
  L.latentErasure C (causeMass p) (causeMass_nonneg hp hp1) (causeMass_sum r p)

theorem iidLatentErasure_optimum (C : Causes r → Finset (Fin n)) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp hp1)).map =
      bernsteinCurve r (layerAverage C (erasureScore S)) p ∧
    ∀ Q : Channel (ErasureFlagOutput n) L.LogicalIndex,
      entanglementFidelity (Q.comp (L.iidLatentErasure C p hp hp1)).map ≤
        bernsteinCurve r (layerAverage C (erasureScore S)) p := by
  have h := L.latentErasure_optimum C (causeMass p) (causeMass_nonneg hp hp1) (causeMass_sum r p)
  change entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp hp1)).map =
      latentCurve C (erasureScore S) p ∧
    ∀ Q : Channel (ErasureFlagOutput n) L.LogicalIndex,
      entanglementFidelity (Q.comp (L.iidLatentErasure C p hp hp1)).map ≤
        latentCurve C (erasureScore S) p at h
  simpa only [latentCurve_eq_bernstein] using h

include L in
theorem physicalLayer_good_fraction (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) :
    layerAverage C (erasureScore S) j =
      (layerGoodCount S C j : ℝ) / ((r.choose j.val : ℝ) * Nat.card (Normalizer S)) := by
  unfold layerAverage
  simp_rw [← L.erasureGood_fraction]
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have hc := latentGoodCount_eq_sum S (fun b : {b : Causes r // hammingLayer b=j} => C b.val)
  rw [← hc]
  change ((layerGoodCount S C j : ℝ) / Nat.card (Normalizer S)) / (r.choose j.val : ℝ) = _
  ring

include L in
theorem physicalLayer_normalized (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) :
    layerAverage C (erasureScore S) j =
      (layerGoodCount S C j : ℝ) / ((layerGoodCount S C j : ℝ) + layerBadCount S C j) := by
  have hc : (layerGoodCount S C j : ℝ) + layerBadCount S C j =
      (r.choose j.val : ℝ) * Nat.card (Normalizer S) := by
    exact_mod_cast layerCount_partition S C j
  rw [hc]
  exact L.physicalLayer_good_fraction C j

theorem iidLatentErasure_certificate_optimum (C : Causes r → Finset (Fin n))
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp hp1)).map =
      bernsteinCurve r (fun j => (layerGoodCount S C j : ℝ) /
        ((layerGoodCount S C j : ℝ) + layerBadCount S C j)) p ∧
    ∀ Q : Channel (ErasureFlagOutput n) L.LogicalIndex,
      entanglementFidelity (Q.comp (L.iidLatentErasure C p hp hp1)).map ≤
        bernsteinCurve r (fun j => (layerGoodCount S C j : ℝ) /
          ((layerGoodCount S C j : ℝ) + layerBadCount S C j)) p := by
  have h := L.iidLatentErasure_optimum C p hp hp1
  simpa only [funext (L.physicalLayer_normalized C)] using h

theorem iidLatentErasure_endpoints (C : Causes r → Finset (Fin n)) :
    entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure C 0 (by norm_num) (by norm_num))).map = erasureScore S (C ∅) ∧
    entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure C 1 (by norm_num) (by norm_num))).map = erasureScore S (C Finset.univ) := by
  constructor
  · rw [(L.iidLatentErasure_optimum C 0 (by norm_num) (by norm_num)).1,
      bernsteinCurve_zero, layerAverage_zero]
  · rw [(L.iidLatentErasure_optimum C 1 (by norm_num) (by norm_num)).1,
      bernsteinCurve_one, layerAverage_last]

end Lift
end QecPhysical.Stabilizer
