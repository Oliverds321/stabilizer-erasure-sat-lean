import PhysicalBridge.PhysicalBernstein

/-! The original M12 two-tail normalization lemma now controls the optimum
of an actual physical flagged channel. Numerical approximation hypotheses
are explicit; no counting runtime or confidence premise is fabricated. -/
noncomputable section
namespace QecPhysical.Stabilizer.Lift
open QecReliability
open QecReliability.Binary
variable {n r : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

theorem physical_curve_relative (C : Causes r → Finset (Fin n))
    {ε : ℝ} (hε : 0≤ε) (hε1 : ε≤1) (Ah Bh : Fin (r+1) → ℝ)
    (hAh : ∀ j, |Ah j - (layerGoodCount S C j : ℝ)| ≤ (ε/3) * (layerGoodCount S C j : ℝ))
    (hBh : ∀ j, |Bh j - (layerBadCount S C j : ℝ)| ≤ (ε/3) * (layerBadCount S C j : ℝ)) :
    ∀ p (hp : 0≤p) (hp1 : p≤1),
      RelPair ε
        (entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp hp1)).map)
        (bernsteinCurve r (fun j => Ah j / (Ah j + Bh j)) p) ∧
      0 ≤ bernsteinCurve r (fun j => Ah j / (Ah j + Bh j)) p ∧
      bernsteinCurve r (fun j => Ah j / (Ah j + Bh j)) p ≤ 1 := by
  have h := normalized_bernstein (fun j => (layerGoodCount S C j : ℝ))
    (fun j => (layerBadCount S C j : ℝ)) Ah Bh hε hε1
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    (layerCount_total_pos S C) hAh hBh
  intro p hp hp1
  have hh := h p hp hp1
  rw [← (L.iidLatentErasure_certificate_optimum C p hp hp1).1] at hh
  exact hh

end QecPhysical.Stabilizer.Lift
