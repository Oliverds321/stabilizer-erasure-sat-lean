import QecReliability.RegularWalks

/-! The Rayleigh contract follows from the usual bound on mean-zero functions.
Positivity is explicit; a non-lazy expander is not silently treated as PSD. -/
noncomputable section
namespace QecReliability.ExpanderWalk
open scoped BigOperators
namespace PortGraph
variable {m d : ℕ} (G : PortGraph m d)

theorem transition_const (c : ℝ) : G.transition (fun _ => c) = fun _ => c := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.degree_pos)
  ext v
  simp [transition, hd]

theorem dot_const (c : ℝ) (f : RVec m) : dot (fun _ => c) f = c * ∑ i, f i := by
  simp only [dot, Finset.mul_sum]

/-- The standard mean-zero upper spectral bound plus positivity suffices for
all previously proved avoidance and symbol-encoding theorems. -/
theorem positiveGap_of_centered {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1)
    (hpos : ∀ f, 0 ≤ dot f (G.transition f))
    (hgap : ∀ f : RVec m, (∑ i, f i) = 0 →
      dot f (G.transition f) ≤ (1-g)*energy f) : G.PositiveGap g := by
  refine ⟨hg, hg1, hpos, ?_⟩
  intro f
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.vertices_pos)
  let c : ℝ := (∑ i, f i) / m
  let u : RVec m := f - (fun _ => c)
  have hc : (m : ℝ)*c = ∑ i, f i := by dsimp [c]; field_simp
  have hu : (∑ i, u i) = 0 := by
    simp only [u, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have he : energy u = energy f - (m : ℝ)*c^2 := by
    simp only [u, energy, dot_sub_left, dot_sub_right]
    rw [dot_comm f (fun _ => c), dot_const, dot_const]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hc]
    ring
  have ht : dot u (G.transition u) = dot f (G.transition f) - (m : ℝ)*c^2 := by
    simp only [u, map_sub, G.transition_const, dot_sub_left, dot_sub_right]
    rw [dot_comm f (fun _ => c), dot_const, dot_const, dot_const, G.transition_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hc]
    ring
  have hh := hgap u hu
  rw [ht, he] at hh
  have hmean : g / (m : ℝ) * (∑ i, f i)^2 = g * (m : ℝ)*c^2 := by
    rw [← hc]
    field_simp
  rw [hmean]
  nlinarith

end PortGraph
end QecReliability.ExpanderWalk
