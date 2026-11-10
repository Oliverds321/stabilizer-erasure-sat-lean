import QecReliability.WalkEnergy

/-! Explicit regular undirected multigraphs with ports, their averaging operator,
and all finite port-choice walks. Loops and repeated neighbors are allowed. -/
noncomputable section
namespace QecReliability.ExpanderWalk
open scoped BigOperators

structure PortGraph (m d : ℕ) where
  vertices_pos : 0 < m
  degree_pos : 0 < d
  rotation : (Fin m × Fin d) ≃ (Fin m × Fin d)
  reverse_reverse : Function.Involutive rotation

namespace PortGraph
variable {m d : ℕ} (G : PortGraph m d)

def neighbor (v : Fin m) (i : Fin d) : Fin m := (G.rotation (v, i)).1

def transition : RVec m →ₗ[ℝ] RVec m where
  toFun f v := (∑ i, f (G.neighbor v i)) / (d : ℝ)
  map_add' f h := by ext v; simp [Finset.sum_add_distrib, add_div]
  map_smul' c f := by ext v; simp [← Finset.mul_sum, mul_div_assoc]

theorem edge_reverse (f h : RVec m) :
    (∑ p : Fin m × Fin d, f p.1 * h (G.neighbor p.1 p.2)) =
      ∑ p : Fin m × Fin d, f (G.neighbor p.1 p.2) * h p.1 := by
  calc
    _ = ∑ p : Fin m × Fin d, f (G.rotation p).1 *
        h (G.neighbor (G.rotation p).1 (G.rotation p).2) :=
      (G.rotation.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [neighbor, Prod.mk.eta, G.reverse_reverse p]

theorem dot_transition (f h : RVec m) :
    dot f (G.transition h) =
      (∑ p : Fin m × Fin d, f p.1 * h (G.neighbor p.1 p.2)) / (d : ℝ) := by
  change (∑ v, f v * ((∑ i, h (G.neighbor v i)) / (d : ℝ))) = _
  simp only [← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div, Fintype.sum_prod_type]

theorem transition_symmetric (f h : RVec m) :
    dot f (G.transition h) = dot (G.transition f) h := by
  rw [dot_comm (G.transition f) h, G.dot_transition, G.dot_transition, G.edge_reverse]
  simp [mul_comm]

theorem transition_sum (f : RVec m) : ∑ v, G.transition f v = ∑ v, f v := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.degree_pos)
  have hr := G.rotation.sum_comp (fun p : Fin m × Fin d => f p.1)
  have he : (∑ v, ∑ i, f (G.neighbor v i)) = (d : ℝ) * ∑ v, f v := by
    simpa [neighbor, Fintype.sum_prod_type, Finset.sum_mul, mul_comm] using hr
  simp only [transition, LinearMap.coe_mk, AddHom.coe_mk, ← Finset.sum_div]
  rw [he]
  field_simp

/-- A positive-semidefinite walk and its conventional mean/Rayleigh gap bound.
This is an explicit spectral premise, not a walk-avoidance or encoder premise. -/
structure PositiveGap (g : ℝ) : Prop where
  gap_pos : 0 < g
  gap_le_one : g ≤ 1
  positive : ∀ f, 0 ≤ dot f (G.transition f)
  rayleigh : ∀ f, dot f (G.transition f) ≤
    (1 - g) * energy f + g / (m : ℝ) * (∑ i, f i) ^ 2

def killed (A : Finset (Fin m)) : RVec m →ₗ[ℝ] RVec m :=
  (mask A).comp (G.transition.comp (mask A))

theorem killed_symmetric (A : Finset (Fin m)) (f h : RVec m) :
    dot f (G.killed A h) = dot (G.killed A f) h := by
  simp only [killed, LinearMap.comp_apply]
  rw [dot_mask, G.transition_symmetric, ← dot_mask, dot_comm]

theorem killed_quadratic (A : Finset (Fin m)) (f : RVec m) :
    dot f (G.killed A f) = dot (mask A f) (G.transition (mask A f)) := by
  exact dot_mask A f _

theorem killed_energy {g δ : ℝ} (hg : G.PositiveGap g)
    (A : Finset (Fin m)) (hA : (A.card : ℝ) ≤ (1 - δ) * m)
    (hβ : 0 < 1 - g * δ) (f : RVec m) :
    energy (G.killed A f) ≤ (1 - g * δ) ^ 2 * energy f := by
  have hm : (0 : ℝ) < m := by exact_mod_cast G.vertices_pos
  apply energy_bound_of_rayleigh (G.killed A) (G.killed_symmetric A) hβ
  · intro u
    rw [G.killed_quadratic]
    exact hg.positive _
  · intro u
    have hc : (A.card : ℝ) / m ≤ 1 - δ := (div_le_iff₀ hm).mpr hA
    have hcoef : 1 - g + g * ((A.card : ℝ) / m) ≤ 1 - g * δ := by
      nlinarith [mul_le_mul_of_nonneg_left hc hg.gap_pos.le]
    calc
      dot u (G.killed A u) = dot (mask A u) (G.transition (mask A u)) := G.killed_quadratic A u
      _ ≤ (1 - g) * energy (mask A u) + g / m * (∑ i, mask A u i) ^ 2 := hg.rayleigh _
      _ ≤ (1 - g + g * ((A.card : ℝ) / m)) * energy (mask A u) := by
        have hs := mul_le_mul_of_nonneg_left (sum_mask_sq_le A u) (div_nonneg hg.gap_pos.le hm.le)
        calc
          _ ≤ (1 - g) * energy (mask A u) + g / m * ((A.card : ℝ) * energy (mask A u)) := add_le_add_right hs _
          _ = _ := by ring
      _ ≤ (1 - g * δ) * energy (mask A u) :=
        mul_le_mul_of_nonneg_right hcoef (energy_nonneg _)
      _ ≤ (1 - g * δ) * energy u :=
        mul_le_mul_of_nonneg_left (energy_mask_le A u) hβ.le

end PortGraph
end QecReliability.ExpanderWalk
