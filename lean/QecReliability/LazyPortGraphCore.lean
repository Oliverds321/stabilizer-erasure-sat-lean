import QecReliability.CenteredSpectralGap

/-! Explicit half-lazy port graphs. Ordinary mean-zero upper spectral control
suffices; positivity is proved from regularity rather than assumed. -/
noncomputable section
namespace QecReliability.ExpanderWalk
open scoped BigOperators
namespace PortGraph
variable {m d : ℕ} (G : PortGraph m d)

def lazyRotation (p : Fin m × Fin (d+d)) : Fin m × Fin (d+d) :=
  Fin.addCases
    (fun i => ((G.rotation (p.1,i)).1, Fin.castAdd d (G.rotation (p.1,i)).2))
    (fun i => (p.1, Fin.natAdd d i)) p.2

theorem lazyRotation_left (v : Fin m) (i : Fin d) :
    G.lazyRotation (v,Fin.castAdd d i) =
      ((G.rotation (v,i)).1, Fin.castAdd d (G.rotation (v,i)).2) := by
  simp [lazyRotation]

theorem lazyRotation_right (v : Fin m) (i : Fin d) :
    G.lazyRotation (v,Fin.natAdd d i) = (v,Fin.natAdd d i) := by
  simp only [lazyRotation, Fin.addCases_right]

theorem lazyRotation_involutive : Function.Involutive G.lazyRotation := by
  rintro ⟨v,i⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [G.lazyRotation_left, G.lazyRotation_left]
    simp only [Prod.mk.eta, G.reverse_reverse (v,j)]
  · rw [G.lazyRotation_right, G.lazyRotation_right]

/-- One holding port for each original port; order m and degree exactly d+d. -/
def lazyGraph : PortGraph m (d+d) where
  vertices_pos := G.vertices_pos
  degree_pos := by have := G.degree_pos; omega
  rotation := ⟨G.lazyRotation, G.lazyRotation, G.lazyRotation_involutive, G.lazyRotation_involutive⟩
  reverse_reverse := G.lazyRotation_involutive

theorem lazy_neighbor_left (v : Fin m) (i : Fin d) :
    G.lazyGraph.neighbor v (Fin.castAdd d i) = G.neighbor v i := by
  exact congrArg Prod.fst (G.lazyRotation_left v i)

theorem lazy_neighbor_right (v : Fin m) (i : Fin d) :
    G.lazyGraph.neighbor v (Fin.natAdd d i) = v := by
  exact congrArg Prod.fst (G.lazyRotation_right v i)

theorem lazy_transition (f : RVec m) :
    G.lazyGraph.transition f = (1/2 : ℝ) • (G.transition f + f) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.degree_pos)
  ext v
  change (∑ i : Fin (d+d), f (G.lazyGraph.neighbor v i)) / ↑(d+d) =
    (1/2 : ℝ) * ((∑ i, f (G.neighbor v i)) / (d : ℝ) + f v)
  rw [Fin.sum_univ_add]
  simp only [G.lazy_neighbor_left, G.lazy_neighbor_right, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add]
  field_simp
  ring

theorem edge_energy (f : RVec m) :
    (∑ p : Fin m × Fin d, (f p.1)^2) = (d : ℝ)*energy f := by
  simp [Fintype.sum_prod_type, energy, dot, sq, Finset.mul_sum, mul_comm]

theorem neighbor_energy (f : RVec m) :
    (∑ p : Fin m × Fin d, (f (G.neighbor p.1 p.2))^2) = (d : ℝ)*energy f := by
  exact (G.rotation.sum_comp (fun p : Fin m × Fin d => (f p.1)^2)).trans (edge_energy (d := d) f)

/-- Every undirected regular normalized walk has quadratic form at least -I. -/
theorem transition_lower (f : RVec m) : -energy f ≤ dot f (G.transition f) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast G.degree_pos
  have hs := Finset.sum_nonneg (s := Finset.univ)
    (fun (p : Fin m × Fin d) (_ : p ∈ Finset.univ) => sq_nonneg (f p.1 + f (G.neighbor p.1 p.2)))
  have he : (∑ p : Fin m × Fin d, (f p.1 + f (G.neighbor p.1 p.2))^2) =
      2*(d : ℝ)*energy f + 2*∑ p : Fin m × Fin d, f p.1*f (G.neighbor p.1 p.2) := by
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, edge_energy, G.neighbor_energy]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  rw [he] at hs
  rw [G.dot_transition]
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem lazy_positive (f : RVec m) : 0 ≤ dot f (G.lazyGraph.transition f) := by
  rw [G.lazy_transition, dot_smul_right, dot_add_right]
  change 0 ≤ (1/2 : ℝ)*(dot f (G.transition f)+energy f)
  linarith [G.transition_lower f]

/-- The normalized upper eigenvalue bound lambda becomes gap (1-lambda)/2.
No absolute-eigenvalue lower bound is required. -/
theorem lazy_positiveGap {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (hupper : ∀ f : RVec m, (∑ i, f i) = 0 →
      dot f (G.transition f) ≤ lam*energy f) :
    G.lazyGraph.PositiveGap ((1-lam)/2) := by
  apply G.lazyGraph.positiveGap_of_centered (by linarith) (by linarith) G.lazy_positive
  intro f hf
  rw [G.lazy_transition, dot_smul_right, dot_add_right]
  change (1/2 : ℝ)*(dot f (G.transition f)+energy f) ≤ _
  nlinarith [hupper f hf]

/-- A convenient rational bound for the manuscript's degree-six LPS choice. -/
theorem lazy_gap_eighth
    (hupper : ∀ f : RVec m, (∑ i, f i) = 0 →
      dot f (G.transition f) ≤ (3/4 : ℝ)*energy f) :
    G.lazyGraph.PositiveGap (1/8) := by
  convert G.lazy_positiveGap (by norm_num : (0:ℝ) ≤ 3/4)
    (by norm_num : (3/4:ℝ) < 1) hupper using 1
  norm_num

end PortGraph
end QecReliability.ExpanderWalk
