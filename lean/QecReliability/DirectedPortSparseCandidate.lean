import QecReliability.CenteredSpectralGap
import QecReliability.CodePadding
import Mathlib.Algebra.BigOperators.Fin

/-!





Messages are independent DIRECTED PORTS. In particular a rotation-fixed loop
still occurs in two DISTINCT local input slots, never as their field sum.
The only external premises are a local systematic-code distance inequality
and a centered upper Rayleigh inequality for the actual supplied PortGraph.
-/

noncomputable section
namespace QecReliability.ExpanderWalk.SparseAmplifierCandidate
open scoped BigOperators
open CodeHash

abbrev Arc (n d : ℕ) := Fin n × Fin d

def supportWeight {ι : Type*} [Fintype ι] (x : ι → F) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

theorem supportWeight_sum {ι : Type*} [Fintype ι] (x : ι → F) :
    supportWeight x = ∑ i, if x i ≠ 0 then 1 else 0 := by
  classical
  simp only [supportWeight, Finset.card_filter]

theorem supportWeight_fin {k : ℕ} (x : Word k) : supportWeight x = weight x := rfl

theorem supportWeight_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → F) : supportWeight (fun i => x (e i)) = supportWeight x := by
  classical
  simp only [supportWeight_sum]
  exact e.sum_comp (fun i => if x i ≠ 0 then (1 : ℕ) else 0)

theorem supportWeight_prod {a b : ℕ} (x : Fin a × Fin b → F) :
    supportWeight x = ∑ v, weight (fun i => x (v, i)) := by
  classical
  simp only [supportWeight_sum, weight, Finset.card_filter, Fintype.sum_prod_type]

theorem weight_append {a b : ℕ} (x : Word a) (y : Word b) :
    weight (Fin.append x y) = weight x + weight y := by
  classical
  simp only [weight, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp

variable {n d : ℕ} (G : PortGraph n d)

def localWord (x : Arc n d → F) (v : Fin n) : Word (d + d) :=
  Fin.append (fun i => x (v, i)) (fun i => x (G.rotation (v, i)))

@[simp] theorem localWord_out (x : Arc n d → F) (v : Fin n) (i : Fin d) :
    (localWord G) x v (Fin.castAdd d i) = x (v, i) := by
  simp [localWord]

@[simp] theorem localWord_in (x : Arc n d → F) (v : Fin n) (i : Fin d) :
    (localWord G) x v (Fin.natAdd d i) = x (G.rotation (v, i)) := by
  exact Fin.append_right _ _ i

/-- Exact multiplicity count. Rotation bijectivity, not loop-freeness, is used. -/
theorem local_incidence (x : Arc n d → F) :
    (∑ v, weight ((localWord G) x v)) = 2 * supportWeight x := by
  calc
    (∑ v, weight ((localWord G) x v)) =
        (∑ v, weight (fun i => x (v, i))) +
        ∑ v, weight (fun i => x (G.rotation (v, i))) := by
      simp only [localWord, weight_append, Finset.sum_add_distrib]
    _ = supportWeight x + supportWeight (fun p => x (G.rotation p)) := by
      rw [supportWeight_prod, supportWeight_prod]
    _ = 2 * supportWeight x := by rw [supportWeight_equiv]; omega

def activeVertices (x : Arc n d → F) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (localWord G) x v ≠ 0)

theorem active_tail {x : Arc n d → F} {p : Arc n d} (hp : x p ≠ 0) :
    p.1 ∈ (activeVertices G) x := by
  classical
  simp only [activeVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hz
  have h := congrFun hz (Fin.castAdd d p.2)
  apply hp
  simpa only [(localWord_out G), Pi.zero_apply, Prod.mk.eta] using h

theorem active_head {x : Arc n d → F} {p : Arc n d} (hp : x p ≠ 0) :
    (G.rotation p).1 ∈ (activeVertices G) x := by
  classical
  simp only [activeVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hz
  have h := congrFun hz (Fin.natAdd d (G.rotation p).2)
  apply hp
  simpa only [(localWord_in G), Pi.zero_apply, Prod.mk.eta, G.reverse_reverse p] using h

def internalPorts (V : Finset (Fin n)) : Finset (Arc n d) :=
  Finset.univ.filter (fun p => p.1 ∈ V ∧ G.neighbor p.1 p.2 ∈ V)

/-- Support inclusion keeps every port occurrence; parallel arcs are not merged. -/
theorem support_le_internal (x : Arc n d → F) :
    supportWeight x ≤ ((internalPorts G) ((activeVertices G) x)).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp only [internalPorts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(active_tail G) hp, (active_head G) hp⟩

def indicator (V : Finset (Fin n)) : RVec n := fun v => if v ∈ V then 1 else 0

theorem indicator_sum (V : Finset (Fin n)) :
    (∑ v, indicator V v) = (V.card : ℝ) := by
  classical
  simp [indicator]

theorem indicator_energy (V : Finset (Fin n)) :
    energy (indicator V) = (V.card : ℝ) := by
  classical
  calc
    energy (indicator V) = ∑ v, indicator V v := by
      unfold energy dot
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ V <;> simp [indicator, hv]
    _ = (V.card : ℝ) := indicator_sum V

/-- EXACT directed-port normalization: no factor two, no distinct-neighbor count. -/
theorem internalPorts_exact (V : Finset (Fin n)) :
    (((internalPorts G) V).card : ℝ) =
      (d : ℝ) * dot (indicator V) (G.transition (indicator V)) := by
  classical
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.degree_pos)
  have hc : (((internalPorts G) V).card : ℝ) =
      ∑ p : Arc n d, indicator V p.1 * indicator V (G.neighbor p.1 p.2) := by
    simp only [internalPorts, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases ht : p.1 ∈ V <;> by_cases hh : G.neighbor p.1 p.2 ∈ V <;>
      simp [indicator, ht, hh]
  rw [G.dot_transition, ← hc]
  field_simp

/-- Mean decomposition without a PSD premise; only the centered upper bound is used.
Nonnegativity of lambda is explicit because the negative mean correction is dropped. -/
theorem centered_rayleigh_loose {lam : ℝ} (hlam : 0 ≤ lam)
    (hupper : ∀ f : RVec n, (∑ v, f v) = 0 →
      dot f (G.transition f) ≤ lam * energy f) (f : RVec n) :
    dot f (G.transition f) ≤ (∑ v, f v)^2 / (n : ℝ) + lam * energy f := by
  have hn : (0 : ℝ) < n := by exact_mod_cast G.vertices_pos
  let c : ℝ := (∑ v, f v) / (n : ℝ)
  let u : RVec n := f - (fun _ => c)
  have hc : (n : ℝ) * c = ∑ v, f v := by dsimp [c]; field_simp [ne_of_gt hn]
  have hu : (∑ v, u v) = 0 := by
    simp only [u, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have he : energy u = energy f - (n : ℝ) * c^2 := by
    simp only [u, energy, dot_sub_left, dot_sub_right]
    rw [dot_comm f (fun _ => c), PortGraph.dot_const, PortGraph.dot_const]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hc]
    ring
  have ht : dot u (G.transition u) = dot f (G.transition f) - (n : ℝ) * c^2 := by
    simp only [u, map_sub, G.transition_const, dot_sub_left, dot_sub_right]
    rw [dot_comm f (fun _ => c), PortGraph.dot_const, PortGraph.dot_const,
      PortGraph.dot_const, G.transition_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← hc]
    ring
  have hh := hupper u hu
  rw [ht, he] at hh
  have hm : (∑ v, f v)^2 / (n : ℝ) = (n : ℝ) * c^2 := by
    rw [← hc]
    field_simp [ne_of_gt hn]
  rw [hm]
  have hcorrection : 0 ≤ lam * (n : ℝ) * c^2 :=
    mul_nonneg (mul_nonneg hlam hn.le) (sq_nonneg c)
  nlinarith

/-- The finite port-count inequality supplied to the sparse-weight argument. -/
theorem internalPorts_spectral {lam : ℝ} (hlam : 0 ≤ lam)
    (hupper : ∀ f : RVec n, (∑ v, f v) = 0 →
      dot f (G.transition f) ≤ lam * energy f) (V : Finset (Fin n)) :
    (((internalPorts G) V).card : ℝ) ≤
      (d : ℝ) * ((V.card : ℝ)^2 / (n : ℝ) + lam * (V.card : ℝ)) := by
  rw [(internalPorts_exact G)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  simpa only [indicator_sum, indicator_energy] using
    (centered_rayleigh_loose G) hlam hupper (indicator V)

def parityWeight (A : Word (d + d) →ₗ[F] Word (d / 4)) (x : Arc n d → F) : ℕ :=
  ∑ v, weight (A ((localWord G) x v))

/-- Distance is imposed on the systematic word, not on parity alone. -/
theorem local_distance_budget
    (A : Word (d + d) →ₗ[F] Word (d / 4))
    (hlocal : ∀ z : Word (d + d), z ≠ 0 →
      (d : ℝ) / 256 ≤ (weight z : ℝ) + (weight (A z) : ℝ))
    (x : Arc n d → F) :
    (d : ℝ) / 256 * (((activeVertices G) x).card : ℝ) ≤
      2 * (supportWeight x : ℝ) + ((parityWeight G) A x : ℝ) := by
  classical
  have hp (v : Fin n) :
      (if v ∈ (activeVertices G) x then (d : ℝ) / 256 else 0) ≤
        (weight ((localWord G) x v) : ℝ) + (weight (A ((localWord G) x v)) : ℝ) := by
    by_cases hv : v ∈ (activeVertices G) x
    · rw [if_pos hv]
      apply hlocal
      simpa only [activeVertices, Finset.mem_filter, Finset.mem_univ, true_and] using hv
    · rw [if_neg hv]
      positivity
  have hs := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hp v)
  have hi : (∑ v, (weight ((localWord G) x v) : ℝ)) = 2 * (supportWeight x : ℝ) := by
    exact_mod_cast (local_incidence G) x
  have ht : (∑ v, (weight (A ((localWord G) x v)) : ℝ)) =
      ((parityWeight G) A x : ℝ) := by simp only [parityWeight, Nat.cast_sum]
  have hl : (∑ v, if v ∈ (activeVertices G) x then (d : ℝ) / 256 else 0) =
      (d : ℝ) / 256 * (((activeVertices G) x).card : ℝ) := by
    simp [mul_comm]
  rw [hl, Finset.sum_add_distrib, hi, ht] at hs
  exact hs

/-- Adapter from the finite local code's INTEGER distance. Divisibility
is what identifies natural D/256 with the rational threshold used above. -/
theorem local_distance_of_systematic
    (A : Word (d + d) →ₗ[F] Word (d / 4)) (hd256 : 256 ∣ d)
    (hcode : ∀ z : Word (d + d), z ≠ 0 →
      d / 256 ≤ weight (Fin.append z (A z)))
    (z : Word (d + d)) (hz : z ≠ 0) :
    (d : ℝ) / 256 ≤ (weight z : ℝ) + (weight (A z) : ℝ) := by
  have hd : d / 256 * 256 = d := Nat.div_mul_cancel hd256
  have hd' : ((d / 256 : ℕ) : ℝ) * 256 = (d : ℝ) := by exact_mod_cast hd
  have hh := hcode z hz
  rw [weight_append] at hh
  have hh' : ((d / 256 : ℕ) : ℝ) ≤ (weight z : ℝ) + (weight (A z) : ℝ) := by
    exact_mod_cast hh
  linarith

/-- Fixed-constant contradiction. The actual coefficient is 7/16, not merely 1/2. -/
theorem sparse_numeric {beta a lam : ℝ}
    (hb : 0 < beta) (hbmax : beta ≤ 1 / 2359296)
    (ha : 0 ≤ a) (halocal : a ≤ 768 * beta)
    (hlam : lam ≤ 1 / 4096) (hports : beta ≤ a^2 + lam * a) : False := by
  have hsquare : a * a ≤ (768 * beta) * (768 * beta) :=
    mul_le_mul halocal halocal ha (by positivity)
  have hb2 : beta * beta ≤ (1 / 2359296 : ℝ) * beta :=
    mul_le_mul_of_nonneg_right hbmax hb.le
  have hla : lam * a ≤ (1 / 4096 : ℝ) * a :=
    mul_le_mul_of_nonneg_right hlam ha
  have hla2 : (1 / 4096 : ℝ) * a ≤ (1 / 4096 : ℝ) * (768 * beta) :=
    mul_le_mul_of_nonneg_left halocal (by norm_num)
  nlinarith

/-- Main directed-port sparse amplifier. All hypotheses concern the actual G and A. -/
theorem directed_sparse_amplification
    (A : Word (d + d) →ₗ[F] Word (d / 4))
    (hlocal : ∀ z : Word (d + d), z ≠ 0 →
      (d : ℝ) / 256 ≤ (weight z : ℝ) + (weight (A z) : ℝ))
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 4096)
    (hupper : ∀ f : RVec n, (∑ v, f v) = 0 →
      dot f (G.transition f) ≤ lam * energy f)
    (x : Arc n d → F) (hx : 0 < supportWeight x)
    (hsparse : (supportWeight x : ℝ) ≤ (1 / 2359296 : ℝ) * ((n * d : ℕ) : ℝ)) :
    supportWeight x < (parityWeight G) A x := by
  by_contra hnot
  have ht : (parityWeight G) A x ≤ supportWeight x := Nat.le_of_not_gt hnot
  have hn : (0 : ℝ) < n := by exact_mod_cast G.vertices_pos
  have hd : (0 : ℝ) < d := by exact_mod_cast G.degree_pos
  have hM : (0 : ℝ) < (d : ℝ) * (n : ℝ) := mul_pos hd hn
  let a : ℝ := (((activeVertices G) x).card : ℝ) / (n : ℝ)
  let beta : ℝ := (supportWeight x : ℝ) / ((d : ℝ) * (n : ℝ))
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hn.le
  have hb : 0 < beta := div_pos (by exact_mod_cast hx) hM
  have haN : a * (n : ℝ) = (((activeVertices G) x).card : ℝ) := by
    dsimp [a]
    exact div_mul_cancel₀ _ (ne_of_gt hn)
  have hbM : beta * ((d : ℝ) * (n : ℝ)) = (supportWeight x : ℝ) := by
    dsimp [beta]
    exact div_mul_cancel₀ _ (ne_of_gt hM)
  have hbmax : beta ≤ 1 / 2359296 := by
    apply (div_le_iff₀ hM).mpr
    simpa only [Nat.cast_mul, mul_comm] using hsparse
  have hlocal' := (local_distance_budget G) A hlocal x
  have ht' : ((parityWeight G) A x : ℝ) ≤ (supportWeight x : ℝ) := by exact_mod_cast ht
  have hlscaled : ((1 / 256 : ℝ) * a) * ((d : ℝ) * (n : ℝ)) ≤
      (3 * beta) * ((d : ℝ) * (n : ℝ)) := by
    calc
      _ = (d : ℝ) / 256 * (((activeVertices G) x).card : ℝ) := by rw [← haN]; ring
      _ ≤ 2 * (supportWeight x : ℝ) + ((parityWeight G) A x : ℝ) := hlocal'
      _ ≤ 3 * (supportWeight x : ℝ) := by linarith
      _ = _ := by rw [← hbM]; ring
  have hl : (1 / 256 : ℝ) * a ≤ 3 * beta :=
    (mul_le_mul_iff_left₀ hM).mp hlscaled
  have halocal : a ≤ 768 * beta := by linarith
  have hsupport : (supportWeight x : ℝ) ≤
      (((internalPorts G) ((activeVertices G) x)).card : ℝ) := by
    exact_mod_cast (support_le_internal G) x
  have hs := hsupport.trans ((internalPorts_spectral G) hlam0 hupper ((activeVertices G) x))
  have hrhs : (d : ℝ) * ((((activeVertices G) x).card : ℝ)^2 / (n : ℝ) +
      lam * (((activeVertices G) x).card : ℝ)) =
      (a^2 + lam * a) * ((d : ℝ) * (n : ℝ)) := by
    rw [← haN]
    field_simp [ne_of_gt hn]
  rw [hrhs, ← hbM] at hs
  have hports : beta ≤ a^2 + lam * a := (mul_le_mul_iff_left₀ hM).mp hs
  exact sparse_numeric hb hbmax ha halocal hlam hports

end QecReliability.ExpanderWalk.SparseAmplifierCandidate
