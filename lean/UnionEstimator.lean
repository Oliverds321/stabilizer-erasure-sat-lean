import HybridEstimator

set_option autoImplicit false

/-!
# The Karp–Luby–Madras union estimator: mean and variance

Finite family `terms`, layer `layer`, weight `g`. The sample space is the set of pairs
`P = {(M, E) : M ∈ terms, E ∈ layer, M ⊆ E}` with the uniform distribution, and the sample is
`X(M, E) = |P| · g(E) / ν(E)`, where `ν(E) = #{M ∈ terms : M ⊆ E}`. With
`U = {E ∈ layer : ∃ M ∈ terms, M ⊆ E}` (equivalently `ν(E) > 0`) and `G = Σ_{E ∈ U} g(E)`:

V1. Mean: `(1/|P|) Σ_P X = G` (unbiasedness).
V2. Second moment: if `0 < gmin ≤ g ≤ gmax` and `ν ≤ νmax` on `U`, then
    `(1/|P|) Σ_P X² ≤ νmax · (gmax/gmin) · G²`, hence the variance is at most
    `(νmax · gmax/gmin - 1) · G²`.
V3. Stabilizer specialisation: `terms` a list of uncorrectable sets, layer `|E| = j`,
    `g = infidelityScore`; then `gmin = 1/2`, `gmax = 1`, and the second moment is at most
    `2 νmax G²`, where `G` is the full layer sum `Σ_{|E|=j} (1 - 2^{-d_E})` when the list
    contains all minimal uncorrectable sets of size `≤ w` and `j ≤ w`.
-/

noncomputable section

namespace QecPhysical.Stabilizer.UnionEstimator

open scoped BigOperators
open Finset
open QecReliability QecReliability.Binary
open QecPhysical.Stabilizer.Uncorrectable

variable {α : Type*} [DecidableEq α]

/-- The sample space `P`. -/
def pairs (terms layer : Finset (Finset α)) : Finset (Finset α × Finset α) :=
  (terms ×ˢ layer).filter (fun x => x.1 ⊆ x.2)

/-- `ν(E)`: number of listed sets contained in `E`. -/
def nu (terms : Finset (Finset α)) (E : Finset α) : ℕ := (terms.filter (fun M => M ⊆ E)).card

/-- The union `U` of the up-sets of the listed sets inside the layer. -/
def unionLayer (terms layer : Finset (Finset α)) : Finset (Finset α) :=
  layer.filter (fun E => ∃ M ∈ terms, M ⊆ E)

/-- The target `G = Σ_{E ∈ U} g(E)`. -/
def unionSum (terms layer : Finset (Finset α)) (g : Finset α → ℝ) : ℝ :=
  ∑ E ∈ unionLayer terms layer, g E

/-- The estimator `X(M, E) = |P| g(E) / ν(E)`. -/
def sample (terms layer : Finset (Finset α)) (g : Finset α → ℝ) (x : Finset α × Finset α) : ℝ :=
  ((pairs terms layer).card : ℝ) * g x.2 / (nu terms x.2 : ℝ)

theorem nu_pos_iff (terms : Finset (Finset α)) (E : Finset α) :
    0 < nu terms E ↔ ∃ M ∈ terms, M ⊆ E := by
  unfold nu
  rw [Finset.card_pos, Finset.filter_nonempty_iff]

theorem mem_unionLayer {terms layer : Finset (Finset α)} {E : Finset α} :
    E ∈ unionLayer terms layer ↔ E ∈ layer ∧ ∃ M ∈ terms, M ⊆ E := by
  unfold unionLayer
  rw [Finset.mem_filter]

theorem unionLayer_eq_nu_pos (terms layer : Finset (Finset α)) :
    unionLayer terms layer = layer.filter (fun E => 0 < nu terms E) := by
  unfold unionLayer
  exact Finset.filter_congr (fun E _ => (nu_pos_iff terms E).symm)

/-- Sums over `P` of functions of `E` are `ν`-weighted layer sums. -/
theorem sum_pairs (terms layer : Finset (Finset α)) (f : Finset α → ℝ) :
    ∑ x ∈ pairs terms layer, f x.2 = ∑ E ∈ layer, (nu terms E : ℝ) * f E := by
  unfold pairs
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  rw [← Finset.sum_filter]
  change ∑ _a ∈ terms.filter (fun M => M ⊆ E), f E = _
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

theorem sum_layer_nu_mul (terms layer : Finset (Finset α)) (F : Finset α → ℝ) :
    ∑ E ∈ layer, (nu terms E : ℝ) * F E =
      ∑ E ∈ unionLayer terms layer, (nu terms E : ℝ) * F E := by
  unfold unionLayer
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  split_ifs with h
  · rfl
  · have : nu terms E = 0 := by
      by_contra h0
      exact h ((nu_pos_iff terms E).mp (Nat.pos_of_ne_zero h0))
    simp [this]

theorem nu_pos_of_mem {terms layer : Finset (Finset α)} {E : Finset α}
    (hE : E ∈ unionLayer terms layer) : (0 : ℝ) < nu terms E := by
  exact_mod_cast (nu_pos_iff terms E).mpr (mem_unionLayer.mp hE).2

/-- `|P| = Σ_{E ∈ U} ν(E)`. -/
theorem card_pairs (terms layer : Finset (Finset α)) :
    ((pairs terms layer).card : ℝ) = ∑ E ∈ unionLayer terms layer, (nu terms E : ℝ) := by
  have h := sum_pairs terms layer (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  have h2 := sum_layer_nu_mul terms layer (fun _ => 1)
  simpa using h2

theorem sum_pairs_div (terms layer : Finset (Finset α)) (g : Finset α → ℝ) :
    ∑ x ∈ pairs terms layer, g x.2 / (nu terms x.2 : ℝ) = unionSum terms layer g := by
  rw [sum_pairs terms layer (fun E => g E / (nu terms E : ℝ)),
    sum_layer_nu_mul terms layer (fun E => g E / (nu terms E : ℝ))]
  unfold unionSum
  refine Finset.sum_congr rfl (fun E hE => ?_)
  have := nu_pos_of_mem hE
  field_simp

/-- **V1 (sum form).** `Σ_P X = |P| · G`. -/
theorem sum_sample (terms layer : Finset (Finset α)) (g : Finset α → ℝ) :
    ∑ x ∈ pairs terms layer, sample terms layer g x =
      ((pairs terms layer).card : ℝ) * unionSum terms layer g := by
  unfold sample
  simp_rw [mul_div_assoc]
  rw [← Finset.mul_sum, sum_pairs_div]

/-- **V1 (mean).** The estimator is unbiased: `(1/|P|) Σ_P X = G`. -/
theorem mean_sample (terms layer : Finset (Finset α)) (g : Finset α → ℝ)
    (hP : (pairs terms layer).Nonempty) :
    (∑ x ∈ pairs terms layer, sample terms layer g x) / ((pairs terms layer).card : ℝ) =
      unionSum terms layer g := by
  have hc : ((pairs terms layer).card : ℝ) ≠ 0 := by exact_mod_cast hP.card_pos.ne'
  rw [sum_sample]
  field_simp

/-- The mean identity agrees with the existing Karp–Luby union identity of `HybridEstimator`. -/
theorem unionSum_eq_karpLuby (terms layer : Finset (Finset α)) (g : Finset α → ℝ) :
    unionSum terms layer g = ∑ M ∈ terms, ∑ E ∈ layer.filter (fun E => M ⊆ E),
      g E / ((terms.filter (fun M' => M' ⊆ E)).card : ℝ) :=
  sum_union_eq_karpLuby terms layer g

/-- Second-moment identity: `Σ_P X² = |P|² Σ_{E ∈ U} g(E)²/ν(E)`. -/
theorem sum_sample_sq (terms layer : Finset (Finset α)) (g : Finset α → ℝ) :
    ∑ x ∈ pairs terms layer, sample terms layer g x ^ 2 =
      ((pairs terms layer).card : ℝ) ^ 2 *
        ∑ E ∈ unionLayer terms layer, g E ^ 2 / (nu terms E : ℝ) := by
  unfold sample
  rw [sum_pairs terms layer
      (fun E => (((pairs terms layer).card : ℝ) * g E / (nu terms E : ℝ)) ^ 2),
    sum_layer_nu_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun E hE => ?_)
  have := nu_pos_of_mem hE
  field_simp

/-- **V2.** Second-moment bound
`(1/|P|) Σ_P X² ≤ νmax · (gmax/gmin) · G²`. -/
theorem second_moment_le (terms layer : Finset (Finset α)) (g : Finset α → ℝ)
    {gmin gmax νmax : ℝ} (hgmin : 0 < gmin)
    (hg : ∀ E ∈ unionLayer terms layer, gmin ≤ g E ∧ g E ≤ gmax)
    (hν : ∀ E ∈ unionLayer terms layer, (nu terms E : ℝ) ≤ νmax)
    (hP : (pairs terms layer).Nonempty) :
    (∑ x ∈ pairs terms layer, sample terms layer g x ^ 2) / ((pairs terms layer).card : ℝ) ≤
      νmax * (gmax / gmin) * unionSum terms layer g ^ 2 := by
  set U := unionLayer terms layer
  set G := unionSum terms layer g
  set c : ℝ := ((pairs terms layer).card : ℝ)
  set T := ∑ E ∈ U, g E ^ 2 / (nu terms E : ℝ)
  have hc0 : 0 < c := Nat.cast_pos.mpr hP.card_pos
  have hlhs : (∑ x ∈ pairs terms layer, sample terms layer g x ^ 2) / c = c * T := by
    rw [sum_sample_sq]
    change c ^ 2 * T / c = c * T
    field_simp
  rw [hlhs]
  -- U is nonempty
  obtain ⟨x, hx⟩ := hP
  have hxU : x.2 ∈ U := by
    unfold pairs at hx
    obtain ⟨hprod, hsub⟩ := Finset.mem_filter.mp hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hprod
    exact mem_unionLayer.mpr ⟨h2, x.1, h1, hsub⟩
  have hgx := hg x.2 hxU
  have hgmax : 0 ≤ gmax := by linarith [hgx.1, hgx.2]
  have hνmax : 0 ≤ νmax := (nu_pos_of_mem hxU).le.trans (hν x.2 hxU)
  have hgnn : ∀ E ∈ U, 0 ≤ g E := fun E hE => hgmin.le.trans (hg E hE).1
  have hG : 0 ≤ G := Finset.sum_nonneg hgnn
  have hT : 0 ≤ T := Finset.sum_nonneg (fun E hE => div_nonneg (sq_nonneg _) (nu_pos_of_mem hE).le)
  have h1 : c ≤ νmax * U.card := by
    change ((pairs terms layer).card : ℝ) ≤ _
    rw [card_pairs]
    calc ∑ E ∈ U, (nu terms E : ℝ) ≤ ∑ _E ∈ U, νmax := Finset.sum_le_sum hν
      _ = νmax * U.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h2 : (U.card : ℝ) * gmin ≤ G := by
    calc (U.card : ℝ) * gmin = ∑ _E ∈ U, gmin := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ G := Finset.sum_le_sum (fun E hE => (hg E hE).1)
  have h2' : (U.card : ℝ) ≤ G / gmin := by rw [le_div_iff₀ hgmin]; exact h2
  have h3 : T ≤ gmax * G := by
    calc T ≤ ∑ E ∈ U, g E ^ 2 := Finset.sum_le_sum (fun E hE => by
          have hn := nu_pos_of_mem hE
          have h1' : (1 : ℝ) ≤ nu terms E := by
            have : 0 < nu terms E := by exact_mod_cast hn
            exact_mod_cast this
          exact div_le_self (sq_nonneg _) h1')
      _ ≤ ∑ E ∈ U, gmax * g E := Finset.sum_le_sum (fun E hE => by
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hg E hE).2 (hgnn E hE))
      _ = gmax * G := by rw [← Finset.mul_sum]; rfl
  calc c * T ≤ (νmax * U.card) * (gmax * G) :=
        mul_le_mul h1 h3 hT (mul_nonneg hνmax (Nat.cast_nonneg _))
    _ ≤ (νmax * (G / gmin)) * (gmax * G) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2' hνmax)
          (mul_nonneg hgmax hG)
    _ = νmax * (gmax / gmin) * G ^ 2 := by ring

/-- **V2 (variance).** `(1/|P|) Σ_P (X - G)² ≤ (νmax · gmax/gmin - 1) · G²`. -/
theorem variance_le (terms layer : Finset (Finset α)) (g : Finset α → ℝ)
    {gmin gmax νmax : ℝ} (hgmin : 0 < gmin)
    (hg : ∀ E ∈ unionLayer terms layer, gmin ≤ g E ∧ g E ≤ gmax)
    (hν : ∀ E ∈ unionLayer terms layer, (nu terms E : ℝ) ≤ νmax)
    (hP : (pairs terms layer).Nonempty) :
    (∑ x ∈ pairs terms layer, (sample terms layer g x - unionSum terms layer g) ^ 2) /
        ((pairs terms layer).card : ℝ) ≤
      (νmax * (gmax / gmin) - 1) * unionSum terms layer g ^ 2 := by
  have hc0 : (0 : ℝ) < (pairs terms layer).card := by exact_mod_cast hP.card_pos
  have hexp : ∑ x ∈ pairs terms layer, (sample terms layer g x - unionSum terms layer g) ^ 2 =
      ∑ x ∈ pairs terms layer, sample terms layer g x ^ 2 -
        ((pairs terms layer).card : ℝ) * unionSum terms layer g ^ 2 := by
    have h : ∀ x ∈ pairs terms layer, (sample terms layer g x - unionSum terms layer g) ^ 2 =
        sample terms layer g x ^ 2 - 2 * unionSum terms layer g * sample terms layer g x +
          unionSum terms layer g ^ 2 := fun x _ => by ring
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_sample, Finset.sum_const, nsmul_eq_mul]
    ring
  have hb := second_moment_le terms layer g hgmin hg hν hP
  rw [hexp, sub_div, mul_div_cancel_left₀ _ hc0.ne']
  linarith

/-! ## V3. Stabilizer specialisation -/

variable {n : ℕ}

/-- On the union of up-sets of listed uncorrectable sets, `1/2 ≤ 1 - 2^{-d_E} ≤ 1`. -/
theorem infidelityScore_bounds_on_union (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (mins layer : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M)) :
    ∀ E ∈ unionLayer mins layer, (1 / 2 : ℝ) ≤ infidelityScore S E ∧ infidelityScore S E ≤ 1 := by
  intro E hE
  obtain ⟨_, M, hM, hME⟩ := mem_unionLayer.mp hE
  have hpos := uncorrectable_mono S hS hME (hunc M hM)
  have h := infidelityScore_le_uncorrectable S E
  have hu : uncorrectable S E = 1 := by unfold uncorrectable; rw [if_pos hpos]
  rw [hu] at h
  constructor <;> linarith [h.1, h.2]

/-- For a list containing all minimal uncorrectable sets of size `≤ w` and `j ≤ w`, the target
`G` of the union estimator is the full layer sum of the infidelity scores. -/
theorem unionSum_eq_layer_sum (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {j : ℕ} (hj : j ≤ w) :
    unionSum mins (univ.filter (fun E : Finset (Fin n) => E.card = j)) (infidelityScore S) =
      ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j), infidelityScore S E := by
  rw [unionSum_eq_karpLuby, layer_sum_infidelityScore_eq_karpLuby S hS w mins hunc hcover hj]

/-- **V3.** For the layer `|E| = j` with weight `1 - 2^{-d_E}`:
the estimator is unbiased for the layer sum and its second moment is at most `2 νmax G²`
(relative variance at most `2 νmax - 1`). -/
theorem stabilizer_union_estimator (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {j : ℕ} (hj : j ≤ w) {νmax : ℝ}
    (hν : ∀ E ∈ unionLayer mins (univ.filter (fun E : Finset (Fin n) => E.card = j)),
      (nu mins E : ℝ) ≤ νmax)
    (hP : (pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j))).Nonempty) :
    (∑ x ∈ pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j)),
        sample mins (univ.filter (fun E : Finset (Fin n) => E.card = j)) (infidelityScore S) x) /
        ((pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j))).card : ℝ) =
      ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j), infidelityScore S E ∧
    (∑ x ∈ pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j)),
        sample mins (univ.filter (fun E : Finset (Fin n) => E.card = j)) (infidelityScore S) x ^ 2) /
        ((pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j))).card : ℝ) ≤
      2 * νmax * (∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j),
        infidelityScore S E) ^ 2 := by
  have hb := infidelityScore_bounds_on_union S hS mins
    (univ.filter (fun E : Finset (Fin n) => E.card = j)) hunc
  have hG := unionSum_eq_layer_sum S hS w mins hunc hcover hj
  refine ⟨by rw [mean_sample _ _ _ hP, hG], ?_⟩
  have h := second_moment_le mins (univ.filter (fun E : Finset (Fin n) => E.card = j))
    (infidelityScore S) (by norm_num : (0 : ℝ) < 1 / 2) hb hν hP
  rw [hG] at h
  calc _ ≤ νmax * (1 / (1 / 2)) * _ := h
    _ = _ := by ring

end QecPhysical.Stabilizer.UnionEstimator

#print axioms QecPhysical.Stabilizer.UnionEstimator.sum_pairs
#print axioms QecPhysical.Stabilizer.UnionEstimator.card_pairs
#print axioms QecPhysical.Stabilizer.UnionEstimator.sum_sample
#print axioms QecPhysical.Stabilizer.UnionEstimator.mean_sample
#print axioms QecPhysical.Stabilizer.UnionEstimator.unionSum_eq_karpLuby
#print axioms QecPhysical.Stabilizer.UnionEstimator.sum_sample_sq
#print axioms QecPhysical.Stabilizer.UnionEstimator.second_moment_le
#print axioms QecPhysical.Stabilizer.UnionEstimator.variance_le
#print axioms QecPhysical.Stabilizer.UnionEstimator.unionSum_eq_layer_sum
#print axioms QecPhysical.Stabilizer.UnionEstimator.stabilizer_union_estimator
