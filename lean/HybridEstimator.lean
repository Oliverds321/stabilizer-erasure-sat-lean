import PointHardness
import PhysicalBridge.AmbiguityRank

set_option autoImplicit false

/-!
# Identities behind the hybrid erasure estimator

D1. Rank formula `dim N_E + s = 2|E| + dim S_{Eᶜ}`.
D2. Duality `d_E + d_{Eᶜ} = 2(n - s)` and the score form `2^{-d_E} = 4^{-k} 2^{d_{Eᶜ}}`.
D3. Layer form of the duality (sum form and `layerAverage` form).
U1. Minimal uncorrectable sets and the "contains a listed minimal set" criterion.
U2. Karp–Luby union identity and its specialisation to correctable-vanishing scores.
C1. Coefficientwise relative error passes to the Bernstein curve.
-/

noncomputable section

namespace QecPhysical.Stabilizer.Uncorrectable

open scoped BigOperators
open Module
open QecReliability
open QecReliability.Binary
open QecPhysical.BinaryPauli

variable {n : ℕ}

/-! ## D1. Rank formula -/

theorem localized_eq_normalizer_sup (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    localized (symplectic n) S (supported E) =
      normalizer (symplectic n) (S ⊔ supported Eᶜ) := by
  rw [normalizer, orthogonal_sup, orthogonal_supported, compl_compl]
  rfl

/-- **D1. Rank formula** (no isotropy needed). -/
theorem finrank_localized_add_finrank (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    finrank Bit (localized (symplectic n) S (supported E)) + finrank Bit S =
      2 * E.card + finrank Bit (S ⊓ supported Eᶜ : Submodule Bit (Pauli n)) := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq S (supported Eᶜ)
  have ho := finrank_normalizer (S ⊔ supported Eᶜ)
  rw [← localized_eq_normalizer_sup] at ho
  rw [BinaryElimination.supported_finrank] at hs
  have hcard : E.card + Eᶜ.card = n := by simp
  have hle : finrank Bit (S ⊔ supported Eᶜ : Submodule Bit (Pauli n)) ≤ 2 * n := by
    simpa [two_mul] using Submodule.finrank_le (S ⊔ supported Eᶜ : Submodule Bit (Pauli n))
  omega

/-- The natural subtraction in `ambiguity` is honest for isotropic `S`. -/
theorem finrank_inf_le_localized (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (E : Finset (Fin n)) :
    finrank Bit (S ⊓ supported E : Submodule Bit (Pauli n)) ≤
      finrank Bit (localized (symplectic n) S (supported E)) :=
  Submodule.finrank_mono (fun _ hx => ⟨hS hx.1, hx.2⟩)

/-! ## D2. Duality -/

/-- **D2. Duality.** `d_E + d_{Eᶜ} = 2 (n - s)` for isotropic `S`. -/
theorem ambiguity_add_ambiguity_compl (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (E : Finset (Fin n)) :
    ambiguity (symplectic n) S (supported E) + ambiguity (symplectic n) S (supported Eᶜ) =
      2 * (n - finrank Bit S) := by
  have h1 := finrank_localized_add_finrank S E
  have h2 := finrank_localized_add_finrank S Eᶜ
  rw [compl_compl] at h2
  have l1 := finrank_inf_le_localized S hS E
  have l2 := finrank_inf_le_localized S hS Eᶜ
  have hs := isotropic_finrank_le S hS
  have hcard : E.card + Eᶜ.card = n := by simp
  unfold ambiguity
  omega

/-- **D2, score form.** `2^{-d_E} = 4^{-(n-s)} · 2^{d_{Eᶜ}}`. -/
theorem erasureScore_eq_dual (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (E : Finset (Fin n)) :
    erasureScore S E = ((4:ℝ) ^ (n - finrank Bit S))⁻¹ *
      (2:ℝ) ^ ambiguity (symplectic n) S (supported Eᶜ) := by
  have hab := ambiguity_add_ambiguity_compl S hS E
  have h4 : (4:ℝ) ^ (n - finrank Bit S) =
      (2:ℝ) ^ ambiguity (symplectic n) S (supported E) *
        (2:ℝ) ^ ambiguity (symplectic n) S (supported Eᶜ) := by
    rw [← pow_add, hab, pow_mul]
    norm_num
  unfold erasureScore
  rw [h4, mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]

/-! ## D3. Layer form of the duality -/

/-- **D3, sum form.** -/
theorem sum_layer_erasureScore_dual (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {j : ℕ} (hj : j ≤ n) :
    ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = j), erasureScore S E =
      ((4:ℝ) ^ (n - finrank Bit S))⁻¹ *
        ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = n - j),
          (2:ℝ) ^ ambiguity (symplectic n) S (supported E) := by
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun E => Eᶜ) (fun E => Eᶜ) ?_ ?_ ?_ ?_ ?_
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE ⊢
    rw [Finset.card_compl, Fintype.card_fin, hE]
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE ⊢
    rw [Finset.card_compl, Fintype.card_fin, hE]
    omega
  · intro E _
    exact compl_compl E
  · intro E _
    exact compl_compl E
  · intro E _
    exact erasureScore_eq_dual S hS E

theorem layerAverage_id_eq (f : Finset (Fin n) → ℝ) (j : Fin (n + 1)) :
    layerAverage (id : Causes n → Finset (Fin n)) f j =
      (∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = j.val), f E) /
        (n.choose j.val : ℝ) := by
  unfold layerAverage
  congr 1
  rw [Finset.sum_subtype (Finset.univ.filter (fun E : Finset (Fin n) => E.card = j.val))
    (p := fun b : Causes n => hammingLayer b = j)]
  · rfl
  · intro E
    simp [hammingLayer, Fin.ext_iff]

/-- **D3, layer-average form.** -/
theorem layerAverage_erasureScore_dual (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (j : Fin (n + 1)) :
    layerAverage (id : Causes n → Finset (Fin n)) (erasureScore S) j =
      ((4:ℝ) ^ (n - finrank Bit S))⁻¹ *
        layerAverage (id : Causes n → Finset (Fin n))
          (fun E => (2:ℝ) ^ ambiguity (symplectic n) S (supported E))
          ⟨n - j.val, by omega⟩ := by
  have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  rw [layerAverage_id_eq, layerAverage_id_eq, sum_layer_erasureScore_dual S hS hj]
  simp only
  rw [Nat.choose_symm hj, mul_div_assoc]

/-! ## U1. Minimal uncorrectable sets -/

/-- `M` is uncorrectable and every proper subset is correctable. -/
def IsMinimalUncorrectable (S : Submodule Bit (Pauli n)) (M : Finset (Fin n)) : Prop :=
  0 < ambiguity (symplectic n) S (supported M) ∧
    ∀ M' ⊂ M, ¬ 0 < ambiguity (symplectic n) S (supported M')

/-- **U1(a).** Every uncorrectable set contains a minimal uncorrectable set. -/
theorem exists_minimalUncorrectable_subset (S : Submodule Bit (Pauli n))
    (E : Finset (Fin n)) (hE : 0 < ambiguity (symplectic n) S (supported E)) :
    ∃ M ⊆ E, IsMinimalUncorrectable S M := by
  refine Finset.strongInduction
    (p := fun E => 0 < ambiguity (symplectic n) S (supported E) →
      ∃ M ⊆ E, IsMinimalUncorrectable S M) ?_ E hE
  intro E ih hE
  by_cases h : ∀ M' ⊂ E, ¬ 0 < ambiguity (symplectic n) S (supported M')
  · exact ⟨E, subset_refl _, hE, h⟩
  · push Not at h
    obtain ⟨M', hM', hpos⟩ := h
    obtain ⟨M, hMM', hmin⟩ := ih M' hM' hpos
    exact ⟨M, hMM'.trans hM'.subset, hmin⟩

/-- **U1(b).** Uncorrectability of a set of size `≤ w` is decided by a family containing all
minimal uncorrectable sets of size `≤ w` (and only uncorrectable sets). -/
theorem uncorrectable_iff_exists_mins (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    (E : Finset (Fin n)) (hE : E.card ≤ w) :
    0 < ambiguity (symplectic n) S (supported E) ↔ ∃ M ∈ mins, M ⊆ E := by
  constructor
  · intro h
    obtain ⟨M, hME, hmin⟩ := exists_minimalUncorrectable_subset S E h
    exact ⟨M, hcover M hmin ((Finset.card_le_card hME).trans hE), hME⟩
  · rintro ⟨M, hM, hME⟩
    exact uncorrectable_mono S hS hME (hunc M hM)

/-! ## U2. Karp–Luby union identity -/

/-- **U2. Union identity** (purely combinatorial). -/
theorem sum_union_eq_karpLuby {α : Type*} [DecidableEq α] (terms layer : Finset (Finset α))
    (g : Finset α → ℝ) :
    ∑ E ∈ layer.filter (fun E => ∃ M ∈ terms, M ⊆ E), g E =
      ∑ M ∈ terms, ∑ E ∈ layer.filter (fun E => M ⊆ E),
        g E / ((terms.filter (fun M' => M' ⊆ E)).card : ℝ) := by
  calc ∑ E ∈ layer.filter (fun E => ∃ M ∈ terms, M ⊆ E), g E
      = ∑ E ∈ layer, if (∃ M ∈ terms, M ⊆ E) then g E else 0 := by
        rw [Finset.sum_filter]
    _ = ∑ E ∈ layer, ∑ M ∈ terms,
          if M ⊆ E then g E / ((terms.filter (fun M' => M' ⊆ E)).card : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro E _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        split_ifs with h
        · have hne : ((terms.filter (fun M' => M' ⊆ E)).card : ℝ) ≠ 0 := by
            obtain ⟨M, hM, hME⟩ := h
            exact_mod_cast Finset.card_ne_zero.mpr ⟨M, Finset.mem_filter.mpr ⟨hM, hME⟩⟩
          field_simp
        · have he : terms.filter (fun M' => M' ⊆ E) = ∅ :=
            Finset.filter_eq_empty_iff.mpr (fun M hM hME => h ⟨M, hM, hME⟩)
          simp [he]
    _ = ∑ M ∈ terms, ∑ E ∈ layer,
          if M ⊆ E then g E / ((terms.filter (fun M' => M' ⊆ E)).card : ℝ) else 0 :=
        Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl
        intro M _
        rw [Finset.sum_filter]

theorem infidelityScore_eq_zero (S : Submodule Bit (Pauli n)) {E : Finset (Fin n)}
    (h : ambiguity (symplectic n) S (supported E) = 0) : infidelityScore S E = 0 := by
  unfold infidelityScore erasureScore
  rw [h]
  simp

theorem uncorrectable_eq_zero (S : Submodule Bit (Pauli n)) {E : Finset (Fin n)}
    (h : ambiguity (symplectic n) S (supported E) = 0) : uncorrectable S E = 0 := by
  unfold uncorrectable
  rw [h]
  simp

/-- **U2, specialised.** For a layer `j ≤ w` and any score vanishing on correctable sets,
the layer sum is the Karp–Luby sum over the listed minimal sets. -/
theorem layer_sum_eq_karpLuby (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    (g : Finset (Fin n) → ℝ) (hg : ∀ E, ambiguity (symplectic n) S (supported E) = 0 → g E = 0)
    {j : ℕ} (hj : j ≤ w) :
    ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = j), g E =
      ∑ M ∈ mins, ∑ E ∈ (Finset.univ.filter (fun E : Finset (Fin n) => E.card = j)).filter
          (fun E => M ⊆ E),
        g E / ((mins.filter (fun M' => M' ⊆ E)).card : ℝ) := by
  rw [← sum_union_eq_karpLuby, Finset.sum_filter (fun E => ∃ M ∈ mins, M ⊆ E)]
  apply Finset.sum_congr rfl
  intro E hE
  have hc : E.card = j := (Finset.mem_filter.mp hE).2
  split_ifs with h
  · rfl
  · have hiff := uncorrectable_iff_exists_mins S hS w mins hunc hcover E (hc ▸ hj)
    have h0 : ambiguity (symplectic n) S (supported E) = 0 := by
      by_contra hne
      exact h (hiff.mp (Nat.pos_of_ne_zero hne))
    exact hg E h0

theorem layer_sum_infidelityScore_eq_karpLuby (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {j : ℕ} (hj : j ≤ w) :
    ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = j), infidelityScore S E =
      ∑ M ∈ mins, ∑ E ∈ (Finset.univ.filter (fun E : Finset (Fin n) => E.card = j)).filter
          (fun E => M ⊆ E),
        infidelityScore S E / ((mins.filter (fun M' => M' ⊆ E)).card : ℝ) :=
  layer_sum_eq_karpLuby S hS w mins hunc hcover _ (fun _ h => infidelityScore_eq_zero S h) hj

theorem layer_sum_uncorrectable_eq_karpLuby (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {j : ℕ} (hj : j ≤ w) :
    ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = j), uncorrectable S E =
      ∑ M ∈ mins, ∑ E ∈ (Finset.univ.filter (fun E : Finset (Fin n) => E.card = j)).filter
          (fun E => M ⊆ E),
        uncorrectable S E / ((mins.filter (fun M' => M' ⊆ E)).card : ℝ) :=
  layer_sum_eq_karpLuby S hS w mins hunc hcover _ (fun _ h => uncorrectable_eq_zero S h) hj

/-! ## C1. Coefficientwise relative error passes to the curve -/

/-- **C1.** No sign condition on `b` or `ε` is needed; only `p ∈ [0,1]`. -/
theorem bernsteinCurve_rel_of_coeff {b c : Fin (n + 1) → ℝ} {ε : ℝ}
    (hc : ∀ j, |c j - b j| ≤ ε * b j) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |bernsteinCurve n c p - bernsteinCurve n b p| ≤ ε * bernsteinCurve n b p := by
  unfold bernsteinCurve average
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hw := bernsteinWeight_nonneg (r := n) hp0 hp1 j
  rw [← mul_sub, abs_mul, abs_of_nonneg hw]
  calc bernsteinWeight n p j * |c j - b j| ≤ bernsteinWeight n p j * (ε * b j) :=
        mul_le_mul_of_nonneg_left (hc j) hw
    _ = ε * (bernsteinWeight n p j * b j) := by ring

end QecPhysical.Stabilizer.Uncorrectable

#print axioms QecPhysical.Stabilizer.Uncorrectable.finrank_localized_add_finrank
#print axioms QecPhysical.Stabilizer.Uncorrectable.ambiguity_add_ambiguity_compl
#print axioms QecPhysical.Stabilizer.Uncorrectable.erasureScore_eq_dual
#print axioms QecPhysical.Stabilizer.Uncorrectable.sum_layer_erasureScore_dual
#print axioms QecPhysical.Stabilizer.Uncorrectable.layerAverage_erasureScore_dual
#print axioms QecPhysical.Stabilizer.Uncorrectable.exists_minimalUncorrectable_subset
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectable_iff_exists_mins
#print axioms QecPhysical.Stabilizer.Uncorrectable.sum_union_eq_karpLuby
#print axioms QecPhysical.Stabilizer.Uncorrectable.layer_sum_eq_karpLuby
#print axioms QecPhysical.Stabilizer.Uncorrectable.layer_sum_infidelityScore_eq_karpLuby
#print axioms QecPhysical.Stabilizer.Uncorrectable.layer_sum_uncorrectable_eq_karpLuby
#print axioms QecPhysical.Stabilizer.Uncorrectable.bernsteinCurve_rel_of_coeff
