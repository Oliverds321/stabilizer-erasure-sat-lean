import UncorrectableProbability

set_option autoImplicit false

/-!
# Single-point hardness: a point estimate of the erasure infidelity determines the distance

T1. Tail sandwich `p^d/2 ≤ I(p) ≤ C(n,d) p^d` and `p^d ≤ U(p) ≤ C(n,d) p^d`.
T2. A relative-factor-`R` estimate of `I(p)` (or `U(p)`) at one small `p` determines `d`
    through an explicit numeric test.
T3. Uniqueness and existence of the distance, and the certificate form of `distance ≤ w`.
-/

noncomputable section

namespace QecPhysical.Stabilizer.Uncorrectable

open scoped BigOperators
open QecReliability
open QecReliability.Binary
open QecPhysical.BinaryPauli

variable {n : ℕ}

/-- `d` is the least size of an uncorrectable erased set. -/
def IsDistance (S : Submodule Bit (Pauli n)) (d : ℕ) : Prop :=
  (∀ E : Finset (Fin n), E.card < d → ¬ (0 < ambiguity (symplectic n) S (supported E))) ∧
    ∃ E : Finset (Fin n), E.card = d ∧ 0 < ambiguity (symplectic n) S (supported E)

/-! ## Superset mass -/

/-- The iid mass of the up-set of `E0` is `p ^ |E0|`. -/
theorem superset_mass (p : ℝ) (E0 : Finset (Fin n)) :
    ∑ E : Finset (Fin n), causeMass p E * (if E0 ⊆ E then (1:ℝ) else 0) = p ^ E0.card := by
  classical
  have h : ∏ i : Fin n, (p + if i ∈ E0 then (0:ℝ) else 1 - p) =
      ∑ t : Finset (Fin n), (∏ i ∈ t, p) *
        ∏ i ∈ Finset.univ \ t, (if i ∈ E0 then (0:ℝ) else 1 - p) := by
    rw [Finset.prod_add, Finset.powerset_univ]
  have hl : ∏ i : Fin n, (p + if i ∈ E0 then (0:ℝ) else 1 - p) = p ^ E0.card := by
    have : ∀ i : Fin n, (p + if i ∈ E0 then (0:ℝ) else 1 - p) = if i ∈ E0 then p else 1 := by
      intro i
      split_ifs <;> ring
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_const]
  have hr : ∀ t : Finset (Fin n), (∏ i ∈ t, p) *
      ∏ i ∈ Finset.univ \ t, (if i ∈ E0 then (0:ℝ) else 1 - p) =
        causeMass p t * (if E0 ⊆ t then 1 else 0) := by
    intro t
    rw [Finset.prod_const]
    unfold causeMass
    split_ifs with hsub
    · have hc : ∀ i ∈ Finset.univ \ t, (if i ∈ E0 then (0:ℝ) else 1 - p) = 1 - p := by
        intro i hi
        have : i ∉ E0 := fun h => (Finset.mem_sdiff.mp hi).2 (hsub h)
        simp [this]
      rw [Finset.prod_congr rfl hc, Finset.prod_const, Finset.card_univ_sdiff, Fintype.card_fin]
      ring
    · obtain ⟨i, hi0, hit⟩ := Finset.not_subset.mp hsub
      rw [Finset.prod_eq_zero (i := i) (by simp [hit]) (by simp [hi0])]
      ring
  rw [← hl, h]
  exact Finset.sum_congr rfl (fun t _ => (hr t).symm)

/-! ## T1. Tail sandwich -/

theorem uncorrectable_le_sum_subsets (S : Submodule Bit (Pauli n)) {d : ℕ} (hd : IsDistance S d)
    (E : Finset (Fin n)) :
    uncorrectable S E ≤
      ∑ D ∈ Finset.powersetCard d Finset.univ, (if D ⊆ E then (1:ℝ) else 0) := by
  unfold uncorrectable
  split_ifs with hE
  · have hcard : d ≤ E.card := by
      by_contra h
      exact hd.1 E (by omega) hE
    obtain ⟨D, hDE, hDc⟩ := Finset.exists_subset_card_eq hcard
    have hmem : D ∈ Finset.powersetCard d Finset.univ :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hDc⟩
    calc (1:ℝ) = if D ⊆ E then 1 else 0 := by simp [hDE]
      _ ≤ _ := Finset.single_le_sum (f := fun D => if D ⊆ E then (1:ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) hmem
  · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem indicator_le_uncorrectable (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {E0 : Finset (Fin n)}
    (h0 : 0 < ambiguity (symplectic n) S (supported E0)) (E : Finset (Fin n)) :
    (if E0 ⊆ E then (1:ℝ) else 0) ≤ uncorrectable S E := by
  split_ifs with hsub
  · unfold uncorrectable
    simp [uncorrectable_mono S hS hsub h0]
  · exact (uncorrectable_range S E).1

theorem uncorrectableProb_le (S : Submodule Bit (Pauli n)) {d : ℕ} (hd : IsDistance S d)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uncorrectableProb S p ≤ (n.choose d : ℝ) * p ^ d := by
  calc uncorrectableProb S p ≤ ∑ E : Finset (Fin n), causeMass p E *
        ∑ D ∈ Finset.powersetCard d Finset.univ, (if D ⊆ E then (1:ℝ) else 0) :=
        Finset.sum_le_sum (fun E _ => mul_le_mul_of_nonneg_left
          (uncorrectable_le_sum_subsets S hd E) (causeMass_nonneg hp0 hp1 E))
    _ = ∑ D ∈ Finset.powersetCard d Finset.univ, ∑ E : Finset (Fin n),
          causeMass p E * (if D ⊆ E then (1:ℝ) else 0) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ D ∈ Finset.powersetCard d Finset.univ, p ^ d := by
        apply Finset.sum_congr rfl
        intro D hD
        rw [superset_mass, (Finset.mem_powersetCard.mp hD).2]
    _ = (n.choose d : ℝ) * p ^ d := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

theorem le_uncorrectableProb (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ d ≤ uncorrectableProb S p := by
  obtain ⟨E0, hc, h0⟩ := hd.2
  rw [← hc, ← superset_mass p E0]
  exact Finset.sum_le_sum (fun E _ => mul_le_mul_of_nonneg_left
    (indicator_le_uncorrectable S hS h0 E) (causeMass_nonneg hp0 hp1 E))

theorem le_infidelity (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ d / 2 ≤ infidelity S p := by
  obtain ⟨E0, hc, h0⟩ := hd.2
  have h : p ^ d ≤ 2 * infidelity S p := by
    rw [← hc, ← superset_mass p E0]
    unfold infidelity
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro E _
    have h1 := (indicator_le_uncorrectable S hS h0 E).trans
      (infidelityScore_le_uncorrectable S E).2
    have := mul_le_mul_of_nonneg_left h1 (causeMass_nonneg hp0 hp1 E)
    linarith
  linarith

theorem infidelity_le (S : Submodule Bit (Pauli n)) {d : ℕ} (hd : IsDistance S d)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    infidelity S p ≤ (n.choose d : ℝ) * p ^ d :=
  (infidelity_le_uncorrectableProb S hp0 hp1).1.trans (uncorrectableProb_le S hd hp0 hp1)

/-- **T1. Tail sandwich.** -/
theorem tail_sandwich (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ d / 2 ≤ infidelity S p ∧ infidelity S p ≤ (n.choose d : ℝ) * p ^ d ∧
      p ^ d ≤ uncorrectableProb S p ∧ uncorrectableProb S p ≤ (n.choose d : ℝ) * p ^ d :=
  ⟨le_infidelity S hS hd hp0 hp1, infidelity_le S hd hp0 hp1,
    le_uncorrectableProb S hS hd hp0 hp1, uncorrectableProb_le S hd hp0 hp1⟩

/-! ## T2. A point estimate determines the distance -/

private theorem choose_le_two_pow_real (n d : ℕ) : (n.choose d : ℝ) ≤ (2:ℝ) ^ n := by
  exact_mod_cast Nat.choose_le_two_pow n d

/-- Core contradiction: `q / (c R) ≤ X R (q p)` with `c X R² p < 1` is impossible for `q > 0`. -/
private theorem gap_absurd {q p R c X : ℝ} (hq : 0 < q) (hR : 0 < R) (hc : 0 < c)
    (h : q / (c * R) ≤ X * R * (q * p)) (hsmall : c * X * R ^ 2 * p < 1) : False := by
  rw [div_le_iff₀ (by positivity)] at h
  have e : X * R * (q * p) * (c * R) = q * (c * X * R ^ 2 * p) := by ring
  have : q * (c * X * R ^ 2 * p) < q * 1 := mul_lt_mul_of_pos_left hsmall hq
  linarith

/-- Generic form of T2: `f` sandwiched as `p^d / c ≤ f ≤ 2^n p^d`, estimate within factor `R`. -/
private theorem point_test_generic {d : ℕ} {f p R est c : ℝ} (hc : 1 ≤ c)
    (hlo : p ^ d / c ≤ f) (hhi : f ≤ (2:ℝ) ^ n * p ^ d)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hR : 1 ≤ R) (hsmall : c * (2:ℝ) ^ n * R ^ 2 * p < 1)
    (hest : f / R ≤ est ∧ est ≤ R * f) (d' : ℕ) :
    (p ^ d' / (c * R) ≤ est ∧ est ≤ (2:ℝ) ^ n * R * p ^ d') ↔ d' = d := by
  have hR0 : 0 < R := by linarith
  have hc0 : 0 < c := by linarith
  have hlo' : p ^ d / (c * R) ≤ est := by
    rw [← div_div]
    exact (div_le_div_of_nonneg_right hlo hR0.le).trans hest.1
  have hhi' : est ≤ (2:ℝ) ^ n * R * p ^ d := by
    calc est ≤ R * f := hest.2
      _ ≤ R * ((2:ℝ) ^ n * p ^ d) := mul_le_mul_of_nonneg_left hhi hR0.le
      _ = (2:ℝ) ^ n * R * p ^ d := by ring
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy d' d with hlt | heq | hgt
    · exfalso
      have hpd : p ^ d ≤ p ^ d' * p := by
        rw [← pow_succ]
        exact pow_le_pow_of_le_one hp0.le hp1 hlt
      have : p ^ d' / (c * R) ≤ (2:ℝ) ^ n * R * (p ^ d' * p) :=
        h1.trans (hhi'.trans (mul_le_mul_of_nonneg_left hpd (by positivity)))
      exact gap_absurd (pow_pos hp0 d') hR0 hc0 this hsmall
    · exact heq
    · exfalso
      have hpd : p ^ d' ≤ p ^ d * p := by
        rw [← pow_succ]
        exact pow_le_pow_of_le_one hp0.le hp1 hgt
      have : p ^ d / (c * R) ≤ (2:ℝ) ^ n * R * (p ^ d * p) :=
        hlo'.trans (h2.trans (mul_le_mul_of_nonneg_left hpd (by positivity)))
      exact gap_absurd (pow_pos hp0 d) hR0 hc0 this hsmall
  · rintro rfl
    exact ⟨hlo', hhi'⟩

/-- **T2 (infidelity).** At one point `p` with `2^(n+1) R² p < 1`, an estimate of `I(p)` within
factor `R` determines the distance: `d` is the unique exponent passing the numeric test. -/
theorem infidelity_point_determines_distance (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p R est : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hR : 1 ≤ R)
    (hsmall : (2:ℝ) ^ (n + 1) * R ^ 2 * p < 1)
    (hest : infidelity S p / R ≤ est ∧ est ≤ R * infidelity S p) (d' : ℕ) :
    (p ^ d' / (2 * R) ≤ est ∧ est ≤ (2:ℝ) ^ n * R * p ^ d') ↔ d' = d := by
  have hhi : infidelity S p ≤ (2:ℝ) ^ n * p ^ d :=
    (infidelity_le S hd hp0.le hp1).trans
      (mul_le_mul_of_nonneg_right (choose_le_two_pow_real n d) (pow_nonneg hp0.le d))
  have hsmall' : 2 * (2:ℝ) ^ n * R ^ 2 * p < 1 := by
    rw [pow_succ] at hsmall
    linarith
  exact point_test_generic (by norm_num) (le_infidelity S hS hd hp0.le hp1) hhi hp0 hp1 hR
    hsmall' hest d'

/-- **T2 (channel form).** The same test, with the estimate taken of the optimal physical
infidelity `1 - F` of the iid flagged erasure channel. -/
theorem channel_point_determines_distance {S : Submodule Bit (Pauli n)} (L : Lift S)
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p R est : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hR : 1 ≤ R)
    (hsmall : (2:ℝ) ^ (n + 1) * R ^ 2 * p < 1)
    (hest : (1 - entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0.le hp1)).map) / R ≤ est ∧
      est ≤ R * (1 - entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0.le hp1)).map)) (d' : ℕ) :
    (p ^ d' / (2 * R) ≤ est ∧ est ≤ (2:ℝ) ^ n * R * p ^ d') ↔ d' = d := by
  rw [← infidelity_eq_channel L p hp0.le hp1] at hest
  exact infidelity_point_determines_distance S hS hd hp0 hp1 hR hsmall hest d'

/-- **T2 (uncorrectable probability).** Only `2^n R² p < 1` is needed. -/
theorem uncorrectableProb_point_determines_distance (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p R est : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hR : 1 ≤ R)
    (hsmall : (2:ℝ) ^ n * R ^ 2 * p < 1)
    (hest : uncorrectableProb S p / R ≤ est ∧ est ≤ R * uncorrectableProb S p) (d' : ℕ) :
    (p ^ d' / R ≤ est ∧ est ≤ (2:ℝ) ^ n * R * p ^ d') ↔ d' = d := by
  have hhi : uncorrectableProb S p ≤ (2:ℝ) ^ n * p ^ d :=
    (uncorrectableProb_le S hd hp0.le hp1).trans
      (mul_le_mul_of_nonneg_right (choose_le_two_pow_real n d) (pow_nonneg hp0.le d))
  have hlo : p ^ d / 1 ≤ uncorrectableProb S p := by
    rw [div_one]
    exact le_uncorrectableProb S hS hd hp0.le hp1
  have hsmall' : 1 * (2:ℝ) ^ n * R ^ 2 * p < 1 := by linarith
  have h := point_test_generic le_rfl hlo hhi hp0 hp1 hR hsmall' hest d'
  rwa [one_mul] at h

/-! ## T3. Existence, uniqueness, certificates -/

/-- **T3(a).** The distance is unique. -/
theorem isDistance_unique (S : Submodule Bit (Pauli n)) {d d' : ℕ}
    (hd : IsDistance S d) (hd' : IsDistance S d') : d = d' := by
  obtain ⟨E, hE, hpos⟩ := hd.2
  obtain ⟨E', hE', hpos'⟩ := hd'.2
  have h1 : ¬ d < d' := fun h => hd'.1 E (hE ▸ h) hpos
  have h2 : ¬ d' < d := fun h => hd.1 E' (hE' ▸ h) hpos'
  omega

/-- **T3(b).** If the full set is uncorrectable, the distance exists and is at most `n`. -/
theorem exists_isDistance (S : Submodule Bit (Pauli n))
    (huniv : 0 < ambiguity (symplectic n) S (supported (Finset.univ : Finset (Fin n)))) :
    ∃ d, IsDistance S d ∧ d ≤ n := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ E : Finset (Fin n), E.card = k ∧ 0 < ambiguity (symplectic n) S (supported E)
  have hex : ∃ k, P k := ⟨n, Finset.univ, by simp, huniv⟩
  refine ⟨Nat.find hex, ⟨?_, Nat.find_spec hex⟩, Nat.find_min' hex ⟨Finset.univ, by simp, huniv⟩⟩
  intro E hE hpos
  exact Nat.find_min hex hE ⟨E, rfl, hpos⟩

/-- **T3(c).** Certificate form of "some erased set of size `≤ w` is uncorrectable". -/
theorem exists_uncorrectable_le_iff_certificate (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) :
    (∃ E : Finset (Fin n), E.card ≤ w ∧ 0 < ambiguity (symplectic n) S (supported E)) ↔
      ∃ E : Finset (Fin n), E.card ≤ w ∧
        ∃ x ∈ localized (symplectic n) S (supported E),
          ∃ z ∈ normalizer (symplectic n) S, symplectic n x z = 1 := by
  constructor
  · rintro ⟨E, hw, hE⟩
    exact ⟨E, hw, (uncorrectable_iff_certificate S hS E).mp hE⟩
  · rintro ⟨E, hw, hE⟩
    exact ⟨E, hw, (uncorrectable_iff_certificate S hS E).mpr hE⟩

/-- **T3(c), distance form.** With `IsDistance S d`, the left side holds iff `d ≤ w`. -/
theorem exists_uncorrectable_le_iff (S : Submodule Bit (Pauli n)) {d : ℕ}
    (hd : IsDistance S d) (w : ℕ) :
    (∃ E : Finset (Fin n), E.card ≤ w ∧ 0 < ambiguity (symplectic n) S (supported E)) ↔
      d ≤ w := by
  constructor
  · rintro ⟨E, hw, hE⟩
    by_contra h
    exact hd.1 E (by omega) hE
  · intro hw
    obtain ⟨E, hc, hE⟩ := hd.2
    exact ⟨E, hc ▸ hw, hE⟩

/-- **T3(c), combined.** With `IsDistance S d`: `d ≤ w` iff a size-`≤ w` certificate exists. -/
theorem distance_le_iff_certificate (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d) (w : ℕ) :
    d ≤ w ↔ ∃ E : Finset (Fin n), E.card ≤ w ∧
        ∃ x ∈ localized (symplectic n) S (supported E),
          ∃ z ∈ normalizer (symplectic n) S, symplectic n x z = 1 :=
  (exists_uncorrectable_le_iff S hd w).symm.trans (exists_uncorrectable_le_iff_certificate S hS w)

end QecPhysical.Stabilizer.Uncorrectable

#print axioms QecPhysical.Stabilizer.Uncorrectable.superset_mass
#print axioms QecPhysical.Stabilizer.Uncorrectable.tail_sandwich
#print axioms QecPhysical.Stabilizer.Uncorrectable.infidelity_point_determines_distance
#print axioms QecPhysical.Stabilizer.Uncorrectable.channel_point_determines_distance
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectableProb_point_determines_distance
#print axioms QecPhysical.Stabilizer.Uncorrectable.isDistance_unique
#print axioms QecPhysical.Stabilizer.Uncorrectable.exists_isDistance
#print axioms QecPhysical.Stabilizer.Uncorrectable.exists_uncorrectable_le_iff_certificate
#print axioms QecPhysical.Stabilizer.Uncorrectable.exists_uncorrectable_le_iff
#print axioms QecPhysical.Stabilizer.Uncorrectable.distance_le_iff_certificate
