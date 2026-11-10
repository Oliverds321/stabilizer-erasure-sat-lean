import QecReliability.PosetShapeRepair
import QecReliability.BernsteinShape
import QecReliability.HammingMonotonicity
import QecReliability.BinarySymplectic
import PhysicalBridge.PhysicalBernstein

set_option autoImplicit false

/-!
# Anchored antitone repair with general interval maps, and the uncorrectable-erasure probability

Part A proves the interval guarantee of the anchored antitone repair for arbitrary interval maps
`lo ≤ id ≤ hi` with `lo` monotone on `[0,1]` (the existing two-tail `RelPair` statement is the
special case `lo = relLower ε`, `hi = relUpper ε`).

Part B treats the probability `U(p)` that an iid erasure pattern is uncorrectable (positive
ambiguity): certificate identity, monotonicity, the comparison `I ≤ U ≤ 2 I` with the optimal
infidelity `I = 1 - F`, its Bernstein form with monotone layer fractions, and the anchored repair
of one-sided relative estimates of those fractions.
-/

noncomputable section

namespace QecReliability.PosetShapeRepair

variable {ι : Type*} [Fintype ι] [PartialOrder ι]

/-- Clipping preserves membership in any interval `[lo f, hi f]` with `lo f ≤ f ≤ hi f`,
`f ∈ [0,1]`. -/
theorem clip_mem_interval {f h a b : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (haf : a ≤ f) (hfb : f ≤ b)
    (hah : a ≤ h) (hhb : h ≤ b) : a ≤ clip h ∧ clip h ≤ b := by
  unfold clip
  refine ⟨le_max_of_le_right (le_min (haf.trans hf1) hah), max_le (hf0.trans hfb) ?_⟩
  exact (min_le_right _ _).trans hhb

/-- **Anchored antitone repair, general interval form.** Only monotonicity of `lo` on `[0,1]`
and `lo t ≤ t ≤ hi t` on `[0,1]` are used; no monotonicity of `hi` is needed. -/
theorem repair_interval' (anchors : Finset ι) (anchorValues estimates f : ι → ℝ)
    (lo hi : ℝ → ℝ)
    (hlo : MonotoneOn lo (Set.Icc 0 1))
    (hlo_le : ∀ t ∈ Set.Icc (0:ℝ) 1, lo t ≤ t) (hle_hi : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≤ hi t)
    (hanti : Antitone f) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hanchor : ∀ a ∈ anchors, anchorValues a = f a)
    (hest : ∀ i, lo (f i) ≤ estimates i ∧ estimates i ≤ hi (f i)) :
    ∀ j, lo (f j) ≤ repair anchors anchorValues estimates j ∧
         repair anchors anchorValues estimates j ≤ hi (f j) := by
  classical
  have hmem : ∀ i, f i ∈ Set.Icc (0:ℝ) 1 := fun i => ⟨(hf i).1, (hf i).2⟩
  have hbase : ∀ i, lo (f i) ≤ anchoredEstimate anchors anchorValues estimates i ∧
      anchoredEstimate anchors anchorValues estimates i ≤ hi (f i) := by
    intro i
    by_cases hi' : i ∈ anchors
    · simp only [anchoredEstimate, hi', ite_true, hanchor i hi']
      exact ⟨hlo_le _ (hmem i), hle_hi _ (hmem i)⟩
    · simp only [anchoredEstimate, hi', ite_false]
      exact clip_mem_interval (hf i).1 (hf i).2 (hlo_le _ (hmem i)) (hle_hi _ (hmem i))
        (hest i).1 (hest i).2
  intro j
  have hlow : lo (f j) ≤ prefixMinimum (anchoredEstimate anchors anchorValues estimates) j := by
    apply (le_prefixMinimum_iff _ j _).mpr
    intro i hij
    exact (hlo (hmem j) (hmem i) (hanti hij)).trans (hbase i).1
  have hfloor : anchorFloor anchors anchorValues j ≤ f j := by
    apply (anchorFloor_le_iff anchors anchorValues j (f j)).mpr
    refine ⟨(hf j).1, ?_⟩
    intro a ha hja
    rw [hanchor a ha]
    exact hanti hja
  refine ⟨hlow.trans (le_max_right _ _), max_le ?_ ?_⟩
  · exact hfloor.trans (hle_hi _ (hmem j))
  · exact (prefixMinimum_le (anchoredEstimate anchors anchorValues estimates) le_rfl).trans
      (hbase j).2

/-- **Anchored antitone repair (paper Lemma), exact requested signature.** The hypothesis
`hhi` is not needed (see `repair_interval'`). -/
theorem repair_interval (anchors : Finset ι) (anchorValues estimates f : ι → ℝ)
    (lo hi : ℝ → ℝ)
    (hlo : MonotoneOn lo (Set.Icc 0 1)) (_hhi : MonotoneOn hi (Set.Icc 0 1))
    (hlo_le : ∀ t ∈ Set.Icc (0:ℝ) 1, lo t ≤ t) (hle_hi : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≤ hi t)
    (hanti : Antitone f) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hanchor : ∀ a ∈ anchors, anchorValues a = f a)
    (hest : ∀ i, lo (f i) ≤ estimates i ∧ estimates i ≤ hi (f i)) :
    ∀ j, lo (f j) ≤ repair anchors anchorValues estimates j ∧
         repair anchors anchorValues estimates j ≤ hi (f j) :=
  repair_interval' anchors anchorValues estimates f lo hi hlo hlo_le hle_hi hanti hf hanchor hest

/-- The existing two-tail statement `repair_relPair` as the special case
`lo = relLower ε`, `hi = relUpper ε`. -/
theorem repair_relPair_of_interval (anchors : Finset ι) (anchorValues estimates f : ι → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hanti : Antitone f)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hanchor : ∀ a ∈ anchors, anchorValues a = f a)
    (hpair : ∀ i, RelPair ε (f i) (estimates i)) (j : ι) :
    RelPair ε (f j) (repair anchors anchorValues estimates j) :=
  (relPair_iff_interval _ _ _).mpr
    (repair_interval' anchors anchorValues estimates f (relLower ε) (relUpper ε)
      ((relLower_mono hε hε1).monotoneOn _)
      (fun _ ht => relLower_le_self hε ht.1 ht.2) (fun _ ht => self_le_relUpper hε ht.1 ht.2)
      hanti hf hanchor (fun i => (relPair_iff_interval _ _ _).mp (hpair i)) j)

end QecReliability.PosetShapeRepair

/-! ## Part B -/

namespace QecReliability

open Module

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- Positive ambiguity iff some normalizer element is a `Bad` certificate. -/
theorem ambiguity_pos_iff_exists_bad (B : LinearMap.BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U : Submodule F W) (hS : S ≤ normalizer B S) :
    0 < ambiguity B S U ↔ ∃ z ∈ normalizer B S, Bad B S U z := by
  have h := finrank_goodSpace_add_ambiguity B hB hR S U hS
  have hle : goodSpace B S U ≤ normalizer B S := inf_le_left
  constructor
  · intro hd
    by_contra hno
    have hge : normalizer B S ≤ goodSpace B S U := by
      intro z hz
      refine ⟨hz, (good_iff_orthogonal B hB hR S U z).mp ?_⟩
      by_contra hg
      exact hno ⟨z, hz, (bad_iff_not_good B hB hR S U z).mpr hg⟩
    have := Submodule.finrank_mono hge
    omega
  · rintro ⟨z, hz, hbad⟩
    have hnot : z ∉ goodSpace B S U := fun hg =>
      (bad_iff_not_good B hB hR S U z).mp hbad ((good_iff_orthogonal B hB hR S U z).mpr hg.2)
    have hlt : goodSpace B S U < normalizer B S :=
      lt_of_le_of_ne hle (fun heq => hnot (heq ▸ hz))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega

end QecReliability

namespace QecPhysical.Stabilizer.Uncorrectable

open scoped BigOperators
open QecReliability
open QecReliability.Binary
open QecPhysical.BinaryPauli
open QecReliability.PosetShapeRepair

variable {n : ℕ}

/-- B1. **Certificate identity.** An erased set is uncorrectable (positive ambiguity) iff some
localized logical `x` pairs to one with some normalizer element `z`. -/
theorem uncorrectable_iff_certificate (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (E : Finset (Fin n)) :
    0 < ambiguity (symplectic n) S (supported E) ↔
      ∃ x ∈ localized (symplectic n) S (supported E),
        ∃ z ∈ normalizer (symplectic n) S, symplectic n x z = 1 := by
  rw [ambiguity_pos_iff_exists_bad (symplectic n) (symplectic_nondegenerate n)
    (symplectic_refl n) S (supported E) hS]
  constructor
  · rintro ⟨z, hz, x, hx, hxz⟩
    exact ⟨x, hx, z, hz, hxz⟩
  · rintro ⟨x, hx, z, hz, hxz⟩
    exact ⟨z, hz, x, hx, hxz⟩

/-- B2. **Monotonicity.** Supersets of uncorrectable erased sets are uncorrectable. -/
theorem uncorrectable_mono (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {E E' : Finset (Fin n)} (h : E ⊆ E')
    (hE : 0 < ambiguity (symplectic n) S (supported E)) :
    0 < ambiguity (symplectic n) S (supported E') :=
  lt_of_lt_of_le hE (ambiguity_erasure_mono S hS h)

/-- Indicator of uncorrectability. -/
def uncorrectable (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) : ℝ :=
  if 0 < ambiguity (symplectic n) S (supported E) then 1 else 0

/-- Per-pattern infidelity `1 - 2^{-d_E}`. -/
def infidelityScore (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) : ℝ :=
  1 - erasureScore S E

/-- Probability that an iid erasure pattern is uncorrectable. -/
def uncorrectableProb (S : Submodule Bit (Pauli n)) (p : ℝ) : ℝ :=
  ∑ E : Finset (Fin n), causeMass p E * uncorrectable S E

/-- Optimal iid erasure infidelity, as a finite sum. -/
def infidelity (S : Submodule Bit (Pauli n)) (p : ℝ) : ℝ :=
  ∑ E : Finset (Fin n), causeMass p E * infidelityScore S E

theorem uncorrectable_range (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    0 ≤ uncorrectable S E ∧ uncorrectable S E ≤ 1 := by
  unfold uncorrectable
  split_ifs <;> norm_num

/-- B3. **Per-pattern comparison.** `Y_E ≤ X_E ≤ 2 Y_E`. -/
theorem infidelityScore_le_uncorrectable (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    infidelityScore S E ≤ uncorrectable S E ∧
      uncorrectable S E ≤ 2 * infidelityScore S E := by
  unfold infidelityScore uncorrectable erasureScore
  set d := ambiguity (symplectic n) S (supported E)
  have hpos : (0:ℝ) < ((2:ℝ) ^ d)⁻¹ := by positivity
  split_ifs with hd
  · have h2 : (2:ℝ) ≤ (2:ℝ) ^ d := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
    have hhalf : ((2:ℝ) ^ d)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      simpa using h2
    constructor <;> linarith
  · have hd0 : d = 0 := by omega
    rw [hd0]
    norm_num

theorem infidelity_le_uncorrectableProb (S : Submodule Bit (Pauli n)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    infidelity S p ≤ uncorrectableProb S p ∧ uncorrectableProb S p ≤ 2 * infidelity S p := by
  unfold infidelity uncorrectableProb
  constructor
  · apply Finset.sum_le_sum
    intro E _
    exact mul_le_mul_of_nonneg_left (infidelityScore_le_uncorrectable S E).1
      (causeMass_nonneg hp0 hp1 E)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro E _
    have := mul_le_mul_of_nonneg_left (infidelityScore_le_uncorrectable S E).2
      (causeMass_nonneg hp0 hp1 E)
    linarith

/-- Infidelity as a Bernstein curve of the layer-averaged erasure scores. -/
theorem infidelity_eq (S : Submodule Bit (Pauli n)) (p : ℝ) :
    infidelity S p =
      1 - bernsteinCurve n (layerAverage (id : Causes n → Finset (Fin n)) (erasureScore S)) p := by
  rw [← latentCurve_eq_bernstein]
  unfold infidelity infidelityScore latentCurve
  have h := causeMass_sum n p
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h]
  rfl

/-- The finite-sum infidelity is the optimal physical infidelity of the iid flagged erasure
channel. -/
theorem infidelity_eq_channel {S : Submodule Bit (Pauli n)} (L : Lift S) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    infidelity S p = 1 - entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0 hp1)).map := by
  rw [(L.iidLatentErasure_optimum (id : Causes n → Finset (Fin n)) p hp0 hp1).1]
  exact infidelity_eq S p

/-- B3 at the channel level: `I(p) ≤ U(p) ≤ 2 I(p)` with `I = 1 - F` the optimal infidelity. -/
theorem channel_infidelity_le_uncorrectableProb {S : Submodule Bit (Pauli n)} (L : Lift S)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0 hp1)).map ≤
        uncorrectableProb S p ∧
      uncorrectableProb S p ≤ 2 * (1 - entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0 hp1)).map) := by
  rw [← infidelity_eq_channel L p hp0 hp1]
  exact infidelity_le_uncorrectableProb S hp0 hp1

/-! ### B4. Bernstein form and shape -/

/-- Fraction of uncorrectable erased sets of size `j`. -/
def layerFraction (S : Submodule Bit (Pauli n)) (j : Fin (n + 1)) : ℝ :=
  layerAverage (id : Causes n → Finset (Fin n)) (uncorrectable S) j

theorem uncorrectableProb_eq_bernstein (S : Submodule Bit (Pauli n)) (p : ℝ) :
    uncorrectableProb S p = bernsteinCurve n (layerFraction S) p := by
  unfold layerFraction
  rw [← latentCurve_eq_bernstein]
  rfl

theorem layerFraction_range (S : Submodule Bit (Pauli n)) (j : Fin (n + 1)) :
    0 ≤ layerFraction S j ∧ layerFraction S j ≤ 1 :=
  layerAverage_range _ _ (uncorrectable_range S) j

theorem layerFraction_monotone (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) : Monotone (layerFraction S) := by
  have hanti := layerAverage_antitone (id : Causes n → Finset (Fin n))
    (fun E => - uncorrectable S E) (by
      intro a b hab
      simp only [id, neg_le_neg_iff]
      unfold uncorrectable
      split_ifs with ha hb <;>
        first | exact absurd (uncorrectable_mono S hS hab ha) hb | norm_num)
  have hneg : ∀ j, layerAverage (id : Causes n → Finset (Fin n))
      (fun E => - uncorrectable S E) j = - layerFraction S j := by
    intro j
    unfold layerFraction layerAverage
    rw [Finset.sum_neg_distrib, neg_div]
  intro i j hij
  have := hanti hij
  rw [hneg, hneg] at this
  linarith

theorem layerFraction_zero (S : Submodule Bit (Pauli n)) : layerFraction S 0 = 0 := by
  have h := layerAverage_zero (id : Causes n → Finset (Fin n)) (uncorrectable S)
  unfold layerFraction
  rw [show (0 : Fin (n + 1)) = ⟨0, Nat.zero_lt_succ n⟩ from rfl, h]
  simp [uncorrectable]

theorem layerFraction_last (S : Submodule Bit (Pauli n)) :
    layerFraction S (Fin.last n) = uncorrectable S Finset.univ :=
  layerAverage_last (id : Causes n → Finset (Fin n)) (uncorrectable S)

/-! ### B5. Repair of one-sided relative estimates of the layer fractions -/

/-- Repaired layer fractions: complement, anchored antitone repair with anchors `{0, last}`,
complement back. -/
def repairedFraction (S : Submodule Bit (Pauli n)) (c : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  1 - repair ({0, Fin.last n} : Finset (Fin (n + 1))) (fun i => 1 - layerFraction S i)
    (fun i => 1 - c i) j

section Repair

variable (S : Submodule Bit (Pauli n)) (hS : S ≤ normalizer (symplectic n) S)
  (c : Fin (n + 1) → ℝ)

include hS in
private theorem target_antitone : Antitone (fun i => 1 - layerFraction S i) := by
  intro i j hij
  have := layerFraction_monotone S hS hij
  simp only
  linarith

private theorem target_range (i : Fin (n + 1)) :
    0 ≤ 1 - layerFraction S i ∧ 1 - layerFraction S i ≤ 1 := by
  have := layerFraction_range S i
  constructor <;> linarith [this.1, this.2]

include hS in
private theorem repair_anchor_eq {a : Fin (n + 1)} (ha : a ∈ ({0, Fin.last n} : Finset _)) :
    repair ({0, Fin.last n} : Finset (Fin (n + 1))) (fun i => 1 - layerFraction S i)
      (fun i => 1 - c i) a = 1 - layerFraction S a :=
  repair_anchor _ _ _ (fun b _ => (target_range S b).1)
    (fun _b _ _d _ hbd => target_antitone S hS hbd) ha

theorem repairedFraction_monotone : Monotone (repairedFraction S c) := by
  intro i j hij
  have := repair_antitone ({0, Fin.last n} : Finset (Fin (n + 1)))
    (fun i => 1 - layerFraction S i) (fun i => 1 - c i) hij
  unfold repairedFraction
  linarith

theorem repairedFraction_range (j : Fin (n + 1)) :
    0 ≤ repairedFraction S c j ∧ repairedFraction S c j ≤ 1 := by
  have := repair_range ({0, Fin.last n} : Finset (Fin (n + 1)))
    (fun i => 1 - layerFraction S i) (fun i => 1 - c i) (fun b _ => target_range S b) j
  unfold repairedFraction
  constructor <;> linarith [this.1, this.2]

include hS in
theorem repairedFraction_zero : repairedFraction S c 0 = 0 := by
  unfold repairedFraction
  rw [repair_anchor_eq S hS c (by simp), layerFraction_zero]
  ring

include hS in
theorem repairedFraction_last :
    repairedFraction S c (Fin.last n) = layerFraction S (Fin.last n) := by
  unfold repairedFraction
  rw [repair_anchor_eq S hS c (by simp)]
  ring

include hS in
/-- One-sided relative accuracy `(1-ε) u ≤ ĉ ≤ (1+ε) u` survives the repair, for any `ε ≥ 0`. -/
theorem repairedFraction_rel {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ j, (1 - ε) * layerFraction S j ≤ c j ∧ c j ≤ (1 + ε) * layerFraction S j)
    (j : Fin (n + 1)) :
    (1 - ε) * layerFraction S j ≤ repairedFraction S c j ∧
      repairedFraction S c j ≤ (1 + ε) * layerFraction S j := by
  have h := repair_interval' ({0, Fin.last n} : Finset (Fin (n + 1)))
    (fun i => 1 - layerFraction S i) (fun i => 1 - c i) (fun i => 1 - layerFraction S i)
    (fun t => (1 + ε) * t - ε) (fun t => (1 - ε) * t + ε)
    (by
      intro s _ t _ hst
      show (1 + ε) * s - ε ≤ (1 + ε) * t - ε
      nlinarith)
    (by
      intro t ht
      show (1 + ε) * t - ε ≤ t
      nlinarith [ht.2])
    (by
      intro t ht
      show t ≤ (1 - ε) * t + ε
      nlinarith [ht.2])
    (target_antitone S hS) (target_range S) (fun _ _ => rfl)
    (by
      intro i
      show (1 + ε) * (1 - layerFraction S i) - ε ≤ 1 - c i ∧
        1 - c i ≤ (1 - ε) * (1 - layerFraction S i) + ε
      constructor <;> nlinarith [hc i])
    j
  unfold repairedFraction
  constructor <;> nlinarith [h.1, h.2]

include hS in
/-- Exact zero pattern: for `ε < 1`, the repaired fraction vanishes exactly where the true
fraction does. -/
theorem repairedFraction_eq_zero_iff {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hc : ∀ j, (1 - ε) * layerFraction S j ≤ c j ∧ c j ≤ (1 + ε) * layerFraction S j)
    (j : Fin (n + 1)) :
    repairedFraction S c j = 0 ↔ layerFraction S j = 0 := by
  have h := repairedFraction_rel S hS c hε hc j
  have hr := repairedFraction_range S c j
  have hu := layerFraction_range S j
  constructor
  · intro h0
    rw [h0] at h
    have : (1 - ε) * layerFraction S j ≤ 0 := h.1
    have hpos : 0 < 1 - ε := by linarith
    nlinarith [hu.1]
  · intro h0
    rw [h0] at h
    linarith [h.2, hr.1]

private theorem bernsteinCurve_smul (a : ℝ) (f : Fin (n + 1) → ℝ) (p : ℝ) :
    bernsteinCurve n (fun j => a * f j) p = a * bernsteinCurve n f p := by
  have := average_affine (bernsteinWeight n p) f (bernsteinWeight_sum n p) a 0
  simpa [bernsteinCurve] using this

private theorem bernsteinCurve_le {f g : Fin (n + 1) → ℝ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hfg : ∀ j, f j ≤ g j) : bernsteinCurve n f p ≤ bernsteinCurve n g p :=
  average_mono (bernsteinWeight_nonneg hp0 hp1) hfg

include hS in
/-- Curve-level accuracy: the repaired Bernstein curve is within relative error `ε` of `U(p)`. -/
theorem repairedCurve_rel {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ j, (1 - ε) * layerFraction S j ≤ c j ∧ c j ≤ (1 + ε) * layerFraction S j)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |bernsteinCurve n (repairedFraction S c) p - uncorrectableProb S p| ≤
      ε * uncorrectableProb S p := by
  rw [uncorrectableProb_eq_bernstein]
  have h1 := bernsteinCurve_le (n := n) hp0 hp1
    (fun j => (repairedFraction_rel S hS c hε hc j).1)
  have h2 := bernsteinCurve_le (n := n) hp0 hp1
    (fun j => (repairedFraction_rel S hS c hε hc j).2)
  rw [bernsteinCurve_smul] at h1 h2
  rw [abs_le]
  constructor <;> nlinarith

theorem repairedCurve_monotoneOn :
    MonotoneOn (bernsteinCurve n (repairedFraction S c)) (Set.Icc 0 1) := by
  have hanti : Antitone (fun j => 1 - repairedFraction S c j) := by
    intro i j hij
    have := repairedFraction_monotone S c hij
    simp only
    linarith
  have h := bernsteinCurve_antitone _ hanti
  intro p hp q hq hpq
  have := h hp hq hpq
  rw [bernsteinCurve_complement, bernsteinCurve_complement] at this
  linarith

theorem repairedCurve_range {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ bernsteinCurve n (repairedFraction S c) p ∧
      bernsteinCurve n (repairedFraction S c) p ≤ 1 :=
  bernsteinCurve_range hp0 hp1 (repairedFraction_range S c)

end Repair

end QecPhysical.Stabilizer.Uncorrectable

#print axioms QecReliability.PosetShapeRepair.repair_interval
#print axioms QecReliability.PosetShapeRepair.repair_relPair_of_interval
#print axioms QecReliability.ambiguity_pos_iff_exists_bad
#print axioms QecPhysical.Stabilizer.Uncorrectable.infidelity_eq_channel
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectable_iff_certificate
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectable_mono
#print axioms QecPhysical.Stabilizer.Uncorrectable.infidelity_le_uncorrectableProb
#print axioms QecPhysical.Stabilizer.Uncorrectable.channel_infidelity_le_uncorrectableProb
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectableProb_eq_bernstein
#print axioms QecPhysical.Stabilizer.Uncorrectable.layerFraction_monotone
#print axioms QecPhysical.Stabilizer.Uncorrectable.layerFraction_zero
#print axioms QecPhysical.Stabilizer.Uncorrectable.layerFraction_last
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedFraction_monotone
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedFraction_range
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedFraction_zero
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedFraction_last
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedFraction_rel
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedFraction_eq_zero_iff
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedCurve_rel
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedCurve_monotoneOn
#print axioms QecPhysical.Stabilizer.Uncorrectable.repairedCurve_range
