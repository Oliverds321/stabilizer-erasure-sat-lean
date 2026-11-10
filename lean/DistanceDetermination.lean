import QecReliability.Latent
import PhysicalBridge.PhysicalBernstein
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false

/-!
# Distance determination

Any Bernstein-form estimate `Î(p) = Σ_j c_j C(n,j) p^j (1-p)^(n-j)` with arbitrary real
coefficients that stays within relative error `ε < 1` of the true erasure infidelity
`I(p) = 1 - F(p)` for every `p ∈ (0,1]` has the same zero prefix as the true infidelity
coefficients `1 - f_j`.  Consequently its first nonzero coefficient sits at the code distance.
-/

noncomputable section

namespace QecReliability.DistanceDetermination

open scoped BigOperators
open Filter Topology

variable {n : ℕ}

/-- `bernsteinCurve n a p` divided by `p ^ j` (valid when `a` vanishes below `j`). -/
def reduced (j : Fin (n + 1)) (a : Fin (n + 1) → ℝ) (p : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), (n.choose i.val : ℝ) * p ^ (i.val - j.val) * (1 - p) ^ (n - i.val) * a i

theorem reduced_continuous (j : Fin (n + 1)) (a : Fin (n + 1) → ℝ) :
    Continuous (reduced j a) := by
  unfold reduced
  fun_prop

theorem curve_eq_pow_mul_reduced (j : Fin (n + 1)) (a : Fin (n + 1) → ℝ)
    (ha : ∀ i < j, a i = 0) (p : ℝ) :
    bernsteinCurve n a p = p ^ j.val * reduced j a p := by
  unfold bernsteinCurve average reduced
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i < j
  · simp [ha i hij]
  · have hle : j.val ≤ i.val := by
      have := not_lt.mp hij
      exact this
    have hp : p ^ i.val = p ^ j.val * p ^ (i.val - j.val) := by
      rw [← pow_add]
      congr 1
      omega
    unfold bernsteinWeight
    rw [hp]
    ring

theorem reduced_zero (j : Fin (n + 1)) (a : Fin (n + 1) → ℝ) (ha : ∀ i < j, a i = 0) :
    reduced j a 0 = (n.choose j.val : ℝ) * a j := by
  unfold reduced
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hne
    by_cases hij : i < j
    · simp [ha i hij]
    · have hgt : j.val < i.val := by
        have h1 := not_lt.mp hij
        have h2 : i.val ≠ j.val := fun h => hne (Fin.ext h)
        have h3 : j.val ≤ i.val := h1
        omega
      have hne0 : i.val - j.val ≠ 0 := by omega
      simp [zero_pow hne0]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The key step: if both coefficient tables vanish strictly below `j`, the relative
guarantee on `(0,1]` passes to the `j`-th coefficients. No sign or `ε` hypothesis is used. -/
theorem coeff_relative {b c : Fin (n + 1) → ℝ} {ε : ℝ}
    (h : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve n c p - bernsteinCurve n b p| ≤ ε * bernsteinCurve n b p)
    (j : Fin (n + 1)) (hb0 : ∀ i < j, b i = 0) (hc0 : ∀ i < j, c i = 0) :
    |c j - b j| ≤ ε * b j := by
  set G := reduced j b
  set H := reduced j c
  have hred : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ ε * G p - |H p - G p| := by
    intro p hp
    have hpj : 0 < p ^ j.val := pow_pos hp.1 _
    have h1 := h p ⟨hp.1, hp.2.le⟩
    rw [curve_eq_pow_mul_reduced j c hc0, curve_eq_pow_mul_reduced j b hb0, ← mul_sub,
      abs_mul, abs_of_pos hpj, mul_left_comm] at h1
    have h2 := le_of_mul_le_mul_left h1 hpj
    linarith
  have hcont : Continuous (fun p => ε * G p - |H p - G p|) := by
    have hG := reduced_continuous j b
    have hH := reduced_continuous j c
    fun_prop
  have htend : Tendsto (fun p => ε * G p - |H p - G p|) (𝓝[>] (0 : ℝ))
      (𝓝 (ε * G 0 - |H 0 - G 0|)) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ), (0 : ℝ) ≤ ε * G p - |H p - G p| :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT zero_lt_one) hred
  have h0 := ge_of_tendsto htend hev
  have hG0 : G 0 = (n.choose j.val : ℝ) * b j := reduced_zero j b hb0
  have hH0 : H 0 = (n.choose j.val : ℝ) * c j := reduced_zero j c hc0
  rw [hG0, hH0, ← mul_sub, abs_mul, abs_of_pos (by
      exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt) : (0 : ℝ) < n.choose j.val),
    mul_left_comm] at h0
  have hC : (0 : ℝ) < n.choose j.val := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt)
  exact le_of_mul_le_mul_left (by linarith) hC

/-- **Distance determination (analytic form).** Arbitrary real coefficients `c` whose Bernstein
curve is within relative error `ε < 1` of the Bernstein curve of nonnegative coefficients `b`
on `(0,1]` have exactly the same zero prefixes as `b`. -/
theorem zero_prefix_iff (b c : Fin (n + 1) → ℝ) (hb : ∀ j, 0 ≤ b j) {ε : ℝ} (hε : ε < 1)
    (h : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve n c p - bernsteinCurve n b p| ≤ ε * bernsteinCurve n b p)
    (j : Fin (n + 1)) :
    (∀ i ≤ j, c i = 0) ↔ (∀ i ≤ j, b i = 0) := by
  have step : ∀ m : ℕ, ∀ i : Fin (n + 1), i.val = m → i ≤ j →
      ((∀ i' ≤ j, c i' = 0) → b i = 0) ∧ ((∀ i' ≤ j, b i' = 0) → c i = 0) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi hij
      have key := fun (hb0 : ∀ i' < i, b i' = 0) (hc0 : ∀ i' < i, c i' = 0) =>
        coeff_relative h i hb0 hc0
      constructor
      · intro hc
        have hc0 : ∀ i' < i, c i' = 0 := fun i' hi' => hc i' (le_trans hi'.le hij)
        have hb0 : ∀ i' < i, b i' = 0 := fun i' hi' =>
          (ih i'.val (by rw [← hi]; exact hi') i' rfl (le_trans hi'.le hij)).1 hc
        have hk := key hb0 hc0
        rw [hc i hij, zero_sub, abs_neg, abs_of_nonneg (hb i)] at hk
        have hbi := hb i
        nlinarith
      · intro hbz
        have hb0 : ∀ i' < i, b i' = 0 := fun i' hi' => hbz i' (le_trans hi'.le hij)
        have hc0 : ∀ i' < i, c i' = 0 := fun i' hi' =>
          (ih i'.val (by rw [← hi]; exact hi') i' rfl (le_trans hi'.le hij)).2 hbz
        have hk := key hb0 hc0
        rw [hbz i hij, sub_zero, mul_zero] at hk
        exact abs_nonpos_iff.mp hk
  constructor
  · intro hc i hij
    exact (step i.val i rfl hij).1 hc
  · intro hbz i hij
    exact (step i.val i rfl hij).2 hbz

/-- First-nonzero-index form: `j` is the first nonzero index of `c` iff it is that of `b`. -/
theorem first_nonzero_iff (b c : Fin (n + 1) → ℝ) (hb : ∀ j, 0 ≤ b j) {ε : ℝ} (hε : ε < 1)
    (h : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve n c p - bernsteinCurve n b p| ≤ ε * bernsteinCurve n b p)
    (j : Fin (n + 1)) :
    (c j ≠ 0 ∧ ∀ i < j, c i = 0) ↔ (b j ≠ 0 ∧ ∀ i < j, b i = 0) := by
  have hz := zero_prefix_iff b c hb hε h
  have hbelow : (∀ i < j, c i = 0) ↔ (∀ i < j, b i = 0) := by
    constructor
    · intro hc i hij
      exact (hz i).1 (fun i' hi' => hc i' (lt_of_le_of_lt hi' hij)) i le_rfl
    · intro hbz i hij
      exact (hz i).2 (fun i' hi' => hbz i' (lt_of_le_of_lt hi' hij)) i le_rfl
  have hat : ∀ (a : Fin (n + 1) → ℝ), (∀ i < j, a i = 0) →
      ((∀ i ≤ j, a i = 0) ↔ a j = 0) := by
    intro a ha
    constructor
    · intro h'
      exact h' j le_rfl
    · intro h' i hij
      rcases lt_or_eq_of_le hij with hlt | rfl
      · exact ha i hlt
      · exact h'
  constructor
  · rintro ⟨hcj, hc⟩
    have hb' := hbelow.1 hc
    refine ⟨fun hbj => hcj ?_, hb'⟩
    exact (hat c hc).1 ((hz j).2 ((hat b hb').2 hbj))
  · rintro ⟨hbj, hb'⟩
    have hc := hbelow.2 hb'
    refine ⟨fun hcj => hbj ?_, hc⟩
    exact (hat b hb').1 ((hz j).1 ((hat c hc).2 hcj))

/-- A layer average of values `≤ 1` equals `1` iff every member of the layer has value `1`. -/
theorem layerAverage_eq_one_iff {E : Type*} (C : Causes n → E) (f : E → ℝ)
    (hf : ∀ e, f e ≤ 1) (j : Fin (n + 1)) :
    layerAverage C f j = 1 ↔ ∀ b : Causes n, hammingLayer b = j → f (C b) = 1 := by
  have hC : (0 : ℝ) < n.choose j.val := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt)
  have hcard : (∑ _b : {b : Causes n // hammingLayer b = j}, (1 : ℝ)) = n.choose j.val := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_eq_nat_card,
      hamming_layer_card]
  unfold layerAverage
  rw [div_eq_one_iff_eq hC.ne', ← hcard, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  constructor
  · intro hs
    have hs' : (∑ b : {b : Causes n // hammingLayer b = j}, (1 - f (C b))) = 0 := by
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib]
      simpa using hs
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (b : {b : Causes n // hammingLayer b = j}) _ => sub_nonneg.mpr (hf (C b.val)))).mp hs'
    intro b hb
    have := hall ⟨b, hb⟩ (Finset.mem_univ _)
    linarith
  · intro hall
    apply Finset.sum_eq_zero
    intro b _
    rw [hall b.val b.property, sub_self]

end QecReliability.DistanceDetermination

namespace QecPhysical.Stabilizer

open scoped BigOperators
open QecReliability
open QecReliability.Binary
open QecPhysical.BinaryPauli
open QecReliability.DistanceDetermination

theorem erasureScore_le_one {n : ℕ} (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    erasureScore S E ≤ 1 := by
  unfold erasureScore
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- **Distance determination (physical form).** For the iid flagged erasure channel on an
`n`-qubit stabilizer code, any Bernstein coefficients `c` (arbitrary signs) whose curve is within
relative error `ε < 1` of the optimal infidelity `1 - F(p)` for all `p ∈ [0,1]` vanish on the
prefix `≤ j` iff every erased set of size `≤ j` is perfectly correctable. -/
theorem Lift.distance_determination {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)
    (c : Fin (n + 1) → ℝ) {ε : ℝ} (hε : ε < 1)
    (h : ∀ p (hp : p ∈ Set.Icc (0 : ℝ) 1),
      |bernsteinCurve n c p - (1 - entanglementFidelity (L.erasureFlagDecoder.comp
          (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map)| ≤
        ε * (1 - entanglementFidelity (L.erasureFlagDecoder.comp
          (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map))
    (j : Fin (n + 1)) :
    (∀ i ≤ j, c i = 0) ↔ (∀ E : Finset (Fin n), E.card ≤ j.val → erasureScore S E = 1) := by
  set b : Fin (n + 1) → ℝ := fun i => 1 - layerAverage (id : Causes n → Finset (Fin n))
    (erasureScore S) i with hbdef
  have hb : ∀ i, 0 ≤ b i := fun i =>
    sub_nonneg.mpr (layerAverage_range _ (erasureScore S)
      (fun E => ⟨by unfold erasureScore; positivity, erasureScore_le_one S E⟩) i).2
  have h' : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve n c p - bernsteinCurve n b p| ≤ ε * bernsteinCurve n b p := by
    intro p hp
    have hp' : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2⟩
    have hF := (L.iidLatentErasure_optimum (id : Causes n → Finset (Fin n)) p hp'.1 hp'.2).1
    have hcomp : bernsteinCurve n b p =
        1 - bernsteinCurve n (layerAverage (id : Causes n → Finset (Fin n)) (erasureScore S)) p :=
      bernsteinCurve_complement n _ p
    have := h p hp'
    rw [hF] at this
    rw [hcomp]
    exact this
  rw [zero_prefix_iff b c hb hε h' j]
  have hlayer : ∀ i : Fin (n + 1), b i = 0 ↔
      ∀ E : Causes n, hammingLayer E = i → erasureScore S E = 1 := by
    intro i
    rw [hbdef]
    simp only [sub_eq_zero]
    rw [eq_comm]
    exact layerAverage_eq_one_iff (id : Causes n → Finset (Fin n)) (erasureScore S)
      (erasureScore_le_one S) i
  constructor
  · intro hall E hE
    have hi : hammingLayer E ≤ j := by
      show E.card ≤ j.val
      exact hE
    exact (hlayer (hammingLayer E)).1 (hall _ hi) E rfl
  · intro hall i hij
    apply (hlayer i).2
    intro E hE
    apply hall E
    have := congrArg Fin.val hE
    have hij' : i.val ≤ j.val := hij
    simp only [hammingLayer] at this
    omega

end QecPhysical.Stabilizer

#print axioms QecReliability.DistanceDetermination.zero_prefix_iff
#print axioms QecReliability.DistanceDetermination.first_nonzero_iff
#print axioms QecPhysical.Stabilizer.Lift.distance_determination
