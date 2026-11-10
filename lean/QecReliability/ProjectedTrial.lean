import QecReliability.HashConfidence
import QecReliability.TargetScale

/-! A total capped-count trial. Exact emptiness and capped enumeration are interfaces;
no SAT implementation, query bound, or hash-circuit construction is assumed proved. -/

noncomputable section
namespace QecReliability
namespace HashStages

variable {Ω A : Type*} [Fintype Ω] {q : ℕ}

def cellCard (H : HashStages Ω A q) (S : Finset A) (r : Fin (q + 1)) (ω : Ω) : ℕ := by
  classical
  exact (S.filter (fun a => H.hash r ω a = zeroCell r.val)).card

theorem cast_cellCard (H : HashStages Ω A q) (S : Finset A) (r : Fin (q + 1)) (ω : Ω) :
    (H.cellCard S r ω : ℝ) = H.count S r ω := by
  classical
  unfold cellCard count PairwiseHashFamily.cellCount PairwiseHashFamily.cellIndicator indicator
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : H.hash r ω a = zeroCell r.val <;> simp [view, ha]

theorem cellCard_zero (H : HashStages Ω A q) (S : Finset A) (ω : Ω) :
    H.cellCard S 0 ω = S.card := by
  classical
  have h : ∀ a, H.hash 0 ω a = zeroCell 0 := by
    intro a
    apply Fin.ext
    have := (H.hash 0 ω a).isLt
    simp only [Fin.val_zero, pow_zero] at this
    change (H.hash 0 ω a).val = 0
    omega
  simp [cellCard, h]

def truncate (H : HashStages Ω A q) (R : ℕ) (hRq : R ≤ q) : HashStages Ω A R where
  law := H.law
  hash r := H.hash (Fin.castLE (Nat.succ_le_succ hRq) r)
  uniform r := H.uniform (Fin.castLE (Nat.succ_le_succ hRq) r)
  pairwise r := H.pairwise (Fin.castLE (Nat.succ_le_succ hRq) r)

end HashStages

/-- Only exact emptiness and exact truncation of DISTINCT projected models are required. -/
structure ExactTrialOracle {Ω A : Type*} [Fintype Ω] {q : ℕ}
    (H : HashStages Ω A q) (S : Finset A) where
  nonempty : Bool
  nonempty_spec : nonempty = true ↔ S.Nonempty
  capped : ℕ → Fin (q + 1) → Ω → ℕ
  capped_spec : ∀ cap r ω, capped cap r ω = min (H.cellCard S r ω) cap

namespace ExactTrialOracle
variable {Ω A : Type*} [Fintype Ω] {q : ℕ} {H : HashStages Ω A q} {S : Finset A}

/-- A finite reference implementation; no efficiency claim is attached. -/
def canonical (H : HashStages Ω A q) (S : Finset A) : ExactTrialOracle H S where
  nonempty := decide S.Nonempty
  nonempty_spec := by simp
  capped cap r ω := min (H.cellCard S r ω) cap
  capped_spec := by intros; rfl

def accepted (O : ExactTrialOracle H S) (B : ℕ) (ω : Ω) : Finset (Fin (q + 1)) :=
  Finset.univ.filter (fun r => O.capped (4 * B + 1) r ω ≤ 4 * B)

theorem mem_accepted (O : ExactTrialOracle H S) (B : ℕ) (ω : Ω) (r : Fin (q + 1)) :
    r ∈ O.accepted B ω ↔ H.cellCard S r ω ≤ 4 * B := by
  simp only [accepted, Finset.mem_filter, Finset.mem_univ, true_and, O.capped_spec]
  omega

theorem accepted_exact (O : ExactTrialOracle H S) {B : ℕ} {ω : Ω} {r : Fin (q + 1)}
    (hr : r ∈ O.accepted B ω) : O.capped (4 * B + 1) r ω = H.cellCard S r ω := by
  rw [O.capped_spec, min_eq_left]
  have := (O.mem_accepted B ω r).mp hr
  omega

/-- Exact zero first; first acceptable scale otherwise. Positive floor and no-stop fallback are 1. -/
def trial (O : ExactTrialOracle H S) (B : ℕ) (ω : Ω) : ℕ :=
  if O.nonempty then
    if h : (O.accepted B ω).Nonempty then
      let r := (O.accepted B ω).min' h
      max 1 (2 ^ r.val * O.capped (4 * B + 1) r ω)
    else 1
  else 0

theorem trial_positive (O : ExactTrialOracle H S) (B : ℕ) (ω : Ω) (hS : S.Nonempty) :
    0 < O.trial B ω := by
  simp only [trial, (O.nonempty_spec).mpr hS, ↓reduceIte]
  split_ifs <;> omega

theorem trial_zero_iff (O : ExactTrialOracle H S) (B : ℕ) (ω : Ω) :
    O.trial B ω = 0 ↔ S = ∅ := by
  classical
  by_cases hS : S.Nonempty
  · have hp := O.trial_positive B ω hS
    simp [ne_of_gt hp, Finset.Nonempty.ne_empty hS]
  · have hn : O.nonempty ≠ true := fun h => hS (O.nonempty_spec.mp h)
    simp [trial, hn, Finset.not_nonempty_iff_eq_empty.mp hS]

theorem trial_fallback (O : ExactTrialOracle H S) (B : ℕ) (ω : Ω)
    (hS : S.Nonempty) (hn : ¬ (O.accepted B ω).Nonempty) : O.trial B ω = 1 := by
  simp [trial, O.nonempty_spec.mpr hS, hn]

theorem first_accepted_le (O : ExactTrialOracle H S) (B : ℕ) (ω : Ω)
    (h : (O.accepted B ω).Nonempty) {r : Fin (q + 1)} (hr : r ∈ O.accepted B ω) :
    (O.accepted B ω).min' h ≤ r := Finset.min'_le _ _ hr

theorem trial_small (O : ExactTrialOracle H S) (B : ℕ) (ω : Ω)
    (hsmall : S.card ≤ 4 * B) : O.trial B ω = S.card := by
  classical
  by_cases hS : S.Nonempty
  · have hz : (0 : Fin (q + 1)) ∈ O.accepted B ω := by
      rw [O.mem_accepted, H.cellCard_zero]
      exact hsmall
    have ha : (O.accepted B ω).Nonempty := ⟨0, hz⟩
    have hmin : (O.accepted B ω).min' ha = 0 :=
      le_antisymm (O.first_accepted_le B ω ha hz) (Fin.zero_le _)
    simp only [trial, O.nonempty_spec.mpr hS, ↓reduceIte, dif_pos ha]
    rw [hmin, O.accepted_exact hz, H.cellCard_zero]
    simp only [Fin.val_zero, pow_zero, one_mul]
    exact max_eq_right (Finset.card_pos.mpr hS)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [(O.trial_zero_iff B ω).mpr he, he, Finset.card_empty]

end ExactTrialOracle

theorem positive_floor_relative {M x ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hx : |x - M| ≤ ε * M) : |max 1 x - M| ≤ ε * M := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  apply abs_le.mpr
  constructor
  · have := le_max_right (1 : ℝ) x; linarith
  · have he : 0 ≤ ε * M := mul_nonneg hε (by linarith)
    have : max 1 x ≤ M + ε * M := max_le (by linarith) (by linarith)
    linarith

namespace ExactTrialOracle
variable {Ω A : Type*} [Fintype Ω] {q : ℕ} {H : HashStages Ω A q} {S : Finset A}

theorem trial_accurate_on_prefix (O : ExactTrialOracle H S) (B : ℕ)
    (hS : S.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {R : ℕ} (hRq : R ≤ q)
    (htarget : (S.card : ℝ) / (2 : ℝ) ^ R < 2 * B) (ω : Ω)
    (hgood : ∀ r : Fin (R + 1),
      |(H.truncate R hRq).count S r ω - (H.truncate R hRq).mean S r| ≤
        ε * (H.truncate R hRq).mean S r) :
    |(O.trial B ω : ℝ) - (S.card : ℝ)| ≤ ε * (S.card : ℝ) := by
  let t : Fin (q + 1) := ⟨R, by omega⟩
  have htcount : (H.cellCard S t ω : ℝ) < 4 * (B : ℝ) := by
    rw [H.cast_cellCard]
    exact (H.truncate R hRq).target_accepts_on_good_event hS hε1 htarget ω hgood
  have ht : t ∈ O.accepted B ω := by
    rw [O.mem_accepted]
    exact_mod_cast htcount.le
  have ha : (O.accepted B ω).Nonempty := ⟨t, ht⟩
  let r := (O.accepted B ω).min' ha
  have hrmem : r ∈ O.accepted B ω := Finset.min'_mem _ ha
  have hrle : r ≤ t := O.first_accepted_le B ω ha ht
  let r' : Fin (R + 1) := ⟨r.val, by have := hrle; change r.val ≤ R at this; omega⟩
  have herr : |(2 : ℝ) ^ r.val * H.count S r ω - (S.card : ℝ)| ≤ ε * (S.card : ℝ) := by
    apply le_of_not_gt
    intro hbad
    have hb := ((H.truncate R hRq).rescaled_error_iff S r' ω ε).mp hbad
    exact (not_lt_of_ge (hgood r')) hb
  have hM : 1 ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hf := positive_floor_relative hM hε herr
  simp only [trial, O.nonempty_spec.mpr hS, ↓reduceIte, dif_pos ha]
  change |((max 1 (2 ^ r.val * O.capped (4 * B + 1) r ω) : ℕ) : ℝ) -
    (S.card : ℝ)| ≤ ε * (S.card : ℝ)
  rw [O.accepted_exact hrmem]
  simpa only [Nat.cast_max, Nat.cast_one, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, H.cast_cellCard] using hf

/-- Full single-trial guarantee, including empty and small sets and every stopping/fallback case. -/
theorem trial_failure_le_one_eighth (O : ExactTrialOracle H S) (B : ℕ)
    (hB : 0 < B) (hM : S.card ≤ 2 ^ q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbudget : 16 ≤ ε ^ 2 * (B : ℝ)) :
    H.law.prob (fun ω => ε * (S.card : ℝ) <
      |(O.trial B ω : ℝ) - (S.card : ℝ)|) ≤ 1 / 8 := by
  classical
  by_cases hsmall : S.card ≤ 4 * B
  · have he : (fun ω => ε * (S.card : ℝ) < |(O.trial B ω : ℝ) - (S.card : ℝ)|) =
        (fun _ => False) := by
      funext ω
      rw [O.trial_small B ω hsmall]
      simp [not_lt_of_ge (mul_nonneg hε.le (Nat.cast_nonneg S.card))]
    rw [he]
    norm_num [FiniteProbability.prob, indicator, FiniteProbability.expect, average]
  · have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hBM : B ≤ S.card := by omega
    let R := targetScale q S.card B hBM
    have hRq : R ≤ q := (targetScale_spec hBM hB hM).1
    have htarget := targetScale_real_spec hBM hB hM
    have hb : 16 ≤ ε ^ 2 * (H.truncate R hRq).mean S ⟨R, Nat.lt_succ_self R⟩ :=
      hbudget.trans (mul_le_mul_of_nonneg_left htarget.1 (sq_nonneg ε))
    apply le_trans (H.law.prob_mono ?_)
      ((H.truncate R hRq).all_scales_failure_le_one_eighth hS hε hb)
    intro ω hbad
    by_contra hn
    push_neg at hn
    exact (not_lt_of_ge (O.trial_accurate_on_prefix B hS hε.le hε1 hRq htarget.2 ω hn)) hbad

theorem binary_trial_failure_le_one_eighth {Ω : Type*} [Fintype Ω] {q : ℕ}
    {H : HashStages Ω (BitModels q) q} {S : Finset (BitModels q)}
    (O : ExactTrialOracle H S) (B : ℕ) (hB : 0 < B)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hbudget : 16 ≤ ε ^ 2 * (B : ℝ)) :
    H.law.prob (fun ω => ε * (S.card : ℝ) <
      |(O.trial B ω : ℝ) - (S.card : ℝ)|) ≤ 1 / 8 :=
  O.trial_failure_le_one_eighth B hB (bitModels_card_bound S) hε hε1 hbudget

end ExactTrialOracle
end QecReliability
