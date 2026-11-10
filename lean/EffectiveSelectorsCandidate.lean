import QecReliability.WalkCodingBridge

/-!

Only finite recursion and integer comparisons occur in the two selectors.

-/
namespace QecReliability.UniformAdapter
open CodeHash ExpanderWalk

/-- Scan from `start`, stopping at the first hit; `fuel` is a finite safety bound.
The zero-fuel fallback is justified by `firstHit_spec`, never by a search oracle. -/
def firstHit (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ → ℕ
  | 0, start => start
  | fuel + 1, start => if P start then start else firstHit P fuel (start + 1)

theorem firstHit_spec (P : ℕ → Prop) [DecidablePred P] (fuel start : ℕ)
    (hex : ∃ j, start ≤ j ∧ j ≤ start + fuel ∧ P j) :
    P (firstHit P fuel start) ∧ start ≤ firstHit P fuel start ∧
      firstHit P fuel start ≤ start + fuel ∧
      ∀ j, start ≤ j → j < firstHit P fuel start → ¬ P j := by
  induction fuel generalizing start with
  | zero =>
    obtain ⟨j, hj₀, hj₁, hj⟩ := hex
    have he : j = start := by omega
    subst j
    simpa [firstHit] using And.intro hj
      (And.intro (le_refl start) (And.intro (le_refl start)
        (show ∀ j, start ≤ j → j < start → ¬ P j from by intros; omega)))
  | succ fuel ih =>
    by_cases hs : P start
    · simp only [firstHit, if_pos hs]
      exact ⟨hs, le_rfl, by omega, by intros; omega⟩
    · have hex' : ∃ j, start + 1 ≤ j ∧ j ≤ (start + 1) + fuel ∧ P j := by
        obtain ⟨j, hj₀, hj₁, hj⟩ := hex
        have hne : j ≠ start := by intro he; exact hs (he ▸ hj)
        exact ⟨j, by omega, by omega, hj⟩
      obtain ⟨hp, hlo, hhi, hmin⟩ := ih (start + 1) hex'
      simp only [firstHit, if_neg hs]
      refine ⟨hp, by omega, by omega, ?_⟩
      intro j hj hjlt
      by_cases he : j = start
      · simpa [he] using hs
      · exact hmin j (by omega) hjlt

/-- An executable first adequate dyadic index. It does not use `Nat.find`. -/
def dyadicUp (base target : ℕ) : ℕ :=
  firstHit (fun e => target ≤ base * 2 ^ e) target 0

theorem dyadicUp_spec (base target : ℕ) (hb : 0 < base) :
    target ≤ base * 2 ^ dyadicUp base target ∧
    ∀ e, e < dyadicUp base target → base * 2 ^ e < target := by
  have hw : target ≤ base * 2 ^ target :=
    (Nat.lt_two_pow_self (n := target)).le.trans (Nat.le_mul_of_pos_left _ hb)
  have hs := firstHit_spec (fun e => target ≤ base * 2 ^ e) target 0
    ⟨target, by omega, by omega, hw⟩
  exact ⟨hs.1, fun e he => Nat.lt_of_not_ge (hs.2.2.2 e (Nat.zero_le e) he)⟩

theorem dyadicUp_eq_index (base target : ℕ) (hb : 0 < base) :
    dyadicUp base target = dyadicIndex base target hb := by
  have hs := dyadicUp_spec base target hb
  apply Nat.le_antisymm
  · by_contra h
    have hlt : dyadicIndex base target hb < dyadicUp base target := by omega
    have hh := hs.2 _ hlt
    have hg := dyadicLength_ge base target hb
    change target ≤ base * 2 ^ dyadicIndex base target hb at hg
    omega
  · exact Nat.find_min' (dyadic_exists base target hb) hs.1

def dyadicValue (base target : ℕ) : ℕ := base * 2 ^ dyadicUp base target

theorem dyadicValue_eq_length (base target : ℕ) (hb : 0 < base) :
    dyadicValue base target = dyadicLength base target hb := by
  simp only [dyadicValue, dyadicLength, dyadicUp_eq_index base target hb]

theorem dyadicValue_bound (base target : ℕ) (hb : 0 < base) :
    dyadicValue base target ≤ max base (2 * target) := by
  rw [dyadicValue_eq_length base target hb]
  exact dyadicLength_le base target hb

/-- Bounded arithmetic search only. This never searches graph candidates. -/
def ceilSquare (N : ℕ) : ℕ := firstHit (fun s => N ≤ s * s) N 1

theorem ceilSquare_spec (N : ℕ) (hN : 0 < N) :
    1 ≤ ceilSquare N ∧ N ≤ ceilSquare N * ceilSquare N ∧
    ∀ s, 1 ≤ s → s < ceilSquare N → s * s < N := by
  have hsq : N ≤ N * N := by nlinarith
  have h := firstHit_spec (fun s => N ≤ s * s) N 1
    ⟨N, hN, by omega, hsq⟩
  exact ⟨h.2.1, h.1, fun s hs hs' => Nat.lt_of_not_ge (h.2.2.2 s hs hs')⟩

theorem ceilSquare_lower (N : ℕ) (hN : 0 < N) :
    N ≤ ceilSquare N * ceilSquare N := (ceilSquare_spec N hN).2.1

theorem ceilSquare_upper (N : ℕ) (hN : 0 < N) :
    ceilSquare N * ceilSquare N ≤ 2 * N := by
  obtain ⟨hs, _, hmin⟩ := ceilSquare_spec N hN
  by_cases he : ceilSquare N = 1
  · rw [he]; omega
  · obtain ⟨s, he⟩ : ∃ s, ceilSquare N = s + 2 := by
      exact ⟨ceilSquare N - 2, by omega⟩
    have hprev := hmin (s + 1) (by omega) (by omega)
    rw [he]
    nlinarith [Nat.zero_le (s * s)]

theorem ceilSquare_ge_three (N : ℕ) (hN : 8 ≤ N) : 3 ≤ ceilSquare N := by
  have hh := ceilSquare_lower N (by omega)
  by_contra hn
  have hs : ceilSquare N ≤ 2 := by omega
  have hsq := Nat.mul_le_mul hs hs
  omega

/-- Bernoulli-style rational decay, without logarithms or a least-real search. -/
theorem decay_mul_linear_le_one {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (k : ℕ) :
    (1-c)^k * (1+(k:ℝ)*c) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ (1-c)^k := pow_nonneg (by linarith) k
    have hstep : (1-c)*(1+((k+1:ℕ):ℝ)*c) ≤ 1+(k:ℝ)*c := by
      push_cast
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (k:ℝ)+1 by positivity) (sq_nonneg c)]
    calc
      (1-c)^(k+1)*(1+((k+1:ℕ):ℝ)*c)
          = (1-c)^k*((1-c)*(1+((k+1:ℕ):ℝ)*c)) := by rw [pow_succ]; ring
      _ ≤ (1-c)^k*(1+(k:ℝ)*c) := mul_le_mul_of_nonneg_left hstep hp
      _ ≤ 1 := ih

/-- A deliberately loose, closed-form clock, constant in every input length. -/
def walkClock (den : ℕ) : ℕ := 256 * den ^ 2

theorem rational_fixed_walk_small (num den : ℕ) (hp : 0 < num) (hpd : num ≤ den) :
    (1-(1/32:ℝ)*(((num:ℝ)/den)/2))^(walkClock den) < ((num:ℝ)/den)/4 := by
  have hd : 0 < den := lt_of_lt_of_le hp hpd
  have hdR : (0:ℝ) < den := by exact_mod_cast hd
  have hpR : (1:ℝ) ≤ num := by exact_mod_cast (show 1 ≤ num by omega)
  have hpdR : (num:ℝ) ≤ den := by exact_mod_cast hpd
  have ha₀ : (0:ℝ) < (num:ℝ)/den := div_pos (by linarith) hdR
  have ha₁ : (num:ℝ)/den ≤ 1 := (div_le_one hdR).2 hpdR
  have hc₀ : (0:ℝ) ≤ ((num:ℝ)/den)/64 := by positivity
  have hc₁ : ((num:ℝ)/den)/64 ≤ 1 := by linarith
  have hdec := decay_mul_linear_le_one hc₀ hc₁ (walkClock den)
  have hf : 1+(walkClock den:ℝ)*(((num:ℝ)/den)/64) =
      1+4*(num:ℝ)*(den:ℝ) := by
    simp only [walkClock, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp [ne_of_gt hdR]
    <;> ring
  rw [hf] at hdec
  have hp2 : (1:ℝ) ≤ (num:ℝ)^2 := by nlinarith
  have hnum : 4*(den:ℝ) < (num:ℝ)+4*(num:ℝ)^2*(den:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hp2 (show (0:ℝ) ≤ 4*(den:ℝ) by positivity)]
  have hprod : 1 < (((num:ℝ)/den)/4)*(1+4*(num:ℝ)*(den:ℝ)) := by
    have h : (1:ℝ) < ((num:ℝ)+4*(num:ℝ)^2*(den:ℝ))/(4*(den:ℝ)) :=
      (lt_div_iff₀ (show (0:ℝ) < 4*(den:ℝ) by positivity)).2 (by simpa using hnum)
    convert h using 1 <;> field_simp [ne_of_gt hdR] <;> ring
  have hbase : 1-(1/32:ℝ)*(((num:ℝ)/den)/2) = 1-((num:ℝ)/den)/64 := by ring
  rw [hbase]
  by_contra hh
  have hle : ((num:ℝ)/den)/4 ≤ (1-((num:ℝ)/den)/64)^walkClock den := le_of_not_gt hh
  have hm := mul_le_mul_of_nonneg_right hle
    (show (0:ℝ) ≤ 1+4*(num:ℝ)*(den:ℝ) by positivity)
  linarith

end QecReliability.UniformAdapter
