import Mathlib.Data.Rat.Cast.Lemmas
import QecReliability.BinarySymplectic
import QecReliability.HammingMonotonicity
import QecReliability.BernsteinShape
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Cast.CharZero

/-!
The composed mathematical bridge for sparse-code reliability.

`score` is defined algebraically. Identifying it with the optimum over quantum
recovery channels is a separate, unformalized physics obligation. The estimate
hypotheses below are explicit numerical hypotheses; no fast counting algorithm
or complexity-theoretic statement is postulated.
-/

noncomputable section

namespace QecReliability.Binary

open Module
open scoped BigOperators

def score {n : ℕ} (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) : ℝ :=
  (2 ^ ambiguity (F := Bit) (symplectic n) S (supported E) : ℝ)⁻¹

theorem score_range {n : ℕ} (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    0 < score S E ∧ score S E ≤ 1 := by
  constructor
  · unfold score
    positivity
  · have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
      (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
        (n := ambiguity (F := Bit) (symplectic n) S (supported E)))
    simpa [score] using h

theorem score_antitone {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S) {E E' : Finset (Fin n)}
    (h : E ⊆ E') : score S E' ≤ score S E := by
  have hd := ambiguity_erasure_mono S hS h
  have hp := pow_right_mono₀ (show (1 : ℝ) ≤ 2 by norm_num) hd
  have hpos : (0 : ℝ) < 2 ^ ambiguity (F := Bit) (symplectic n) S (supported E) := by positivity
  simpa [score] using one_div_le_one_div_of_le hpos hp

@[simp] theorem score_empty {n : ℕ} (S : Submodule Bit (Pauli n)) : score S ∅ = 1 := by
  simp [score]

theorem score_full {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S) :
    score S Finset.univ = (4 ^ (n - finrank Bit S) : ℝ)⁻¹ := by
  rw [score, ambiguity_full S hS, pow_mul]
  norm_num

theorem score_eq_good_fraction {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S) (E : Finset (Fin n)) :
    (Nat.card {z : normalizer (F := Bit) (symplectic n) S //
      Good (F := Bit) (symplectic n) S (supported E) z} : ℝ) /
      Nat.card (normalizer (F := Bit) (symplectic n) S) = score S E := by
  have h : (Nat.card {z : normalizer (F := Bit) (symplectic n) S //
      Good (F := Bit) (symplectic n) S (supported E) z} : ℚ) /
      Nat.card (normalizer (F := Bit) (symplectic n) S) =
      (2 ^ ambiguity (F := Bit) (symplectic n) S (supported E) : ℚ)⁻¹ := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using
      good_card_fraction (F := Bit) (symplectic n) (symplectic_nondegenerate n)
        (symplectic_refl n) S (supported E) hS
  unfold score
  have hc := congrArg (fun q : ℚ => (q : ℝ)) h
  simpa only [Rat.cast_div, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat] using hc

def goodCoefficient {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (j : Fin (r + 1)) : ℕ :=
  Nat.card {bz : {b : Causes r // hammingLayer b = j} ×
      normalizer (F := Bit) (symplectic n) S //
    Good (F := Bit) (symplectic n) S (supported (C bz.1)) bz.2}

def badCoefficient {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (j : Fin (r + 1)) : ℕ :=
  Nat.card {bz : {b : Causes r // hammingLayer b = j} ×
      normalizer (F := Bit) (symplectic n) S //
    Bad (F := Bit) (symplectic n) S (supported (C bz.1)) bz.2}

theorem coefficient_partition {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (j : Fin (r + 1)) :
    goodCoefficient S C j + badCoefficient S C j =
      r.choose j.val * Nat.card (normalizer (F := Bit) (symplectic n) S) := by
  unfold goodCoefficient badCoefficient
  have h := latent_pair_partition C hammingLayer j
    (fun E (z : normalizer (F := Bit) (symplectic n) S) =>
      Good (F := Bit) (symplectic n) S (supported E) z)
    (fun E (z : normalizer (F := Bit) (symplectic n) S) =>
      Bad (F := Bit) (symplectic n) S (supported E) z)
    (fun E z => bad_iff_not_good (F := Bit) (symplectic n) (symplectic_nondegenerate n)
      (symplectic_refl n) S (supported E) z)
  simpa only [hamming_layer_card] using h

theorem good_coefficient_normalized {n r : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : Causes r → Finset (Fin n)) (j : Fin (r + 1)) :
    (goodCoefficient S C j : ℝ) /
      ((r.choose j.val : ℝ) * Nat.card (normalizer (F := Bit) (symplectic n) S)) =
      layerAverage C (score S) j := by
  classical
  unfold goodCoefficient
  rw [pair_predicate_card (fun (b : {b : Causes r // hammingLayer b = j})
    (z : normalizer (F := Bit) (symplectic n) S) =>
      Good (F := Bit) (symplectic n) S (supported (C b)) z), Nat.cast_sum]
  rw [mul_comm (r.choose j.val : ℝ), div_mul_eq_div_div, Finset.sum_div]
  unfold layerAverage
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact score_eq_good_fraction S hS (C b)

theorem coefficient_total_pos {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (j : Fin (r + 1)) :
    0 < (goodCoefficient S C j : ℝ) + badCoefficient S C j := by
  rw [← Nat.cast_add, coefficient_partition, Nat.cast_mul, normalizer_card]
  have hchoose : 0 < (r.choose j.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt)
  positivity

/-- The complete numerical transfer, conditional only on explicit coefficient estimates. -/
theorem latent_curve_two_tail_relative {n r : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : Causes r → Finset (Fin n)) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (Ah Bh : Fin (r + 1) → ℝ)
    (hAh : ∀ j, |Ah j - goodCoefficient S C j| ≤ (ε / 3) * goodCoefficient S C j)
    (hBh : ∀ j, |Bh j - badCoefficient S C j| ≤ (ε / 3) * badCoefficient S C j) :
    ∀ p, 0 ≤ p → p ≤ 1 →
      RelPair ε (latentCurve C (score S) p)
        (bernsteinCurve r (fun j => Ah j / (Ah j + Bh j)) p) ∧
      0 ≤ bernsteinCurve r (fun j => Ah j / (Ah j + Bh j)) p ∧
      bernsteinCurve r (fun j => Ah j / (Ah j + Bh j)) p ≤ 1 := by
  have h := normalized_bernstein (fun j => (goodCoefficient S C j : ℝ))
    (fun j => (badCoefficient S C j : ℝ)) Ah Bh hε hε1
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    (coefficient_total_pos S C) hAh hBh
  have heq : (fun j => (goodCoefficient S C j : ℝ) /
      ((goodCoefficient S C j : ℝ) + badCoefficient S C j)) = layerAverage C (score S) := by
    funext j
    rw [← Nat.cast_add, coefficient_partition, Nat.cast_mul]
    exact good_coefficient_normalized S hS C j
  rw [heq] at h
  simpa only [latentCurve_eq_bernstein] using h

theorem latent_score_layers_antitone {n r : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : Causes r → Finset (Fin n)) (hC : ∀ a b, a ⊆ b → C a ⊆ C b) :
    Antitone (layerAverage C (score S)) :=
  layerAverage_antitone C (score S) (fun a b hab => score_antitone S hS (hC a b hab))

def shapeCorrectedCurve {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (Ah Bh : Fin (r + 1) → ℝ) (p : ℝ) : ℝ :=
  bernsteinCurve r (shapeCoefficients (layerAverage C (score S))
    (fun j => Ah j / (Ah j + Bh j))) p

/-- The whole-curve theorem with actual curve monotonicity and exact endpoints. -/
theorem latent_curve_shape_contract {n r : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : Causes r → Finset (Fin n)) (hC : ∀ a b, a ⊆ b → C a ⊆ C b)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (Ah Bh : Fin (r + 1) → ℝ)
    (hAh : ∀ j, |Ah j - goodCoefficient S C j| ≤ (ε / 3) * goodCoefficient S C j)
    (hBh : ∀ j, |Bh j - badCoefficient S C j| ≤ (ε / 3) * badCoefficient S C j) :
    AntitoneOn (shapeCorrectedCurve S C Ah Bh) (Set.Icc 0 1) ∧
      shapeCorrectedCurve S C Ah Bh 0 = score S (C ∅) ∧
      shapeCorrectedCurve S C Ah Bh 1 = score S (C Finset.univ) ∧
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        RelPair ε (latentCurve C (score S) p) (shapeCorrectedCurve S C Ah Bh p) ∧
        score S (C Finset.univ) ≤ shapeCorrectedCurve S C Ah Bh p ∧
        shapeCorrectedCurve S C Ah Bh p ≤ score S (C ∅) ∧
        0 ≤ shapeCorrectedCurve S C Ah Bh p ∧ shapeCorrectedCurve S C Ah Bh p ≤ 1 := by
  have hpair : ∀ j, RelPair ε (layerAverage C (score S) j) (Ah j / (Ah j + Bh j)) := by
    intro j
    have he : (goodCoefficient S C j : ℝ) /
        ((goodCoefficient S C j : ℝ) + badCoefficient S C j) = layerAverage C (score S) j := by
      rw [← Nat.cast_add, coefficient_partition, Nat.cast_mul]
      exact good_coefficient_normalized S hS C j
    rw [← he]
    exact (normalize_counts hε hε1 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (coefficient_total_pos S C j) (hAh j) (hBh j)).2.2.2
  have h := shape_curve_contract (layerAverage C (score S)) (fun j => Ah j / (Ah j + Bh j))
    hε hε1 (layerAverage_range C (score S) (fun E => ⟨(score_range S E).1.le, (score_range S E).2⟩))
    (latent_score_layers_antitone S hS C hC) hpair
  unfold shapeCorrectedCurve
  simpa only [latentCurve_eq_bernstein, layerAverage_zero, layerAverage_last] using h

end QecReliability.Binary
