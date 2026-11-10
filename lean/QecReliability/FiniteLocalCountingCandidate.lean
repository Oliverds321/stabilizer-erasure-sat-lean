/-






This file is semantic finite existence only. It does not choose matrix DATA.

-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
open Finset

namespace FiniteLocalCountingCandidate

abbrev F := ZMod 2
abbrev Word (n : ℕ) := Fin n → F
abbrev Mat (k h : ℕ) := Fin h → Fin k → F

def weight {ι : Type*} [Fintype ι] (x : ι → F) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

def zeroCount {ι : Type*} [Fintype ι] (x : ι → F) : ℕ :=
  (Finset.univ.filter fun i => x i = 0).card

def score {ι : Type*} [Fintype ι] (x : ι → F) : ℕ :=
  ∏ i, if x i = 0 then 32 else 1

lemma zeroCount_add_weight {ι : Type*} [Fintype ι] (x : ι → F) :
    zeroCount x + weight x = Fintype.card ι := by
  classical
  simpa [zeroCount, weight] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (fun i => x i = 0))

lemma score_eq {ι : Type*} [Fintype ι] (x : ι → F) :
    score x = 32 ^ zeroCount x := by
  classical
  simp [score, zeroCount, Finset.prod_ite]

/-- The only two-element alphabet enumeration. This never enumerates messages
or matrices: the sum has exactly two terms. -/
lemma sum_bit_score : (∑ a : F, if a = 0 then (32 : ℕ) else 1) = 33 := by
  decide

/-- Product-of-sums replaces the optional binomial/powerset layer. -/
lemma score_moment {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∑ x : ι → F, score x) = 33 ^ Fintype.card ι := by
  classical
  calc
    (∑ x : ι → F, score x) =
        ∏ _i : ι, ∑ a : F, if a = 0 then (32 : ℕ) else 1 := by
      simpa only [score] using
        (Fintype.prod_sum (fun (_i : ι) (a : F) =>
          if a = 0 then (32 : ℕ) else 1)).symm
    _ = 33 ^ Fintype.card ι := by simp only [sum_bit_score, Finset.prod_const,
      Finset.card_univ]

def ball {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) : Finset (ι → F) :=
  Finset.univ.filter fun x => weight x < r

/-- Entirely integral exponential-moment bound; no logarithms or entropy. -/
theorem ball_weighted_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) :
    (ball (ι := ι) r).card * 32 ^ (Fintype.card ι - r) ≤
      33 ^ Fintype.card ι := by
  classical
  calc
    (ball (ι := ι) r).card * 32 ^ (Fintype.card ι - r) =
        ∑ _x ∈ ball (ι := ι) r, 32 ^ (Fintype.card ι - r) := by simp
    _ ≤ ∑ x ∈ ball (ι := ι) r, score x := by
      apply Finset.sum_le_sum
      intro x hx
      have hw : weight x < r := (Finset.mem_filter.mp hx).2
      have hc := zeroCount_add_weight x
      rw [score_eq]
      exact pow_le_pow_right' (by decide : (1 : ℕ) ≤ 32) (by omega)
    _ ≤ ∑ x : ι → F, score x :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 33 ^ Fintype.card ι := score_moment

def pairBall (k h r : ℕ) : Finset (Word k × Word h) :=
  Finset.univ.filter fun xy => weight xy.1 + weight xy.2 < r

def pairScore {k h : ℕ} (xy : Word k × Word h) : ℕ :=
  score xy.1 * score xy.2

lemma pairScore_eq {k h : ℕ} (xy : Word k × Word h) :
    pairScore xy = 32 ^ (zeroCount xy.1 + zeroCount xy.2) := by
  simp only [pairScore, score_eq, pow_add]

lemma pairScore_moment (k h : ℕ) :
    (∑ xy : Word k × Word h, pairScore xy) = 33 ^ (k + h) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [pairScore]
  rw [← Finset.sum_mul_sum, score_moment, score_moment]
  simp only [Fintype.card_fin, pow_add]

theorem pairBall_weighted_bound (k h r : ℕ) :
    (pairBall k h r).card * 32 ^ (k + h - r) ≤ 33 ^ (k + h) := by
  classical
  calc
    (pairBall k h r).card * 32 ^ (k + h - r) =
        ∑ _xy ∈ pairBall k h r, 32 ^ (k + h - r) := by simp
    _ ≤ ∑ xy ∈ pairBall k h r, pairScore xy := by
      apply Finset.sum_le_sum
      intro xy hxy
      have hw : weight xy.1 + weight xy.2 < r := (Finset.mem_filter.mp hxy).2
      have hx := zeroCount_add_weight xy.1
      have hy := zeroCount_add_weight xy.2
      simp only [Fintype.card_fin] at hx hy
      rw [pairScore_eq]
      exact pow_le_pow_right' (by decide : (1 : ℕ) ≤ 32) (by omega)
    _ ≤ ∑ xy : Word k × Word h, pairScore xy :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 33 ^ (k + h) := pairScore_moment k h

/-- Only this 81/82-bit integer certificate is numerically normalized. -/
lemma small_certificate : (33 : ℕ) ^ 16 < 2 * 32 ^ 16 := by
  norm_num

/-- Symbolic powers only, including at t = 2^1528. -/
lemma grouped_power_bound (t : ℕ) :
    (33 : ℕ) ^ (576 * t) ≤ 2 ^ (41 * t) * 32 ^ (575 * t) := by
  have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
  calc
    (33 : ℕ) ^ (576 * t) = (33 ^ 16) ^ (36 * t) := by
      rw [← pow_mul]
      congr 1 <;> omega
    _ ≤ (2 * 32 ^ 16) ^ (36 * t) :=
      pow_le_pow_left' small_certificate.le _
    _ = 2 ^ (41 * t) * 32 ^ (575 * t) := by
      rw [h32]
      simp only [mul_pow, ← pow_mul, ← pow_add]
      congr 1 <;> omega

lemma two_pow_strictMono : StrictMono (fun n : ℕ => (2 : ℕ) ^ n) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp : 0 < (2 : ℕ) ^ n := by positivity
  rw [pow_succ]
  omega

/-- The weighted bound actually gives the stronger weak bound 2^(41t).
The final gap 41t < 64t supplies strictness, so powering the certificate
does not need a strict-power lemma. -/
theorem pairBall_card_lt (t : ℕ) (ht : 0 < t) :
    (pairBall (512 * t) (64 * t) t).card < 2 ^ (64 * t) := by
  have hw := pairBall_weighted_bound (512 * t) (64 * t) t
  have hsum : 512 * t + 64 * t = 576 * t := by omega
  have hsub : 512 * t + 64 * t - t = 575 * t := by omega
  rw [hsum] at hw
  have hsub' : 576 * t - t = 575 * t := by omega
  rw [hsub'] at hw
  have hg := grouped_power_bound t
  have hvol : (pairBall (512 * t) (64 * t) t).card ≤ 2 ^ (41 * t) := by
    exact Nat.le_of_mul_le_mul_right (hw.trans hg) (by positivity)
  exact hvol.trans_lt (two_pow_strictMono (by omega))

/-! ## Uniform fibers without explicitly evaluating 2^(h(k-1)) -/

theorem card_preimage_mul_card_of_surjective
    {M Y : Type*} [AddGroup M] [Fintype M] [AddGroup Y] [Fintype Y] [DecidableEq Y]
    (f : M →+ Y) (hf : Function.Surjective f) (s : Finset Y) :
    (Finset.univ.filter fun m => f m ∈ s).card * Fintype.card Y =
      Fintype.card M * s.card := by
  classical
  let q : ℕ := (Finset.univ.filter fun m : M => f m = 0).card
  have hfiber (y : Y) : (Finset.univ.filter fun m : M => f m = y).card = q := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf 0)
  have htotal : Fintype.card M = Fintype.card Y * q := by
    calc
      Fintype.card M =
          ∑ y : Y, (Finset.univ.filter fun m : M => f m = y).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset M)) (t := (Finset.univ : Finset Y))
          (f := f) (fun _ _ => Finset.mem_univ _))
      _ = Fintype.card Y * q := by simp only [hfiber, Finset.sum_const,
        Finset.card_univ, smul_eq_mul]
  have hpre : (Finset.univ.filter fun m => f m ∈ s).card = s.card * q := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ s f]
    simp only [hfiber, Finset.sum_const, smul_eq_mul]
  rw [hpre, htotal]
  ring

def evalHom {k h : ℕ} (x : Word k) : Mat k h →+ Word h where
  toFun A i := ∑ j, A i j * x j
  map_zero' := by ext i; simp
  map_add' A B := by ext i; simp [add_mul, Finset.sum_add_distrib]

/-- The same fixed-message evaluation is F₂-linear in the matrix. Counting
uses only its additive-hom projection. -/
def evalLinear {k h : ℕ} (x : Word k) : Mat k h →ₗ[F] Word h where
  toFun := evalHom x
  map_add' := (evalHom x).map_add
  map_smul' a A := by
    ext i
    simp [evalHom, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Pivot selection stays inside a proposition proof. No matrix-producing
definition uses classical choice. -/
theorem evalHom_surjective {k h : ℕ} (x : Word k) (hx : x ≠ 0) :
    Function.Surjective (evalHom (h := h) x) := by
  classical
  have hp : ∃ j, x j ≠ 0 := by
    by_contra! hp
    exact hx (funext hp)
  obtain ⟨j, hj⟩ := hp
  intro y
  refine ⟨fun i c => if c = j then y i * (x j)⁻¹ else 0, ?_⟩
  ext i
  simp [evalHom, ite_mul, mul_assoc, hj]

theorem evalLinear_surjective {k h : ℕ} (x : Word k) (hx : x ≠ 0) :
    Function.Surjective (evalLinear (h := h) x) := by
  change Function.Surjective (evalHom (h := h) x)
  exact evalHom_surjective x hx

theorem evalHom_uniform_fibers {k h : ℕ} (x : Word k) (hx : x ≠ 0)
    (y z : Word h) :
    (Finset.univ.filter fun A : Mat k h => evalHom x A = y).card =
      (Finset.univ.filter fun A : Mat k h => evalHom x A = z).card := by
  exact AddMonoidHom.card_fiber_eq_of_mem_range (evalHom (h := h) x)
    (evalHom_surjective x hx y) (evalHom_surjective x hx z)

lemma card_matrices (k h : ℕ) : Fintype.card (Mat k h) = 2 ^ (h * k) := by
  simp only [Mat, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul,
    Nat.mul_comm]

lemma pairBall_card_eq_sum (k h r : ℕ) :
    (pairBall k h r).card =
      ∑ x : Word k, (Finset.univ.filter fun y : Word h => weight x + weight y < r).card := by
  classical
  simp only [pairBall, Finset.card_filter, Fintype.sum_prod_type]

def badPairs (k h r : ℕ) : Finset (Mat k h × Word k) :=
  Finset.univ.filter fun Ax =>
    Ax.2 ≠ 0 ∧ weight Ax.2 + weight (evalHom Ax.2 Ax.1) < r

lemma badPairs_card_eq_sum (k h r : ℕ) :
    (badPairs k h r).card =
      ∑ x ∈ (Finset.univ.filter fun x : Word k => x ≠ 0),
        (Finset.univ.filter fun A : Mat k h =>
          weight x + weight (evalHom x A) < r).card := by
  classical
  simp only [badPairs, Finset.card_filter, Fintype.sum_prod_type_right,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ≠ 0 <;> simp [hx]

/-- Literal double-counting bound. This avoids a common explicit fiber size
Q by clearing the output-cardinality denominator before summing over x. -/
theorem badPairs_scaled_bound (k h r : ℕ) :
    (badPairs k h r).card * Fintype.card (Word h) ≤
      Fintype.card (Mat k h) * (pairBall k h r).card := by
  classical
  rw [badPairs_card_eq_sum, Finset.sum_mul]
  calc
    (∑ x ∈ (Finset.univ.filter fun x : Word k => x ≠ 0),
        (Finset.univ.filter fun A : Mat k h =>
          weight x + weight (evalHom x A) < r).card * Fintype.card (Word h)) =
        ∑ x ∈ (Finset.univ.filter fun x : Word k => x ≠ 0),
          Fintype.card (Mat k h) *
            (Finset.univ.filter fun y : Word h => weight x + weight y < r).card := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 : x ≠ 0 := (Finset.mem_filter.mp hx).2
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and]
        using card_preimage_mul_card_of_surjective (evalHom (h := h) x)
          (evalHom_surjective x hx0)
          (Finset.univ.filter fun y : Word h => weight x + weight y < r)
    _ ≤ ∑ x : Word k, Fintype.card (Mat k h) *
        (Finset.univ.filter fun y : Word h => weight x + weight y < r).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = Fintype.card (Mat k h) * (pairBall k h r).card := by
      rw [pairBall_card_eq_sum, Finset.mul_sum]

theorem badPairs_card_lt_matrices (k h r : ℕ)
    (hball : (pairBall k h r).card < Fintype.card (Word h)) :
    (badPairs k h r).card < Fintype.card (Mat k h) := by
  have hs := badPairs_scaled_bound k h r
  have hp : 0 < Fintype.card (Mat k h) := Fintype.card_pos
  have hprod : (badPairs k h r).card * Fintype.card (Word h) <
      Fintype.card (Mat k h) * Fintype.card (Word h) :=
    hs.trans_lt (Nat.mul_lt_mul_of_pos_left hball hp)
  by_contra! hnot
  exact (not_lt_of_ge (Nat.mul_le_mul_right _ hnot)) hprod

/-- Finite bad-matrix union bound, scaled to avoid division and common-fiber
dimension arithmetic. Every summand uses the SAME total matrix cardinality. -/
theorem systematic_matrix_exists (k h r : ℕ)
    (hball : (pairBall k h r).card < Fintype.card (Word h)) :
    ∃ A : Mat k h, ∀ x : Word k, x ≠ 0 →
      r ≤ weight x + weight (evalHom x A) := by
  classical
  let nonzero : Finset (Word k) := Finset.univ.filter fun x => x ≠ 0
  let badFor : Word k → Finset (Mat k h) := fun x =>
    Finset.univ.filter fun A => weight x + weight (evalHom x A) < r
  let lowOut : Word k → Finset (Word h) := fun x =>
    Finset.univ.filter fun y => weight x + weight y < r
  let bad : Finset (Mat k h) := nonzero.biUnion badFor
  have hscaled : bad.card * Fintype.card (Word h) ≤
      Fintype.card (Mat k h) * (pairBall k h r).card := by
    calc
      bad.card * Fintype.card (Word h) ≤
          (∑ x ∈ nonzero, (badFor x).card) * Fintype.card (Word h) :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ x ∈ nonzero, Fintype.card (Mat k h) * (lowOut x).card := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        have hx0 : x ≠ 0 := (Finset.mem_filter.mp hx).2
        simpa only [badFor, lowOut, Finset.mem_filter, Finset.mem_univ, true_and]
          using card_preimage_mul_card_of_surjective (evalHom (h := h) x)
            (evalHom_surjective x hx0) (lowOut x)
      _ = Fintype.card (Mat k h) * (∑ x ∈ nonzero, (lowOut x).card) := by
        rw [Finset.mul_sum]
      _ ≤ Fintype.card (Mat k h) * (∑ x : Word k, (lowOut x).card) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      _ = Fintype.card (Mat k h) * (pairBall k h r).card := by
        rw [pairBall_card_eq_sum]
  have hmpos : 0 < Fintype.card (Mat k h) := Fintype.card_pos
  have hbad : bad.card < (Finset.univ : Finset (Mat k h)).card := by
    rw [Finset.card_univ]
    have hprodlt : bad.card * Fintype.card (Word h) <
        Fintype.card (Mat k h) * Fintype.card (Word h) :=
      hscaled.trans_lt (Nat.mul_lt_mul_of_pos_left hball hmpos)
    by_contra! hnot
    exact (not_lt_of_ge (Nat.mul_le_mul_right _ hnot)) hprodlt
  obtain ⟨A, _hA, hAgood⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  refine ⟨A, ?_⟩
  intro x hx
  by_contra! hsmall
  apply hAgood
  apply Finset.mem_biUnion.mpr
  exact ⟨x, by simp [nonzero, hx], by simp [badFor, hsmall]⟩

/-- Closed semantic finite-existence target for the fixed local code.
No exhaustive matrix enumeration is evaluated or normalized. -/
theorem local_systematic_matrix_exists (t : ℕ) (ht : 0 < t) :
    ∃ A : Mat (512 * t) (64 * t), ∀ x : Word (512 * t), x ≠ 0 →
      t ≤ weight x + weight (evalHom x A) := by
  apply systematic_matrix_exists
  simpa only [Word, Fintype.card_fun, Fintype.card_fin, ZMod.card]
    using pairBall_card_lt t ht

/-! ## The actual systematic F₂-linear map -/

def parityLinear {k h : ℕ} (A : Mat k h) : Word k →ₗ[F] Word h where
  toFun x := evalHom x A
  map_add' x y := by
    ext i
    simp [evalHom, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp [evalHom, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc, mul_left_comm]

def systematicLinear {k h : ℕ} (A : Mat k h) :
    Word k →ₗ[F] ((Fin k ⊕ Fin h) → F) where
  toFun x := Sum.elim x (parityLinear A x)
  map_add' x y := by
    ext i
    cases i <;> simp
  map_smul' a x := by
    ext i
    cases i <;> simp

@[simp] lemma systematicLinear_left {k h : ℕ} (A : Mat k h) (x : Word k)
    (i : Fin k) : systematicLinear A x (Sum.inl i) = x i := rfl

lemma weight_sumElim {k h : ℕ} (x : Word k) (y : Word h) :
    weight (Sum.elim x y) = weight x + weight y := by
  classical
  simp only [weight, Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]

theorem local_systematic_linear_code_exists (t : ℕ) (ht : 0 < t) :
    ∃ A : Mat (512 * t) (64 * t), ∀ x : Word (512 * t), x ≠ 0 →
      t ≤ weight (systematicLinear A x) := by
  obtain ⟨A, hA⟩ := local_systematic_matrix_exists t ht
  refine ⟨A, fun x hx => ?_⟩
  change t ≤ weight (Sum.elim x (evalHom x A))
  rw [weight_sumElim]
  exact hA x hx

/-- The huge constant is never evaluated: this is just equality of exponents. -/
lemma fixed_degree_reparametrization :
    (16 : ℕ) ^ 384 = 256 * 2 ^ 1528 := by
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
  rw [h16, h256, ← pow_mul, ← pow_add]

theorem fixed_local_systematic_matrix_exists :
    ∃ A : Mat (512 * 2 ^ 1528) (64 * 2 ^ 1528),
      ∀ x : Word (512 * 2 ^ 1528), x ≠ 0 →
        2 ^ 1528 ≤ weight (evalHom x A) + weight x := by
  simpa only [Nat.add_comm] using
    local_systematic_matrix_exists (2 ^ 1528) (by positivity)

end FiniteLocalCountingCandidate
