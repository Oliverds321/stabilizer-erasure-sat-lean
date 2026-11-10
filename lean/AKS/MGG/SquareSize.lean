/- Copyright (c) 2026. Released under Apache 2.0; see LICENSE. -/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

namespace QuantumExpander

/-- Integer ceiling square root, for positive lengths. -/
def squareSide (L : ℕ) : ℕ := Nat.sqrt (L - 1) + 1

theorem squareSide_predecessor_sq_lt (L : ℕ) (hL : 0 < L) :
    (squareSide L - 1) ^ 2 < L := by
  have h := Nat.sqrt_le' (L - 1)
  simp only [squareSide, Nat.add_sub_cancel]
  omega

theorem squareSide_covers (L : ℕ) (hL : 0 < L) :
    L ≤ squareSide L * squareSide L := by
  have h := Nat.lt_succ_sqrt (L - 1)
  simp only [Nat.succ_eq_add_one] at h
  unfold squareSide
  omega

theorem squareSide_ge_three (L : ℕ) (hL : 8 ≤ L) :
    3 ≤ squareSide L := by
  have h : 2 ≤ Nat.sqrt (L - 1) := Nat.le_sqrt.mpr (by omega)
  unfold squareSide
  omega

theorem squareSide_lt_twice (L : ℕ) (hL : 8 ≤ L) :
    squareSide L * squareSide L < 2 * L := by
  have hlo := Nat.sqrt_le (L - 1)
  have hs := squareSide_ge_three L hL
  unfold squareSide at *
  have hsub : L - 1 + 1 = L := Nat.sub_add_cancel (by omega)
  by_cases hsmall : Nat.sqrt (L - 1) = 2
  · simp only [hsmall]
    omega
  · have hlarge : 3 ≤ Nat.sqrt (L - 1) := by omega
    nlinarith [Nat.mul_le_mul_right (Nat.sqrt (L - 1) + 1) hlarge]

theorem shifted_base_ge_eight (b : ℕ) (hb : 4 ≤ b) : 8 ≤ 2 * b := by omega

end QuantumExpander
