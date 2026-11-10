/- Copyright (c) 2026. Released under Apache 2.0; see LICENSE. -/
import AKS.MGG.Adapter
import AKS.MGG.SquareSize

open BigOperators

namespace QuantumExpander

/-- A uniform, computable graph family with square order. This is graph data,
not a hash family and not an encoder-efficiency assumption. -/
def squareMGG (L : ℕ) : RegularGraph (squareSide L * squareSide L) 8 :=
  mgg (squareSide L)

theorem squareMGG_vertex_bounds (L : ℕ) (hL : 8 ≤ L) :
    L ≤ squareSide L * squareSide L ∧ squareSide L * squareSide L < 2 * L :=
  ⟨squareSide_covers L (by omega), squareSide_lt_twice L hL⟩

theorem squareMGG_upper_rayleigh (L : ℕ) (hL : 8 ≤ L)
    (f : Fin (squareSide L * squareSide L) → ℝ) (hzero : ∑ v, f v = 0) :
    (∑ v, f v * ((∑ i : Fin 8, f ((squareMGG L).neighbor v i)) / 8)) ≤
      (15 / 16 : ℝ) * ∑ v, (f v) ^ 2 :=
  mgg_upper_rayleigh (squareSide L) (squareSide_ge_three L hL) f hzero

/-- Doubling a supplied base of at least four guarantees the MGG modulus
premise at every length above the shifted base. -/
theorem shifted_length_modulus (b L : ℕ) (hb : 4 ≤ b) (hL : 2 * b ≤ L) :
    3 ≤ squareSide L :=
  squareSide_ge_three L (by omega)

end QuantumExpander
