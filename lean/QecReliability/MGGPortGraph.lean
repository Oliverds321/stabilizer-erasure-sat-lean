/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
Adapter from the girving/aks MGG rotation and proved Rayleigh bound
to the existing quantum project's exact PortGraph and half-lazy construction.
-/
import AKS.MGG.Factory
import QecReliability.LazyPortGraphCore

open scoped BigOperators

namespace QecReliability.ExpanderWalk

/-- The eight-port MGG graph, with its actual involutive rotation. -/
def mggPortGraph (s : ℕ) (hs : 3 ≤ s) : PortGraph (s * s) 8 where
  vertices_pos := Nat.mul_pos (by omega) (by omega)
  degree_pos := by decide
  rotation := (mgg s).rotEquiv
  reverse_reverse := (mgg s).rot_involution

theorem mggPortGraph_neighbor (s : ℕ) (hs : 3 ≤ s)
    (v : Fin (s * s)) (i : Fin 8) :
    (mggPortGraph s hs).neighbor v i = (mgg s).neighbor v i := rfl

theorem mggPortGraph_transition (s : ℕ) (hs : 3 ≤ s)
    (f : RVec (s * s)) (v : Fin (s * s)) :
    (mggPortGraph s hs).transition f v =
      (∑ i : Fin 8, f ((mgg s).neighbor v i)) / 8 := rfl

/-- The existing project's upper-Rayleigh premise is a proved consequence of
the imported theorem, with no spectral premise supplied by the caller. -/
theorem mggPortGraph_upper (s : ℕ) (hs : 3 ≤ s)
    (f : RVec (s * s)) (hzero : ∑ v, f v = 0) :
    dot f ((mggPortGraph s hs).transition f) ≤ (15 / 16 : ℝ) * energy f := by
  simpa only [dot, energy, mggPortGraph_transition, pow_two] using
    QuantumExpander.mgg_upper_rayleigh s hs f hzero

/-- The original half-lazy construction has exactly sixteen ports. -/
def lazyMGGPortGraph (s : ℕ) (hs : 3 ≤ s) : PortGraph (s * s) 16 :=
  (mggPortGraph s hs).lazyGraph

theorem lazyMGGPortGraph_positiveGap (s : ℕ) (hs : 3 ≤ s) :
    (lazyMGGPortGraph s hs).PositiveGap (1 / 32) := by
  have h := (mggPortGraph s hs).lazy_positiveGap
    (by norm_num : (0 : ℝ) ≤ 15 / 16)
    (by norm_num : (15 / 16 : ℝ) < 1)
    (mggPortGraph_upper s hs)
  norm_num at h
  exact h

/-- The first eight ports retain the MGG edges with their multiplicities. -/
theorem lazyMGGPortGraph_neighbor_left (s : ℕ) (hs : 3 ≤ s)
    (v : Fin (s * s)) (i : Fin 8) :
    (lazyMGGPortGraph s hs).neighbor v (Fin.castAdd 8 i) =
      (mgg s).neighbor v i :=
  (mggPortGraph s hs).lazy_neighbor_left v i

/-- The other eight ports hold at the current vertex. -/
theorem lazyMGGPortGraph_neighbor_right (s : ℕ) (hs : 3 ≤ s)
    (v : Fin (s * s)) (i : Fin 8) :
    (lazyMGGPortGraph s hs).neighbor v (Fin.natAdd 8 i) = v :=
  (mggPortGraph s hs).lazy_neighbor_right v i

/-- A computable square-order graph family in the project's original type. -/
def squarePortGraph (L : ℕ) (hL : 8 ≤ L) :
    PortGraph (QuantumExpander.squareSide L * QuantumExpander.squareSide L) 16 :=
  lazyMGGPortGraph (QuantumExpander.squareSide L)
    (QuantumExpander.squareSide_ge_three L hL)

theorem squarePortGraph_spec (L : ℕ) (hL : 8 ≤ L) :
    L ≤ QuantumExpander.squareSide L * QuantumExpander.squareSide L ∧
    QuantumExpander.squareSide L * QuantumExpander.squareSide L < 2 * L ∧
    (squarePortGraph L hL).PositiveGap (1 / 32) := by
  exact ⟨QuantumExpander.squareSide_covers L (by omega),
    QuantumExpander.squareSide_lt_twice L hL,
    lazyMGGPortGraph_positiveGap _ _⟩

/-- Shifting the supplied base ensures the modulus premise uniformly. -/
def shiftedSquarePortGraph (b : ℕ) (hb : 4 ≤ b) (L : ℕ) (hL : 2 * b ≤ L) :
    PortGraph (QuantumExpander.squareSide L * QuantumExpander.squareSide L) 16 :=
  squarePortGraph L (by omega)

theorem shiftedSquarePortGraph_spec (b : ℕ) (hb : 4 ≤ b) (L : ℕ) (hL : 2 * b ≤ L) :
    L ≤ QuantumExpander.squareSide L * QuantumExpander.squareSide L ∧
    QuantumExpander.squareSide L * QuantumExpander.squareSide L < 2 * L ∧
    (shiftedSquarePortGraph b hb L hL).PositiveGap (1 / 32) :=
  squarePortGraph_spec L (by omega)

end QecReliability.ExpanderWalk
