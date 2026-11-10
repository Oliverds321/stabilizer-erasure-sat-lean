/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
The explicit port-word power of the target-checked lazy MGG graph.
-/
import QecReliability.MGGPortGraph
import QecReliability.PortPowerCandidate

open scoped BigOperators

namespace QecReliability.ExpanderWalk

/-- Computable 384-step graph. The degree is retained symbolically. -/
def poweredMGGPortGraph (s : ℕ) (hs : 3 ≤ s) : PortGraph (s * s) (16 ^ 384) :=
  (lazyMGGPortGraph s hs).power 384

theorem poweredMGGPortGraph_neighbor (s : ℕ) (hs : 3 ≤ s)
    (v : Fin (s * s)) (i : Fin (16 ^ 384)) :
    (poweredMGGPortGraph s hs).neighbor v i =
      (lazyMGGPortGraph s hs).walkEnd 384 v (PortGraph.portWordEquiv 16 384 i) :=
  (lazyMGGPortGraph s hs).power_neighbor 384 v i

theorem poweredMGGPortGraph_transition (s : ℕ) (hs : 3 ≤ s)
    (f : RVec (s * s)) :
    (poweredMGGPortGraph s hs).transition f =
      (lazyMGGPortGraph s hs).transitionPow 384 f :=
  (lazyMGGPortGraph s hs).power_transition 384 f

/-- The bound is derived from the actual lazy MGG theorem, with no spectral
assumption supplied by the caller. -/
theorem poweredMGGPortGraph_centered (s : ℕ) (hs : 3 ≤ s)
    (f : RVec (s * s)) (hf : (∑ i, f i) = 0) :
    dot f ((poweredMGGPortGraph s hs).transition f) ≤
      (1 / 4096 : ℝ) * energy f :=
  (lazyMGGPortGraph s hs).power384_centered (lazyMGGPortGraph_positiveGap s hs) f hf

theorem poweredMGGPortGraph_positiveGap (s : ℕ) (hs : 3 ≤ s) :
    (poweredMGGPortGraph s hs).PositiveGap (4095 / 4096) :=
  (lazyMGGPortGraph s hs).power384_positiveGap (lazyMGGPortGraph_positiveGap s hs)

/-- The computable square-size family retains its order under powering. -/
def poweredSquarePortGraph (L : ℕ) (hL : 8 ≤ L) :
    PortGraph (QuantumExpander.squareSide L * QuantumExpander.squareSide L) (16 ^ 384) :=
  (squarePortGraph L hL).power 384

theorem poweredSquarePortGraph_spec (L : ℕ) (hL : 8 ≤ L) :
    L ≤ QuantumExpander.squareSide L * QuantumExpander.squareSide L ∧
    QuantumExpander.squareSide L * QuantumExpander.squareSide L < 2 * L ∧
    (poweredSquarePortGraph L hL).PositiveGap (4095 / 4096) := by
  obtain ⟨hcover, hsize, hgap⟩ := squarePortGraph_spec L hL
  exact ⟨hcover, hsize, (squarePortGraph L hL).power384_positiveGap hgap⟩

def poweredShiftedSquarePortGraph (b : ℕ) (hb : 4 ≤ b) (L : ℕ) (hL : 2 * b ≤ L) :
    PortGraph (QuantumExpander.squareSide L * QuantumExpander.squareSide L) (16 ^ 384) :=
  poweredSquarePortGraph L (by omega)

theorem poweredShiftedSquarePortGraph_spec
    (b : ℕ) (hb : 4 ≤ b) (L : ℕ) (hL : 2 * b ≤ L) :
    L ≤ QuantumExpander.squareSide L * QuantumExpander.squareSide L ∧
    QuantumExpander.squareSide L * QuantumExpander.squareSide L < 2 * L ∧
    (poweredShiftedSquarePortGraph b hb L hL).PositiveGap (4095 / 4096) :=
  poweredSquarePortGraph_spec L (by omega)

end QecReliability.ExpanderWalk
