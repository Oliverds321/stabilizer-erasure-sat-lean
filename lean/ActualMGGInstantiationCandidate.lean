import ZeroDispatchCandidate
import QecReliability.MGGPortGraph

/-!
`QecReliability.MGGPortGraph` is the exact
imported module, not an assumed expander.

Do not import two copies of LazyPortGraph definitions into the same environment:
use the LazyPortGraphCore-compatible import arrangement.
-/
namespace QecReliability.UniformAdapter
open ExpanderWalk

def actualMGG : MGGInput where
  graph := lazyMGGPortGraph
  gap := lazyMGGPortGraph_positiveGap

noncomputable def buildActualWalkCode (F : DyadicXorData) (q : ℕ) : WalkCode q :=
  buildWalkCode F actualMGG q

noncomputable def buildActualWalkCircuits (F : DyadicXorData) (q : ℕ) :
    (buildActualWalkCode F q).Circuits := buildWalkCircuits F actualMGG q

/-- The remaining encoder premise is visible, not renamed as a SAT-only theorem. -/
theorem buildActual_gate_bound (F : DyadicXorData) (q : ℕ) :
    (buildActualWalkCircuits F q).gateBudget ≤ F.shift.Cfixed*(q+1) :=
  F.shift.gates_all_lengths F.shift_base_ge_eight actualMGG q

end QecReliability.UniformAdapter
