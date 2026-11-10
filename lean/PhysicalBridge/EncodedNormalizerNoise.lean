import PhysicalBridge.UniformLogicalNoise

/-! The logical representation is tied to an actual encoded physical channel,
by an exact factorization derived from the intertwining identity. -/
noncomputable section
namespace QecPhysical.Stabilizer.Lift
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)
variable {τ : Type*} [Fintype τ]

theorem encodedNormalizer_factorization (e : τ → Normalizer S) (p : τ → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hsum : ∑ t, p t=1) :
    (L.encodedPauliChannel (fun t => (e t).val) p hp hsum).map =
      L.encodingChannel.map.comp (mixtureMap p (fun t => conjugateMap (L.logicalOp (e t)))) := by
  change mixtureMap p (fun t => conjugateMap (pauli (e t).val * L.encoding)) =
    (conjugateMap L.encoding).comp (mixtureMap p (fun t => conjugateMap (L.logicalOp (e t))))
  rw [comp_mixtureMap]
  congr 1
  funext t
  rw [conjugateMap_comp, L.logicalOp_intertwine]

end QecPhysical.Stabilizer.Lift
