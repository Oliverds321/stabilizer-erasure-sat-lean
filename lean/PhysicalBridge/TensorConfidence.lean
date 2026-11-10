import PhysicalBridge.MultivariateReliability
import QecReliability.TensorCoefficientCounting

/-! The multiclass counting event implies uniform physical two-tail accuracy
after exact-corner shape repair. The explicit counting/hash interface remains
visible here; concrete machine instantiation is a separate obligation. -/
set_option autoImplicit false
noncomputable section

namespace QecPhysical.Stabilizer.Lift
open QecReliability QecReliability.Binary
open QecReliability.TensorBernstein QecReliability.TensorLatent
open QecReliability.TensorCoefficientCounting

variable {n : ℕ} {ds : List ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

/-- Physical accuracy is simultaneous in all Bernoulli parameters, on both
the fidelity and infidelity scale. -/
def TensorPhysicalAccuracy (C : CausesGrid ds → Finset (Fin n))
    (ε : ℝ) (g : Params ds → ℝ) : Prop :=
  ∀ p (hp : cube ds p), RelPair ε
    (entanglementFidelity
      (L.erasureFlagDecoder.comp (L.multivariateLatentErasure C p hp)).map) (g p)

/-- Deterministic shape and exact physical corners hold for every estimate
table. Only the accuracy assertion requires a successful counting event. -/
def TensorPhysicalStructure (C : CausesGrid ds → Finset (Fin n))
    (g : Params ds → ℝ) : Prop :=
  AntitoneOn g {p | cube ds p} ∧
  (∀ p, cube ds p → 0 ≤ g p ∧ g p ≤ 1) ∧
  ∀ b : Corner ds, g (cornerParams ds b) =
    entanglementFidelity
      (L.erasureFlagDecoder.comp (L.multivariateLatentErasure C (cornerParams ds b)
        (cornerParams_mem_cube ds b))).map

theorem physicalCornerRepairedCurve_structure
    (C : CausesGrid ds → Finset (Fin n)) (hC : Monotone C)
    (est : Grid ds → ℝ) :
    L.TensorPhysicalStructure C (physicalCornerRepairedCurve S C est) := by
  obtain ⟨hanti, hrange⟩ := physicalCornerRepairedCurve_shape C est
  exact ⟨hanti, hrange, L.physicalCornerRepairedCurve_corner C hC est⟩

/-- One finite-seed event controls every tensor coefficient and therefore
every physical parameter, without a second union bound or failure allowance. -/
theorem tensor_counting_physical_confidence
    {Ω : Type*} [Fintype Ω] (C : CausesGrid ds → Finset (Fin n))
    (hC : Monotone C) (H : HashStages Ω (Key n ds) (SharedCircuit.LatentEncoding.keySize n ds.sum))
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i))
    (B m : ℕ) (hB : 0 < B) {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hcell : 16 ≤ (ε/3)^2*(B:ℝ))
    (hrepeat : (Fintype.card (Index ds):ℝ)*(1/2:ℝ)^(m+2) ≤ δ) :
    (∀ ω, L.TensorPhysicalStructure C
      (physicalCornerRepairedCurve S C (estimates O B m ω))) ∧
    1-δ ≤ (repeatedLaw H.law m).prob (fun ω =>
      L.TensorPhysicalAccuracy C ε
        (physicalCornerRepairedCurve S C (estimates O B m ω))) := by
  refine ⟨fun ω => L.physicalCornerRepairedCurve_structure C hC _, ?_⟩
  apply (coefficients_confidence S L.isotropic C H O B m hB hε hε1 hcell hrepeat).trans
  apply FiniteProbability.prob_mono
  intro ω hω
  exact L.physicalCornerRepairedCurve_relPair C hC _ hε.le hε1 (fun j => (hω j).1)

end QecPhysical.Stabilizer.Lift
