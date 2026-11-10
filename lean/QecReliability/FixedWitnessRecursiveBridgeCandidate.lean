import QecReliability.FixedWitnessSparseAmplifierCandidate
import QecReliability.RecursiveEncoderDistanceCandidate

/-!


Concrete graph/padding bindings for ONE supplied local packed certificate.
No spectral, local-distance, GoodCode, or EfficientFactory premise remains.
The THREE exact compiler equalities remain explicit.
This file does NOT turn those
obligations into a claim of an unconditional finite encoder generator.
-/

set_option autoImplicit false
noncomputable section

namespace QecReliability.SharedCircuit.FixedWitnessEncoder
open scoped BigOperators
open CodeHash EncoderSemantics SerializedDyadicEncoder
open FiniteLocalSelectorCandidate
open ExpanderWalk.FixedWitnessSparseAmplifier

/-- Fixed-degree facts are proofs, not a closed data initialization. -/
theorem degree_pos {D : Nat} (hD : D = 16 ^ 384) : 0 < D :=
  hD.symm ▸ ExpanderWalk.SelectedSparseAmplifier.fixed_degree_pos

theorem degree_four {D : Nat} (hD : D = 16 ^ 384) : 4 ∣ D :=
  hD.symm ▸ ExpanderWalk.SelectedSparseAmplifier.fixed_degree_four_dvd

/-- Actual powered MGG square, with both capacities already derived. -/
def paddedSource (D : Nat) (hD : D = 16 ^ 384) (T out : Nat)
    (hdiv : D ∣ T) (hlarge : 8 * D ≤ T) (hout : T / 2 = out) :
    PaddedSource D T out where
  vertices := QuantumExpander.squareSide (T / D) * QuantumExpander.squareSide (T / D)
  graph := ExpanderWalk.SelectedSparseAmplifier.graph D hD T hdiv hlarge
  input_capacity := (ExpanderWalk.SelectedSparseAmplifier.graph_capacity D hD T hdiv hlarge).1
  output_capacity := (ExpanderWalk.SelectedSparseAmplifier.graph_capacity D hD T hdiv hlarge).2
  output_eq := hout

theorem paddedSource_centered (D : Nat) (hD : D = 16 ^ 384) (T out : Nat)
    (hdiv : D ∣ T) (hlarge : 8 * D ≤ T) (hout : T / 2 = out)
    (f : ExpanderWalk.RVec (paddedSource D hD T out hdiv hlarge hout).vertices)
    (hf : (∑ v, f v) = 0) :
    ExpanderWalk.dot f ((paddedSource D hD T out hdiv hlarge hout).graph.transition f) ≤
      (1 / 4096 : ℝ) * ExpanderWalk.energy f :=
  ExpanderWalk.SelectedSparseAmplifier.graph_centered D hD T hdiv hlarge f hf

set_option maxRecDepth 4096 in
/-- Exact equality with the generic same-certificate amplifier, after only the
output-dimension cast used by the recursive encoder interface. -/
theorem paddedSource_linear {D t : Nat} (hD : D = 16 ^ 384)
    (hd : D = 256 * t) (A : CertifiedParity (512 * t) (64 * t) t)
    (T out : Nat) (hdiv : D ∣ T) (hlarge : 8 * D ≤ T) (hout : T / 2 = out) :
    (paddedSource D hD T out hdiv hlarge hout).linear (parityForDegree hd A) =
      (castWord hout).comp (amplifier D t hD hd A T hdiv hlarge) := rfl

/-- R1 always has at least 32D inputs, so its square graph is admissible. -/
def firstSource (D : Nat) (hD : D = 16 ^ 384) (ell : Nat) :
    PaddedSource D (2 * messageWidth D ell) (messageWidth D ell) :=
  paddedSource D hD (2 * messageWidth D ell) (messageWidth D ell)
    (amplifier_dimensions D ell).1
    (by have h := messageWidth_ge_base D ell; omega)
    (by omega)

/-- R2 always has at least 64D inputs. It uses the SAME local certificate. -/
def secondSource (D : Nat) (hD : D = 16 ^ 384) (ell : Nat) :
    PaddedSource D (4 * messageWidth D ell) (2 * messageWidth D ell) :=
  paddedSource D hD (4 * messageWidth D ell) (2 * messageWidth D ell)
    (amplifier_dimensions D ell).2.1
    (by have h := messageWidth_ge_base D ell; omega)
    (by omega)

theorem firstSource_centered (D : Nat) (hD : D = 16 ^ 384) (ell : Nat)
    (f : ExpanderWalk.RVec (firstSource D hD ell).vertices) (hf : (∑ v, f v) = 0) :
    ExpanderWalk.dot f ((firstSource D hD ell).graph.transition f) ≤
      (1 / 4096 : ℝ) * ExpanderWalk.energy f :=
  paddedSource_centered D hD (2 * messageWidth D ell) (messageWidth D ell)
    (amplifier_dimensions D ell).1
    (by have h := messageWidth_ge_base D ell; omega) (by omega) f hf

theorem secondSource_centered (D : Nat) (hD : D = 16 ^ 384) (ell : Nat)
    (f : ExpanderWalk.RVec (secondSource D hD ell).vertices) (hf : (∑ v, f v) = 0) :
    ExpanderWalk.dot f ((secondSource D hD ell).graph.transition f) ≤
      (1 / 4096 : ℝ) * ExpanderWalk.energy f :=
  paddedSource_centered D hD (4 * messageWidth D ell) (2 * messageWidth D ell)
    (amplifier_dimensions D ell).2.1
    (by have h := messageWidth_ge_base D ell; omega) (by omega) f hf

variable {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
  (A : CertifiedParity (512 * t) (64 * t) t)
  (base : XorProgram (messageWidth D 0) (4 * messageWidth D 0))
  (R₁ : (ell : Nat) → XorProgram (2 * messageWidth D ell) (messageWidth D ell))
  (R₂ : (ell : Nat) → XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell))

/-- The remaining hypotheses are literal local compiler bindings, not desired
recursive distance. The one-copy encoder and its wire ordering are unchanged. -/
theorem encoder_distance_from_certificate
    (hbase : base.toLinear = baseForEncoder (degree_four hD) (parityForDegree hd A))
    (hcompile₁ : ∀ ell, (R₁ ell).toLinear = (firstSource D hD ell).linear (parityForDegree hd A))
    (hcompile₂ : ∀ ell, (R₂ ell).toLinear = (secondSource D hD ell).linear (parityForDegree hd A))
    (ell : Nat) (x : Word (messageWidth D ell)) (hx : x ≠ 0) :
    alpha * (((64 * D) * 2 ^ ell : Nat) : ℝ) ≤
      (weight ((encoder base R₁ R₂ ell).toLinear x) : ℝ) := by
  exact encoder_distance_from_local_and_padded base R₁ R₂
    (degree_pos hD) (degree_four hD) (parityForDegree hd A)
    (parityForDegree_local hd A) hbase
    (firstSource D hD) (secondSource D hD) hcompile₁ hcompile₂
    (firstSource_centered D hD) (secondSource_centered D hD) ell x hx

/-- The SAME exact-size program used by the all-length adapter. -/
theorem exactEncoder_distance_from_certificate
    (hbase : base.toLinear = baseForEncoder (degree_four hD) (parityForDegree hd A))
    (hcompile₁ : ∀ ell, (R₁ ell).toLinear = (firstSource D hD ell).linear (parityForDegree hd A))
    (hcompile₂ : ∀ ell, (R₂ ell).toLinear = (secondSource D hD ell).linear (parityForDegree hd A))
    (ell : Nat) (x : Word (((64 * D) * 2 ^ ell) / 4)) (hx : x ≠ 0) :
    alpha * (((64 * D) * 2 ^ ell : Nat) : ℝ) ≤
      (weight ((exactEncoder base R₁ R₂ ell).toLinear x) : ℝ) := by
  apply exactEncoder_distance base R₁ R₂ (degree_pos hD)
  · intro z hz
    rw [hbase]
    exact baseForEncoder_distance (degree_four hD) (parityForDegree hd A)
      (parityForDegree_local hd A) z hz
  · intro j
    exact sparseSpec_of_padded (R₁ j) (firstSource D hD j) (parityForDegree hd A)
      (hcompile₁ j) (parityForDegree_local hd A) (firstSource_centered D hD j)
  · intro j
    exact sparseSpec_of_padded (R₂ j) (secondSource D hD j) (parityForDegree hd A)
      (hcompile₂ j) (parityForDegree_local hd A) (secondSource_centered D hD j)
  · exact hx

/-- No new semantic encoder is inserted between certificate and exact program. -/
theorem exactEncoder_injective_from_certificate
    (hbase : base.toLinear = baseForEncoder (degree_four hD) (parityForDegree hd A))
    (ell : Nat) : Function.Injective (exactEncoder base R₁ R₂ ell).toLinear :=
  exactEncoder_injective_from_localBase base R₁ R₂
    (degree_four hD) (parityForDegree hd A) hbase ell

/-- The semantic bridge does not alter the one-copy gate recurrence. -/
theorem same_encoder_gates (ell : Nat) :
    (encoder base R₁ R₂ (ell + 1)).gates =
      (R₁ ell).gates + (encoder base R₁ R₂ ell).gates + (R₂ ell).gates :=
  encoder_step_gates base R₁ R₂ ell

end QecReliability.SharedCircuit.FixedWitnessEncoder
