import QecReliability.FixedLocalAmplifierEmitterCandidate

/-!


Close all three LOCAL COMPILER equalities with the actual programs just defined.
The recursive circuit is the existing exactEncoder, not a newly assumed family.
One supplied finite table is reused at every recursion level. The final theorem
introduces that table once outside every length. No caller GoodCode, spectral,
local-distance, or compiler-correctness hypothesis remains.

This is circuit-level existence and correctness, NOT a finite-machine generation
or bit-runtime theorem. The concrete graph/source specialization uses the existing computable Nat
arithmetic/radix definitions. Their finite-machine cost refinement is still
separate; computability is not a polynomial physical-runtime certificate.
-/

set_option autoImplicit false
namespace QecReliability.SharedCircuit.FixedLocalEmitter
open scoped BigOperators
open CodeHash EncoderSemantics SerializedDyadicEncoder
open FiniteLocalSelectorCandidate
open ExpanderWalk.FixedWitnessSparseAmplifier

/-- Exactly the one-copy constructor, with all its local inputs built. -/
def concreteEncoder {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    XorProgram (messageWidth D ell) (4 * messageWidth D ell) :=
  encoder (baseProgram (FixedWitnessEncoder.degree_four hD) hd A)
    (firstProgram hD hd A) (secondProgram hD hd A) ell

/-- Exact dyadic shape expected by the all-length adapter. -/
def concreteExactEncoder {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    XorProgram (((64 * D) * 2 ^ ell) / 4) ((64 * D) * 2 ^ ell) :=
  exactEncoder (baseProgram (FixedWitnessEncoder.degree_four hD) hd A)
    (firstProgram hD hd A) (secondProgram hD hd A) ell

/-- All previously explicit compiler equalities are now proved by the emitters. -/
theorem concreteExactEncoder_distance {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t)
    (ell : Nat) (x : Word (((64 * D) * 2 ^ ell) / 4)) (hx : x ≠ 0) :
    alpha * (((64 * D) * 2 ^ ell : Nat) : ℝ) ≤
      (weight ((concreteExactEncoder hD hd A ell).toLinear x) : ℝ) := by
  exact FixedWitnessEncoder.exactEncoder_distance_from_certificate hD hd A
    (baseProgram (FixedWitnessEncoder.degree_four hD) hd A)
    (firstProgram hD hd A) (secondProgram hD hd A)
    (baseProgram_linear _ hd A) (firstProgram_linear hD hd A) (secondProgram_linear hD hd A)
    ell x hx

theorem concreteExactEncoder_injective {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    Function.Injective (concreteExactEncoder hD hd A ell).toLinear :=
  FixedWitnessEncoder.exactEncoder_injective_from_certificate hD hd A
    (baseProgram (FixedWitnessEncoder.degree_four hD) hd A)
    (firstProgram hD hd A) (secondProgram hD hd A)
    (baseProgram_linear _ hd A) ell

theorem concreteExactEncoder_gates {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    (concreteExactEncoder hD hd A ell).gates ≤ 2 * D * ((64 * D) * 2 ^ ell) := by
  have hb := baseProgram_gates (FixedWitnessEncoder.degree_four hD) hd A
  have hg := encoder_gates_le (FixedWitnessEncoder.degree_pos hD)
    (baseProgram (FixedWitnessEncoder.degree_four hD) hd A)
    (firstProgram hD hd A) (secondProgram hD hd A)
    (le_of_eq hb) (firstProgram_gates_le hD hd A) (secondProgram_gates_le hD hd A) ell
  simpa only [concreteExactEncoder, exactEncoder_gates, codeLength_formula] using hg

/-- Literal finite valid payload with bounded gate and output reference tables. -/
theorem concreteExactEncoder_serialized {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    (concreteExactEncoder hD hd A ell).serialize.Valid ∧
    (concreteExactEncoder hD hd A ell).serialize.gates.length ≤
      2 * D * ((64 * D) * 2 ^ ell) ∧
    (concreteExactEncoder hD hd A ell).serialize.outputs.length = (64 * D) * 2 ^ ell := by
  let P := concreteExactEncoder hD hd A ell
  refine ⟨⟨XorProgram.serialize_topological P, ?_⟩, ?_, ?_⟩
  · intro v hv
    have h := XorProgram.serialize_output_bound P v hv
    simpa only [XorProgram.serialize, XorCircuit.erase_length] using h
  · simpa only [XorProgram.serialize, XorCircuit.erase_length] using
      concreteExactEncoder_gates hD hd A ell
  · simp only [XorProgram.serialize, List.length_ofFn]

/-- Symbolic dimensions keep existential elimination independent of closed huge numerals. -/
theorem exists_one_certificate_all_concrete_encoders_generic
    {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t) (ht : 0 < t) :
    ∃ A : CertifiedParity (512 * t) (64 * t) t,
      ∀ ell : Nat,
        let P := concreteExactEncoder hD hd A ell
        P.gates ≤ 2 * D * ((64 * D) * 2 ^ ell) ∧
        Function.Injective P.toLinear ∧
        ∀ x : Word (((64 * D) * 2 ^ ell) / 4), x ≠ 0 →
          alpha * (((64 * D) * 2 ^ ell : Nat) : ℝ) ≤
            (weight (P.toLinear x) : ℝ) := by
  obtain ⟨A⟩ := exists_certificate t ht
  refine ⟨A, ?_⟩
  intro ell
  exact ⟨concreteExactEncoder_gates hD hd A ell,
    concreteExactEncoder_injective hD hd A ell,
    concreteExactEncoder_distance hD hd A ell⟩

/-- Unconditional ONE finite certificate outside ALL dyadic lengths. The
programs are actually the defined emitter/one-copy composition, not free advice.
This existential does not materialize or execute the astronomical certificate. -/
theorem exists_one_certificate_all_concrete_encoders :
    ∃ A : CertifiedParity (512 * 2 ^ 1528) (64 * 2 ^ 1528) (2 ^ 1528),
      ∀ ell : Nat,
        let P := concreteExactEncoder (D := 16 ^ 384) rfl
          FiniteLocalCountingCandidate.fixed_degree_reparametrization A ell
        P.gates ≤ 2 * (16 ^ 384) * ((64 * (16 ^ 384)) * 2 ^ ell) ∧
        Function.Injective P.toLinear ∧
        ∀ x : Word (((64 * (16 ^ 384)) * 2 ^ ell) / 4), x ≠ 0 →
          alpha * (((64 * (16 ^ 384)) * 2 ^ ell : Nat) : ℝ) ≤
            (weight (P.toLinear x) : ℝ) := by
  exact exists_one_certificate_all_concrete_encoders_generic rfl
    FiniteLocalCountingCandidate.fixed_degree_reparametrization
    (pow_pos (by decide : 0 < (2 : Nat)) _)

end QecReliability.SharedCircuit.FixedLocalEmitter
