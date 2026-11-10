import QecReliability.FixedLocalBaseEmitterCandidate
import QecReliability.FixedWitnessRecursiveBridgeCandidate

/-!


The actual generic padded-amplifier emitter. Every directed port occurrence is
kept: incoming slots use the full rotation (vertex AND reverse port), while
padding and zero coefficients refer to the one existing zero gate. Outputs
retain the exact vertex-major/local-row order of rawAmplifier.
No compiler-equality or semantic amplification assumption is accepted here.
Physical graph arithmetic/runtime lowering remains a separate obligation.
-/

set_option autoImplicit false
namespace QecReliability.SharedCircuit.FixedLocalEmitter
open scoped BigOperators
open CodeHash EncoderSemantics SerializedDyadicEncoder FiniteXorRowEmitter
open ExpanderWalk.SparseAmplifierCandidate
open FiniteLocalSelectorCandidate
open ExpanderWalk.FixedWitnessSparseAmplifier

/-- A stored input reference or the one shared zero, never a runtime evaluator. -/
def paddedReference {T N : Nat} (i : Fin N) : Fin (T + 1) :=
  if hi : i.val < T then (⟨i.val, hi⟩ : Fin T).castSucc else Fin.last T

theorem paddedReference_value {T N : Nat} (hIn : T ≤ N) (x : Word T) (i : Fin N) :
    Fin.snoc (α := fun _ => F) x 0 (paddedReference (T := T) i) = pad hIn x i := by
  by_cases hi : i.val < T
  · rw [paddedReference, dif_pos hi, Fin.snoc_castSucc]
    simp only [pad, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hi]
  · rw [paddedReference, dif_neg hi, Fin.snoc_last]
    simp only [pad, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi]

/-- Both halves contain distinct port SLOTS, including loops and repeated arcs. -/
def portReferences {vertices d T : Nat} (G : ExpanderWalk.PortGraph vertices d)
    (v : Fin vertices) : Fin (d + d) → Fin (T + 1) :=
  Fin.addCases (fun i => paddedReference (finProdFinEquiv (v, i)))
    (fun i => paddedReference (finProdFinEquiv (G.rotation (v, i))))

theorem portReferences_value {vertices d T : Nat} (G : ExpanderWalk.PortGraph vertices d)
    (hIn : T ≤ vertices * d) (x : Word T) (v : Fin vertices) (i : Fin (d + d)) :
    Fin.snoc (α := fun _ => F) x 0 (portReferences (T := T) G v i) =
      localWord G (fun p => pad hIn x (finProdFinEquiv p)) v i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [portReferences, Fin.addCases_left, localWord_out]
    exact paddedReference_value hIn x _
  · simp only [portReferences, Fin.addCases_right, localWord_in]
    exact paddedReference_value hIn x _

def amplifierKeepZero {vertices d : Nat} (G : ExpanderWalk.PortGraph vertices d)
    (T : Nat) (coeff : Coefficients (d + d) (d / 4)) :
    XorProgram T (1 + vertices * (d / 4)) :=
  emitBlocksKeepZero T vertices (d + d) (d / 4) coeff (portReferences G)

theorem amplifierKeepZero_value {vertices d T : Nat} (G : ExpanderWalk.PortGraph vertices d)
    (hIn : T ≤ vertices * d) (coeff : Coefficients (d + d) (d / 4))
    (x : Word T) (out : Fin (vertices * (d / 4))) :
    (amplifierKeepZero G T coeff).toLinear x (Fin.natAdd 1 out) =
      rawAmplifier G (boolParity coeff) (pad hIn x) out := by
  rw [amplifierKeepZero, emitBlocksKeepZero_value]
  change boolParity coeff
    (fun j => Fin.snoc (α := fun _ => F) x 0 (portReferences G (finProdFinEquiv.symm out).1 j))
    (finProdFinEquiv.symm out).2 =
      boolParity coeff
        (localWord G (fun p => pad hIn x (finProdFinEquiv p)) (finProdFinEquiv.symm out).1)
        (finProdFinEquiv.symm out).2
  apply congrArg (fun z => boolParity coeff z (finProdFinEquiv.symm out).2)
  funext j
  exact portReferences_value G hIn x _ j

/-- The final output-zero padding is only an array of existing references. -/
def amplifierProgram {vertices d T : Nat} (G : ExpanderWalk.PortGraph vertices d)
    (_hIn : T ≤ vertices * d) (_hOut : vertices * (d / 4) ≤ T / 2)
    (coeff : Coefficients (d + d) (d / 4)) : XorProgram T (T / 2) :=
  let P := amplifierKeepZero G T coeff
  { gates := P.gates
    circuit := P.circuit
    output := fun j => if hj : j.val < vertices * (d / 4) then
      P.output (Fin.natAdd 1 ⟨j.val, hj⟩)
      else P.output (Fin.castAdd (vertices * (d / 4)) 0) }

/-- Exact generic padded-amplifier compiler equality, without a correctness premise. -/
theorem amplifierProgram_linear {vertices d T : Nat} (G : ExpanderWalk.PortGraph vertices d)
    (hIn : T ≤ vertices * d) (hOut : vertices * (d / 4) ≤ T / 2)
    (coeff : Coefficients (d + d) (d / 4)) :
    (amplifierProgram G hIn hOut coeff).toLinear =
      paddedAmplifier G hIn hOut (boolParity coeff) := by
  apply LinearMap.ext
  intro x
  funext j
  let P := amplifierKeepZero G T coeff
  change P.circuit.fieldRun x
    (if hj : j.val < vertices * (d / 4) then P.output (Fin.natAdd 1 ⟨j.val, hj⟩)
      else P.output (Fin.castAdd (vertices * (d / 4)) 0)) =
    pad hOut (rawAmplifier G (boolParity coeff) (pad hIn x)) j
  by_cases hj : j.val < vertices * (d / 4)
  · rw [dif_pos hj]
    change P.toLinear x (Fin.natAdd 1 ⟨j.val, hj⟩) = _
    rw [amplifierKeepZero_value G hIn]
    simp only [pad, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hj]
  · rw [dif_neg hj]
    change P.toLinear x (Fin.castAdd (vertices * (d / 4)) 0) = _
    rw [show P.toLinear x (Fin.castAdd (vertices * (d / 4)) 0) = 0 from
      emitBlocksKeepZero_zero T vertices (d + d) (d / 4) coeff (portReferences G) x]
    simp only [pad, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hj]

@[simp] theorem amplifierProgram_gates {vertices d T : Nat} (G : ExpanderWalk.PortGraph vertices d)
    (hIn : T ≤ vertices * d) (hOut : vertices * (d / 4) ≤ T / 2)
    (coeff : Coefficients (d + d) (d / 4)) :
    (amplifierProgram G hIn hOut coeff).gates =
      1 + (vertices * (d / 4)) * (d + d) :=
  emitBlocksKeepZero_gates _ _ _ _ _ _

/-- Exactly the local gate estimate required by encoder_gates_le. -/
theorem amplifierProgram_gates_le {vertices d T : Nat} (G : ExpanderWalk.PortGraph vertices d)
    (hIn : T ≤ vertices * d) (hOut : vertices * (d / 4) ≤ T / 2)
    (coeff : Coefficients (d + d) (d / 4)) :
    (amplifierProgram G hIn hOut coeff).gates ≤ d * T + 1 := by
  rw [amplifierProgram_gates]
  have hhalf : 2 * (T / 2) ≤ T := by
    have h := Nat.div_mul_le_self T 2
    omega
  calc
    1 + (vertices * (d / 4)) * (d + d) ≤ 1 + (T / 2) * (d + d) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hOut) 1
    _ = 1 + d * (2 * (T / 2)) := by ring
    _ ≤ 1 + d * T := Nat.add_le_add_left (Nat.mul_le_mul_left d hhalf) 1
    _ = d * T + 1 := Nat.add_comm _ _

/-- Concrete source compiler with only the source's declared output cast. -/
def sourceProgram {D T out : Nat} (S : PaddedSource D T out)
    (coeff : Coefficients (D + D) (D / 4)) : XorProgram T out :=
  (amplifierProgram S.graph S.input_capacity S.output_capacity coeff).outputCast S.output_eq

theorem sourceProgram_linear {D T out : Nat} (S : PaddedSource D T out)
    (coeff : Coefficients (D + D) (D / 4)) :
    (sourceProgram S coeff).toLinear = S.linear (boolParity coeff) := by
  apply LinearMap.ext
  intro x
  rw [sourceProgram, XorProgram.outputCast_linear, amplifierProgram_linear]
  rfl

theorem sourceProgram_gates_le {D T out : Nat} (S : PaddedSource D T out)
    (coeff : Coefficients (D + D) (D / 4)) :
    (sourceProgram S coeff).gates ≤ D * T + 1 :=
  amplifierProgram_gates_le S.graph S.input_capacity S.output_capacity coeff

/-- R1 for the actual powered-MGG source and the supplied certificate. -/
def firstProgram {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    XorProgram (2 * messageWidth D ell) (messageWidth D ell) :=
  sourceProgram (FixedWitnessEncoder.firstSource D hD ell) (degreeCoefficients hd A)

/-- R2 uses exactly the SAME finite local coefficient table. -/
def secondProgram {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell) :=
  sourceProgram (FixedWitnessEncoder.secondSource D hD ell) (degreeCoefficients hd A)

theorem firstProgram_linear {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    (firstProgram hD hd A ell).toLinear =
      (FixedWitnessEncoder.firstSource D hD ell).linear (parityForDegree hd A) := by
  rw [firstProgram, sourceProgram_linear, degreeCoefficients_parity]

theorem secondProgram_linear {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    (secondProgram hD hd A ell).toLinear =
      (FixedWitnessEncoder.secondSource D hD ell).linear (parityForDegree hd A) := by
  rw [secondProgram, sourceProgram_linear, degreeCoefficients_parity]

theorem firstProgram_gates_le {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    (firstProgram hD hd A ell).gates ≤ D * (2 * messageWidth D ell) + 1 :=
  sourceProgram_gates_le _ _

theorem secondProgram_gates_le {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : Nat) :
    (secondProgram hD hd A ell).gates ≤ D * (4 * messageWidth D ell) + 1 :=
  sourceProgram_gates_le _ _

end QecReliability.SharedCircuit.FixedLocalEmitter
