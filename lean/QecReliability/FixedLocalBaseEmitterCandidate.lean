import QecReliability.FiniteXorRowEmitterCandidate
import QecReliability.FixedWitnessSparseAmplifierCandidate

/-!


Actual circuit definitions for one supplied row-major Boolean local matrix.
The eight-block base compiler equality and gate count are proved below, not
accepted as premises. False coefficients emit XOR with the one shared zero.
This replaces support skipping by an equally valid,
fixed-length row-major emitter with the SAME semantic matrix and gate bound.
-/

set_option autoImplicit false
namespace QecReliability.SharedCircuit.FixedLocalEmitter
open scoped BigOperators
open CodeHash EncoderSemantics SerializedDyadicEncoder FiniteXorRowEmitter
open FiniteLocalSelectorCandidate
open ExpanderWalk.FixedWitnessSparseAmplifier

abbrev Coefficients (k h : Nat) := Fin h → Fin k → Bool

/-- Semantic interpretation only; the emitter itself uses the finite Bool table. -/
noncomputable def boolParity {k h : Nat} (coeff : Coefficients k h) :
    Word k →ₗ[F] Word h :=
  FiniteLocalCountingCandidate.parityLinear
    (fun i j => PackedSemanticBridgeCandidate.bitF (coeff i j))

/-- One local matrix reused at every block; references supply the local inputs. -/
def emitBlocksKeepZero (n blocks k h : Nat) (coeff : Coefficients k h)
    (refs : Fin blocks → Fin k → Fin (n + 1)) :
    XorProgram n (1 + blocks * h) :=
  emitKeepZero n (blocks * h) k (fun out col =>
    if coeff (finProdFinEquiv.symm out).2 col then
      refs (finProdFinEquiv.symm out).1 col else Fin.last n)

@[simp] theorem emitBlocksKeepZero_gates (n blocks k h : Nat) (coeff : Coefficients k h)
    (refs : Fin blocks → Fin k → Fin (n + 1)) :
    (emitBlocksKeepZero n blocks k h coeff refs).gates = 1 + (blocks * h) * k :=
  emitKeepZero_gates _ _ _ _

theorem emitBlocksKeepZero_zero (n blocks k h : Nat) (coeff : Coefficients k h)
    (refs : Fin blocks → Fin k → Fin (n + 1)) (x : Word n) :
    (emitBlocksKeepZero n blocks k h coeff refs).toLinear x (Fin.castAdd (blocks * h) 0) = 0 := by
  rw [emitBlocksKeepZero, emitKeepZero_linear, Fin.append_left]

theorem emitBlocksKeepZero_value (n blocks k h : Nat) (coeff : Coefficients k h)
    (refs : Fin blocks → Fin k → Fin (n + 1)) (x : Word n) (out : Fin (blocks * h)) :
    (emitBlocksKeepZero n blocks k h coeff refs).toLinear x (Fin.natAdd 1 out) =
      boolParity coeff
        (fun j => Fin.snoc (α := fun _ => F) x 0 (refs (finProdFinEquiv.symm out).1 j))
        (finProdFinEquiv.symm out).2 := by
  rw [emitBlocksKeepZero, emitKeepZero_linear, Fin.append_right]
  change (∑ j : Fin k, Fin.snoc (α := fun _ => F) x 0
      (if coeff (finProdFinEquiv.symm out).2 j then
        refs (finProdFinEquiv.symm out).1 j else Fin.last n)) =
    ∑ j : Fin k, PackedSemanticBridgeCandidate.bitF (coeff (finProdFinEquiv.symm out).2 j) *
      Fin.snoc (α := fun _ => F) x 0 (refs (finProdFinEquiv.symm out).1 j)
  apply Finset.sum_congr rfl
  intro j _
  cases hc : coeff (finProdFinEquiv.symm out).2 j <;>
    simp [hc, PackedSemanticBridgeCandidate.bitF]

/-- The exact primary-input block indexing already used by eightBase. -/
def eightReferences (k : Nat) (v : Fin 8) (i : Fin k) : Fin (8 * k + 1) :=
  (finProdFinEquiv (v, i)).castSucc

/-- Outputs: all original inputs, then eight parity blocks, then zero aliases.
Zero padding and primary retention emit no additional gates. -/
def eightBaseProgram {k h : Nat} (coeff : Coefficients k h) (zeros : Nat) :
    XorProgram (8 * k) (8 * k + (8 * h + zeros)) :=
  let P := emitBlocksKeepZero (8 * k) 8 k h coeff (eightReferences k)
  { gates := P.gates
    circuit := P.circuit
    output := Fin.addCases (Fin.castAdd P.gates)
      (Fin.addCases (fun j => P.output (Fin.natAdd 1 j))
        (fun _ => P.output (Fin.castAdd (8 * h) 0))) }

@[simp] theorem eightBaseProgram_gates {k h : Nat} (coeff : Coefficients k h) (zeros : Nat) :
    (eightBaseProgram coeff zeros).gates = 1 + (8 * h) * k :=
  emitBlocksKeepZero_gates _ _ _ _ _ _

/-- The genuine base compilation theorem, for any finite coefficient table. -/
theorem eightBaseProgram_linear {k h : Nat} (coeff : Coefficients k h) (zeros : Nat) :
    (eightBaseProgram coeff zeros).toLinear = eightBase (boolParity coeff) zeros := by
  apply LinearMap.ext
  intro x
  funext i
  let P := emitBlocksKeepZero (8 * k) 8 k h coeff (eightReferences k)
  change P.circuit.fieldRun x
    (Fin.addCases (Fin.castAdd P.gates)
      (Fin.addCases (fun j => P.output (Fin.natAdd 1 j))
        (fun _ : Fin zeros => P.output (Fin.castAdd (8 * h) 0))) i) =
    Fin.append x (Fin.append (eightParity (boolParity coeff) x) (0 : Word zeros)) i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left, Fin.append_left]
    exact fieldRun_primary P.circuit x j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.addCases_right, Fin.addCases_left, Fin.append_right, Fin.append_left]
      change P.toLinear x (Fin.natAdd 1 j) =
        boolParity coeff (localBlock x (finProdFinEquiv.symm j).1)
          (finProdFinEquiv.symm j).2
      have hlocal : localBlock x (finProdFinEquiv.symm j).1 =
          (fun col : Fin k => x (finProdFinEquiv ((finProdFinEquiv.symm j).1, col))) := rfl
      rw [hlocal]
      simpa only [P, eightReferences, Fin.snoc_castSucc] using
        emitBlocksKeepZero_value (8 * k) 8 k h coeff (eightReferences k) x j
    · simp only [Fin.addCases_right, Fin.append_right, Pi.zero_apply]
      exact emitBlocksKeepZero_zero (8 * k) 8 k h coeff (eightReferences k) x

/-- Literal finite coefficients of the supplied certificate, not a fresh code. -/
@[simp] theorem boolParity_certificate {k h r : Nat} (A : CertifiedParity k h r) :
    boolParity (matrixEntry A) = parity A := rfl

/-- Index casts retain all row-major coefficients. -/
def castCoefficients {k h k' h' : Nat} (hk : k = k') (hh : h = h')
    (coeff : Coefficients k h) : Coefficients k' h' :=
  fun i j => coeff (Fin.cast hh.symm i) (Fin.cast hk.symm j)

theorem boolParity_cast {k h k' h' : Nat} (hk : k = k') (hh : h = h')
    (coeff : Coefficients k h) :
    boolParity (castCoefficients hk hh coeff) =
      ExpanderWalk.SelectedSparseAmplifier.castParity hk hh (boolParity coeff) := by
  cases hk
  cases hh
  rfl

def degreeCoefficients {D t : Nat} (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) : Coefficients (D + D) (D / 4) :=
  castCoefficients (by omega : 512 * t = D + D) (by omega : 64 * t = D / 4) (matrixEntry A)

@[simp] theorem degreeCoefficients_parity {D t : Nat} (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) :
    boolParity (degreeCoefficients hd A) = parityForDegree hd A := by
  rw [degreeCoefficients, boolParity_cast, boolParity_certificate]
  rfl

/-- The base input/output casts are exactly those in baseForEncoder. -/
def baseProgram {D t : Nat} (hD4 : 4 ∣ D) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) :
    XorProgram (messageWidth D 0) (4 * messageWidth D 0) :=
  (((eightBaseProgram (degreeCoefficients hd A) (46 * D)).inputCast
    (base_input_dim D).symm).outputCast (base_output_dim hD4)).outputCast
      (base_encoder_output_dim D)

/-- Missing base equality DISCHARGED by the actual supplied-table emitter. -/
theorem baseProgram_linear {D t : Nat} (hD4 : 4 ∣ D) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) :
    (baseProgram hD4 hd A).toLinear = baseForEncoder hD4 (parityForDegree hd A) := by
  apply LinearMap.ext
  intro x
  simp only [baseProgram, XorProgram.outputCast_linear, XorProgram.inputCast_linear,
    eightBaseProgram_linear, degreeCoefficients_parity]
  rfl

/-- Exact base cost: one shared zero and one XOR for every one of 8*h*k cells. -/
theorem baseProgram_gates {D t : Nat} (hD4 : 4 ∣ D) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) :
    (baseProgram hD4 hd A).gates = 4 * D * D + 1 := by
  simp only [baseProgram, XorProgram.outputCast, XorProgram.inputCast_gates,
    eightBaseProgram_gates]
  have hfour := Nat.div_mul_cancel hD4
  have h : 8 * (D / 4) = 2 * D := by omega
  rw [h]
  ring

/-- Every serialized reference is bounded by the exact base wire count. -/
theorem baseProgram_reference_bound {D t : Nat} (hD4 : 4 ∣ D) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t)
    (v : Nat) (hv : v ∈ (baseProgram hD4 hd A).serialize.outputs) :
    v < 16 * D + (4 * D * D + 1) := by
  have h := XorProgram.serialize_output_bound (baseProgram hD4 hd A) v hv
  simpa only [baseProgram_gates, messageWidth] using h

end QecReliability.SharedCircuit.FixedLocalEmitter
