import WholeWrapperContracts
import OracleCost.EncodedSAT

/-!
# The concrete `External` interface of the macro controller

`concreteExternal` instantiates the three charged boundaries of
`WholeWrapperCandidate.step`:

* `compileQuery key` is the canonical serialization `QueryCodec.encode (padRequest D _)`
  of the resolved concrete quantum request when `key` is valid (and `[]` otherwise);
* `sat bits` is the reply of the fixed external SAT machine `E` on `bits`, read off
  from its (unique) completed run whenever `bits` is the canonical encoding of some
  padded request (a classical choice of such a request; the choice is irrelevant by
  `Completed.unique`), and `emptyReply` otherwise;
* `endpoint side` is the exact dyadic endpoint ratio.

All construction/endpoint costs are reported as `0`: they are *macro* observations only;
the bit-level cost of these boundaries belongs to the register-program lowering.

`concreteExternal_boundary` proves `BoundaryCorrect` (all four fields). No injectivity of
`QueryCodec.encode ∘ padRequest D` is needed: equal bits give equal completed runs.
-/

set_option autoImplicit false

noncomputable section
namespace QecReliability.Final
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput

section SAT
variable {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {D : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}

/-- Two completed runs of the same deterministic machine on equal inputs have the same
observations. Stated with an explicit input equality so it can be used across the
syntactically different inputs `encode (padRequest D req₁) = encode (padRequest D req₂)`. -/
theorem completed_observations_eq {b₁ b₂ : List Bool} (h : b₁ = b₂)
    (r₁ : Completed E b₁) (r₂ : Completed E b₂) :
    r₁.output = r₂.output ∧ r₁.time = r₂.time ∧ r₁.cells = r₂.cells := by
  subst h
  obtain ⟨_, ht, hc, ho⟩ := Completed.unique r₁ r₂
  exact ⟨ho, ht, hc⟩

/-- The SAT service of `spec` only depends on the canonical query bits. -/
theorem service_run_eq_of_encode_eq (spec : EncodedSAT E D PtE PsE T)
    {req₁ req₂ : SATRequest}
    (h : QueryCodec.encode (padRequest D req₁) = QueryCodec.encode (padRequest D req₂)) :
    spec.service.run req₁ = spec.service.run req₂ := by
  obtain ⟨ho, ht, hc⟩ := completed_observations_eq h (spec.run req₁) (spec.run req₂)
  change SATReply.mk (spec.run req₁).output (spec.run req₁).time
      (machineCellBits ΓE * (spec.run req₁).cells + machineControlBits ΛE) =
    SATReply.mk (spec.run req₂).output (spec.run req₂).time
      (machineCellBits ΓE * (spec.run req₂).cells + machineControlBits ΛE)
  rw [ho, ht, hc]

/-- Bits that are the canonical padded encoding of some request. -/
def IsPaddedQuery (D : ℕ) (bits : List Bool) : Prop :=
  ∃ req : SATRequest, bits = QueryCodec.encode (padRequest D req)

open scoped Classical in
/-- Reply of the external SAT machine on a query word. -/
def satReply (spec : EncodedSAT E D PtE PsE T) (bits : List Bool) : SATReply :=
  if h : IsPaddedQuery D bits then spec.service.run (Classical.choose h) else emptyReply

theorem satReply_encode (spec : EncodedSAT E D PtE PsE T) (req : SATRequest) :
    satReply spec (QueryCodec.encode (padRequest D req)) = spec.service.run req := by
  have h : IsPaddedQuery D (QueryCodec.encode (padRequest D req)) := ⟨req, rfl⟩
  unfold satReply
  rw [dif_pos h]
  exact service_run_eq_of_encode_eq spec (Classical.choose_spec h).symm

/-- Physical meaning of `satReply`: on a canonical padded query, EVERY completed run of
the fixed machine `E` on exactly those bits reports the same answer, time and
(cell-bit) workspace as `satReply`. -/
theorem satReply_of_completed (spec : EncodedSAT E D PtE PsE T) {bits : List Bool}
    (hbits : IsPaddedQuery D bits) (run : Completed E bits) :
    (satReply spec bits).value = run.output ∧ (satReply spec bits).time = run.time ∧
      (satReply spec bits).workspace = machineCellBits ΓE * run.cells + machineControlBits ΛE := by
  obtain ⟨req, rfl⟩ := hbits
  rw [satReply_encode]
  obtain ⟨ho, ht, hc⟩ := completed_observations_eq rfl (spec.run req) run
  exact ⟨ho, ht, by
    change machineCellBits ΓE * (spec.run req).cells + machineControlBits ΛE = _
    rw [hc]⟩

/-- A completed run exists on every canonical padded query (the SAT premise). -/
theorem exists_completed_of_padded (spec : EncodedSAT E D PtE PsE T) {bits : List Bool}
    (hbits : IsPaddedQuery D bits) : Nonempty (Completed E bits) := by
  obtain ⟨req, rfl⟩ := hbits
  exact ⟨spec.run req⟩

end SAT

section Boundary
variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))
    (m : ℕ) (ω : Fin (2*m+1) → Ω) (D : ℕ)

open scoped Classical in
/-- The canonical padded query of a request key (`[]` for invalid keys, which are never
reached by the controller, see `reachable_request_invariant`). -/
def concreteQuery (key : RequestKey) : List Bool :=
  if valid : ValidKey (keySize n r) r m key then
    QueryCodec.encode (padRequest D (resolveRequest rows C H K m ω key valid))
  else []

theorem concreteQuery_valid (key : RequestKey) (valid : ValidKey (keySize n r) r m key) :
    concreteQuery rows C H K m ω D key =
      QueryCodec.encode (padRequest D (resolveRequest rows C H K m ω key valid)) := by
  unfold concreteQuery
  rw [dif_pos valid]

theorem concreteQuery_padded (key : RequestKey) (valid : ValidKey (keySize n r) r m key) :
    IsPaddedQuery D (concreteQuery rows C H K m ω D key) :=
  ⟨_, concreteQuery_valid rows C H K m ω D key valid⟩

/-- Exact endpoint ratios (`false` ↦ empty cause set, `true` ↦ all causes). -/
def concreteEndpoint : Bool → EndpointResult
  | false => ⟨Ratio.dyadic rows (circuitMap C ∅), 0, 0⟩
  | true => ⟨Ratio.dyadic rows (circuitMap C Finset.univ), 0, 0⟩

variable {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}

/-- The concrete external interface. -/
def concreteExternal (spec : EncodedSAT E D PtE PsE T) : External where
  compileQuery key := ⟨concreteQuery rows C H K m ω D key, 0, 0⟩
  sat := satReply spec
  endpoint := concreteEndpoint rows C

@[simp] theorem concreteExternal_compileQuery (spec : EncodedSAT E D PtE PsE T)
    (key : RequestKey) :
    (concreteExternal rows C H K m ω D spec).compileQuery key =
      ⟨concreteQuery rows C H K m ω D key, 0, 0⟩ := rfl

@[simp] theorem concreteExternal_sat (spec : EncodedSAT E D PtE PsE T) :
    (concreteExternal rows C H K m ω D spec).sat = satReply spec := rfl

@[simp] theorem concreteExternal_endpoint (spec : EncodedSAT E D PtE PsE T) :
    (concreteExternal rows C H K m ω D spec).endpoint = concreteEndpoint rows C := rfl

theorem concreteExternal_endpoint_time (spec : EncodedSAT E D PtE PsE T) (side : Bool) :
    ((concreteExternal rows C H K m ω D spec).endpoint side).time = 0 ∧
      ((concreteExternal rows C H K m ω D spec).endpoint side).space = 0 := by
  cases side <;> exact ⟨rfl, rfl⟩

/-- Boundary fidelity of the concrete external interface: all four fields. -/
theorem concreteExternal_boundary (spec : EncodedSAT E D PtE PsE T) :
    BoundaryCorrect rows C H K spec.service m ω D (concreteExternal rows C H K m ω D spec) where
  query key valid := concreteQuery_valid rows C H K m ω D key valid
  answer key valid := by
    change satReply spec (concreteQuery rows C H K m ω D key) = _
    rw [concreteQuery_valid rows C H K m ω D key valid]
    exact satReply_encode spec _
  endpoint0 := rfl
  endpoint1 := rfl

end Boundary

end QecReliability.Final
