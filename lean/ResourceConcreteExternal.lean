import ResourceEncodedSAT
import Final.ConcreteExternal

/-! Resource-parametric sibling of the concrete boundary. Uses the original
query bytes, endpoints and deterministic completed-run uniqueness. -/
set_option autoImplicit false

noncomputable section
namespace QecReliability.Final.Resource
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput

section SAT
variable {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {D : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ} {resource : SATRequest → ℕ}

/-- The SAT service of `spec` only depends on the canonical query bits. -/
theorem service_run_eq_of_encode_eq (spec : ResourceEncodedSAT E D PtE PsE T resource)
    {req₁ req₂ : SATRequest}
    (h : QueryCodec.encode (padRequest D req₁) = QueryCodec.encode (padRequest D req₂)) :
    spec.service.run req₁ = spec.service.run req₂ := by
  obtain ⟨ho, ht, hc⟩ := completed_observations_eq h (spec.run req₁) (spec.run req₂)
  change SATReply.mk (spec.run req₁).output (spec.run req₁).time
      (machineCellBits ΓE * (spec.run req₁).cells + machineControlBits ΛE) =
    SATReply.mk (spec.run req₂).output (spec.run req₂).time
      (machineCellBits ΓE * (spec.run req₂).cells + machineControlBits ΛE)
  rw [ho, ht, hc]

open scoped Classical in
/-- Reply of the external SAT machine on a query word. -/
def satReply (spec : ResourceEncodedSAT E D PtE PsE T resource) (bits : List Bool) : SATReply :=
  if h : IsPaddedQuery D bits then spec.service.run (Classical.choose h) else emptyReply

theorem satReply_encode (spec : ResourceEncodedSAT E D PtE PsE T resource) (req : SATRequest) :
    satReply spec (QueryCodec.encode (padRequest D req)) = spec.service.run req := by
  have h : IsPaddedQuery D (QueryCodec.encode (padRequest D req)) := ⟨req, rfl⟩
  unfold satReply
  rw [dif_pos h]
  exact service_run_eq_of_encode_eq spec (Classical.choose_spec h).symm

/-- Physical meaning of `satReply`: on a canonical padded query, EVERY completed run of
the fixed machine `E` on exactly those bits reports the same answer, time and
(cell-bit) workspace as `satReply`. -/
theorem satReply_of_completed (spec : ResourceEncodedSAT E D PtE PsE T resource) {bits : List Bool}
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
theorem exists_completed_of_padded (spec : ResourceEncodedSAT E D PtE PsE T resource) {bits : List Bool}
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

variable {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ} {resource : SATRequest → ℕ}

/-- The concrete external interface. -/
def concreteExternal (spec : ResourceEncodedSAT E D PtE PsE T resource) : External where
  compileQuery key := ⟨concreteQuery rows C H K m ω D key, 0, 0⟩
  sat := satReply spec
  endpoint := concreteEndpoint rows C

@[simp] theorem concreteExternal_compileQuery (spec : ResourceEncodedSAT E D PtE PsE T resource)
    (key : RequestKey) :
    (concreteExternal rows C H K m ω D spec).compileQuery key =
      ⟨concreteQuery rows C H K m ω D key, 0, 0⟩ := rfl

@[simp] theorem concreteExternal_sat (spec : ResourceEncodedSAT E D PtE PsE T resource) :
    (concreteExternal rows C H K m ω D spec).sat = satReply spec := rfl

@[simp] theorem concreteExternal_endpoint (spec : ResourceEncodedSAT E D PtE PsE T resource) :
    (concreteExternal rows C H K m ω D spec).endpoint = concreteEndpoint rows C := rfl

theorem concreteExternal_endpoint_time (spec : ResourceEncodedSAT E D PtE PsE T resource) (side : Bool) :
    ((concreteExternal rows C H K m ω D spec).endpoint side).time = 0 ∧
      ((concreteExternal rows C H K m ω D spec).endpoint side).space = 0 := by
  cases side <;> exact ⟨rfl, rfl⟩

/-- Boundary fidelity of the concrete external interface: all four fields. -/
theorem concreteExternal_boundary (spec : ResourceEncodedSAT E D PtE PsE T resource) :
    BoundaryCorrect rows C H K spec.service m ω D (concreteExternal rows C H K m ω D spec) where
  query key valid := concreteQuery_valid rows C H K m ω D key valid
  answer key valid := by
    change satReply spec (concreteQuery rows C H K m ω D key) = _
    rw [concreteQuery_valid rows C H K m ω D key valid]
    exact satReply_encode spec _
  endpoint0 := rfl
  endpoint1 := rfl

end Boundary

end QecReliability.Final.Resource

