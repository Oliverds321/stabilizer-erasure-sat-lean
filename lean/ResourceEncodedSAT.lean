import OracleCost.EncodedSAT

/-! An additional resource-parametric SAT contract. The existing `EncodedSAT`
contract is unchanged. Resource measures and envelopes are proof specifications,
not runtime advice or extra machine inputs. -/
namespace QecReliability.OracleCost
open PrefixCNF MultiTape

/-- Binary payload plus explicitly charged ambient dimension. -/
def requestExtent (request : SATRequest) : ℕ :=
  request.varCount + (QueryCodec.encode request).length

variable {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]

structure ResourceEncodedSAT (M : Machine k Γ Λ) (D : ℕ)
    (Ptime Pspace : PolynomialEnvelope) (T : ℕ → ℕ)
    (resource : SATRequest → ℕ) : Prop where
  positive_density_parameter : 0 < D
  complete : ∀ request : SATRequest, D * request.formula.length ≤ request.varCount →
    ∃ run : Completed M (QueryCodec.encode request),
      (run.output = true ↔ ∃ a, eval request.formula a = true) ∧
      run.time ≤ Ptime.eval (resource request) * T request.varCount ∧
      run.cells ≤ Pspace.eval (resource request)

variable {M : Machine k Γ Λ} {D : ℕ} {Ptime Pspace : PolynomialEnvelope}
    {T : ℕ → ℕ} {resource : SATRequest → ℕ}

/-- The old, stronger contract embeds without changing its statement or machine. -/
theorem EncodedSAT.toResource (spec : EncodedSAT M D Ptime Pspace T)
    (hresource : ∀ q, (QueryCodec.encode q).length ≤ resource q) :
    ResourceEncodedSAT M D Ptime Pspace T resource := by
  refine ⟨spec.positive_density_parameter, ?_⟩
  intro q hd
  obtain ⟨run, hout, ht, hs⟩ := spec.complete q hd
  exact ⟨run, hout, ht.trans (Nat.mul_le_mul_right _ (Ptime.monotone (hresource q))),
    hs.trans (Pspace.monotone (hresource q))⟩

theorem EncodedSAT.toDimensionAware (spec : EncodedSAT M D Ptime Pspace T) :
    ResourceEncodedSAT M D Ptime Pspace T requestExtent :=
  spec.toResource (fun q => by unfold requestExtent; omega)

noncomputable def ResourceEncodedSAT.run
    (spec : ResourceEncodedSAT M D Ptime Pspace T resource) (request : SATRequest) :
    Completed M (QueryCodec.encode (padRequest D request)) :=
  Classical.choose (spec.complete (padRequest D request) (padRequest_density D request))

theorem ResourceEncodedSAT.run_spec
    (spec : ResourceEncodedSAT M D Ptime Pspace T resource) (request : SATRequest) :
    ((spec.run request).output = true ↔ ∃ a, eval (padRequest D request).formula a = true) ∧
    (spec.run request).time ≤ Ptime.eval (resource (padRequest D request)) *
      T (padRequest D request).varCount ∧
    (spec.run request).cells ≤ Pspace.eval (resource (padRequest D request)) :=
  Classical.choose_spec (spec.complete (padRequest D request) (padRequest_density D request))

noncomputable def ResourceEncodedSAT.service
    (spec : ResourceEncodedSAT M D Ptime Pspace T resource) : SATService where
  run request := ⟨(spec.run request).output, (spec.run request).time,
    machineCellBits Γ * (spec.run request).cells + machineControlBits Λ⟩
  correct request := (spec.run_spec request).1.trans (padRequest_sat D request)

theorem ResourceEncodedSAT.realizes
    (spec : ResourceEncodedSAT M D Ptime Pspace T resource) (request : SATRequest) :
    ∃ run : Completed M (QueryCodec.encode (padRequest D request)),
      run.output = (spec.service.run request).value ∧
      run.time = (spec.service.run request).time ∧
      machineCellBits Γ * run.cells + machineControlBits Λ =
        (spec.service.run request).workspace :=
  ⟨spec.run request, rfl, rfl, rfl⟩

/-- Generic bounds require an explicit bound on the padded resource measure. -/
theorem ResourceEncodedSAT.request_bounds
    (spec : ResourceEncodedSAT M D Ptime Pspace T resource) (hT : Monotone T)
    (request : SATRequest) (V R : ℕ)
    (hv : (padRequest D request).varCount ≤ V)
    (hr : resource (padRequest D request) ≤ R) :
    (spec.service.run request).time ≤ Ptime.eval R * T V ∧
    (spec.service.run request).workspace ≤
      machineCellBits Γ * Pspace.eval R + machineControlBits Λ := by
  have hs := spec.run_spec request
  exact ⟨hs.2.1.trans (Nat.mul_le_mul (Ptime.monotone hr) (hT hv)),
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (hs.2.2.trans (Pspace.monotone hr))) _⟩

theorem padRequest_extent_le (request : SATRequest) (V C : ℕ)
    (hv : request.varCount ≤ V) (hc : request.formula.length ≤ C) :
    requestExtent (padRequest D request) ≤
      max V (D*C) + QueryCodec.sizeBound (max V (D*C)) C := by
  have hp := padRequest_size request hv hc (D := D)
  exact Nat.add_le_add hp.1 hp.2

theorem ResourceEncodedSAT.dimension_request_bounds
    (spec : ResourceEncodedSAT M D Ptime Pspace T requestExtent) (hT : Monotone T)
    (request : SATRequest) (V C : ℕ)
    (hv : request.varCount ≤ V) (hc : request.formula.length ≤ C) :
    (spec.service.run request).time ≤
      Ptime.eval (max V (D*C) + QueryCodec.sizeBound (max V (D*C)) C) * T (max V (D*C)) ∧
    (spec.service.run request).workspace ≤
      machineCellBits Γ *
        Pspace.eval (max V (D*C) + QueryCodec.sizeBound (max V (D*C)) C) +
      machineControlBits Λ :=
  spec.request_bounds hT request _ _ (padRequest_size request hv hc).1
    (padRequest_extent_le request V C hv hc)

end QecReliability.OracleCost
