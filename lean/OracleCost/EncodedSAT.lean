import OracleCost.MultiTape
import OracleCost.DensityPadding

/-! A fixed finite machine consumes the actual canonical serialized queries.
The only algorithmic hypothesis here is an external exact SAT machine, with
fixed polynomial time overhead and space, on density-restricted width-three
inputs. It includes finite halting witnesses, not just bounds on runs that may
not exist. Density padding and semantic correctness are proved below.

Selecting the unique run is proof-level bookkeeping. The implementation to be
substituted is the finite machine itself. These results do not yet lower local
wrapper instructions, construct the query on tapes, or reset private tapes.
-/
namespace QecReliability.OracleCost
open PrefixCNF MultiTape

structure PolynomialEnvelope where
  coefficient : ℕ
  degree : ℕ

def PolynomialEnvelope.eval (P : PolynomialEnvelope) (n : ℕ) : ℕ :=
  P.coefficient*(n+1)^P.degree

theorem PolynomialEnvelope.monotone (P : PolynomialEnvelope) : Monotone P.eval := by
  intro a b h
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- Accepted input domain, deliberately narrower than the parser's accepted
strings: exactly generated, canonical encodings of typed width-three formulas.
No claim about the parser rejecting malformed strings is needed. -/
def CanonicalDensityInput (D : ℕ) (bits : List Bool) : Prop :=
  ∃ request : SATRequest, D*request.formula.length≤request.varCount ∧
    bits=QueryCodec.encode request

variable {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]

/-- A standard finite multitape exact-SAT assumption. Time counts transitions
plus halt inspection; space counts all visited cells, including the input.
`D>0` specifies the reciprocal clause-density restriction using an integer.
All polynomial constants and the machine are fixed, not input-specific advice. -/
structure EncodedSAT (M : Machine k Γ Λ) (D : ℕ)
    (Ptime Pspace : PolynomialEnvelope) (T : ℕ → ℕ) : Prop where
  positive_density_parameter : 0<D
  complete : ∀ request : SATRequest, D*request.formula.length≤request.varCount →
    ∃ run : Completed M (QueryCodec.encode request),
      (run.output=true ↔ ∃ a, eval request.formula a=true) ∧
      run.time≤Ptime.eval (QueryCodec.encode request).length*T request.varCount ∧
      run.cells≤Pspace.eval (QueryCodec.encode request).length

variable {M : Machine k Γ Λ} {D : ℕ} {Ptime Pspace : PolynomialEnvelope} {T : ℕ → ℕ}

noncomputable def EncodedSAT.run (spec : EncodedSAT M D Ptime Pspace T)
    (request : SATRequest) : Completed M (QueryCodec.encode (padRequest D request)) :=
  Classical.choose (spec.complete (padRequest D request) (padRequest_density D request))

theorem EncodedSAT.run_spec (spec : EncodedSAT M D Ptime Pspace T)
    (request : SATRequest) :
    ((spec.run request).output=true ↔ ∃ a, eval (padRequest D request).formula a=true) ∧
    (spec.run request).time≤Ptime.eval (QueryCodec.encode (padRequest D request)).length*
      T (padRequest D request).varCount ∧
    (spec.run request).cells≤Pspace.eval (QueryCodec.encode (padRequest D request)).length :=
  Classical.choose_spec (spec.complete (padRequest D request) (padRequest_density D request))

/-- A fixed finite alphabet uses a constant number of bits per visited cell.
This excludes wrapper buffers and the later reset/simulation metadata. -/
def machineCellBits (Γ : Type*) [Fintype Γ] : ℕ := max 1 (Fintype.card Γ).size

def machineControlBits (Λ : Type*) [Fintype Λ] : ℕ := (Fintype.card Λ).size

noncomputable def EncodedSAT.service (spec : EncodedSAT M D Ptime Pspace T) : SATService where
  run request := ⟨(spec.run request).output,(spec.run request).time,
    machineCellBits Γ*(spec.run request).cells+machineControlBits Λ⟩
  correct request := (spec.run_spec request).1.trans (padRequest_sat D request)

theorem padRequest_canonical (D : ℕ) (request : SATRequest) :
    CanonicalDensityInput D (QueryCodec.encode (padRequest D request)) :=
  ⟨padRequest D request,padRequest_density D request,rfl⟩

/-- Every service observation is backed by the fixed machine's actual finite
run on the padded encoded request, with exactly the reported answer and time. -/
theorem EncodedSAT.realizes (spec : EncodedSAT M D Ptime Pspace T) (request : SATRequest) :
    ∃ run : Completed M (QueryCodec.encode (padRequest D request)),
      run.output=(spec.service.run request).value ∧
      run.time=(spec.service.run request).time ∧
      machineCellBits Γ*run.cells+machineControlBits Λ=(spec.service.run request).workspace :=
  ⟨spec.run request,rfl,rfl,rfl⟩

theorem EncodedSAT.request_bounds (spec : EncodedSAT M D Ptime Pspace T)
    (hT : Monotone T) (request : SATRequest) (V C : ℕ)
    (hv : request.varCount≤V) (hc : request.formula.length≤C) :
    (spec.service.run request).time≤
      Ptime.eval (QueryCodec.sizeBound (max V (D*C)) C)*T (max V (D*C)) ∧
    (spec.service.run request).workspace≤
      machineCellBits Γ*Pspace.eval (QueryCodec.sizeBound (max V (D*C)) C)+
        machineControlBits Λ := by
  have hp := padRequest_size request hv hc (D:=D)
  have hs := spec.run_spec request
  exact ⟨hs.2.1.trans (Nat.mul_le_mul (Ptime.monotone hp.2) (hT hp.1)),
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (hs.2.2.trans (Pspace.monotone hp.2))) _⟩

end QecReliability.OracleCost
