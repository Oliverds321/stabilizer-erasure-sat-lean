import TensorCountingResources
import TensorFactoryResourceBounds
import Assembly.Poly

/-! Dimension-aware SAT charges with a polynomial structural-input factor and
the SAT rate evaluated only at a linear variable count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachine.Boundary
open SharedCircuit TensorCoefficientCounting SharedCircuit.LatentEncoding
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))

theorem resolve_dimensions (m : ℕ) (ω : Fin (2*m+1) → Ω) (g : ℕ)
    (hg : ∀ scale seed, (K.program scale seed).gates≤g)
    (key : RequestKey) (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key) :
    (resolve rows C H K m ω key valid).varCount≤TensorQuery.Service.variableBound rows C g ∧
    (resolve rows C H K m ω key valid).formula.length≤TensorQuery.Service.clauseBound rows C g := by
  cases key with
  | base side j rep => exact TensorQuery.Service.base_dimensions rows C g _ []
  | cell side j rep scale pre =>
    exact TensorQuery.Service.cell_dimensions rows C H K g _ _ _ pre (hg _ _)

theorem resolve_caps (m : ℕ) (ω : Fin (2*m+1) → Ω) (density g : ℕ)
    (hg : ∀ scale seed, (K.program scale seed).gates≤g)
    (key : RequestKey) (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key) :
    (padRequest density (resolve rows C H K m ω key valid)).varCount≤
      max (TensorQuery.Service.variableBound rows C g) (density*TensorQuery.Service.clauseBound rows C g) ∧
    requestExtent (padRequest density (resolve rows C H K m ω key valid))≤extentCap rows C density g := by
  have h := resolve_dimensions rows C H K m ω g hg key valid
  exact ⟨(TensorQuery.Service.padded_dimensions density _ _ _ h.1 h.2).1,
    padRequest_extent_le _ _ _ h.1 h.2⟩

def inputScale (factor L : ℕ) : ℕ := (2*factor+1)*(L+1)
def variableCoefficient (density factor : ℕ) : ℕ :=
  (46+178*density)*(2*factor+1)+6*density+1
def extentPolynomial (density factor L : ℕ) : ℕ :=
  variableCoefficient density factor*(L+1)+TensorQuery.Service.bitBound density (inputScale factor L)

def structuralSize (a b c d : ℕ) : ℕ :=
  InputEncoding.paperLength rows C a b c d+ds.length

theorem structuralSize_le_resource (a b c d : ℕ) :
    structuralSize rows C a b c d≤resourceSize rows C a b c d := by
  unfold structuralSize resourceSize
  omega

theorem extentPolynomial_mono (density factor : ℕ) : Monotone (extentPolynomial density factor) := by
  intro x y h
  unfold extentPolynomial TensorQuery.Service.bitBound inputScale
  dsimp only
  gcongr

theorem extentPolynomial_pb (density factor : ℕ) : Assembly.PolyBounded (extentPolynomial density factor) := by
  unfold extentPolynomial TensorQuery.Service.bitBound inputScale
  poly_bounded

theorem input_caps (a b c d factor density : ℕ) (ha : 0<a) (hc : 0<c) :
    let L := structuralSize rows C a b c d
    let g := factor*(keySize n ds.sum+1)
    max (TensorQuery.Service.variableBound rows C g) (density*TensorQuery.Service.clauseBound rows C g)≤
      variableCoefficient density factor*(L+1) ∧
    extentCap rows C density g≤extentPolynomial density factor L := by
  let L := structuralSize rows C a b c d
  let N := inputScale factor L
  let g := factor*(keySize n ds.sum+1)
  obtain ⟨hn0,hr0,hrows0,hC0,_⟩ := InputEncoding.paperLength_components rows C a b c d
  have hq0 := InputEncoding.keySize_le_paperLength rows C a b c d
  have hn : n≤L := by dsimp [L,structuralSize]; omega
  have hr : ds.sum≤L := by dsimp [L,structuralSize]; omega
  have hq : keySize n ds.sum≤2*L := by dsimp [L,structuralSize]; omega
  have hk : ds.length≤L := by dsimp [L,structuralSize]; omega
  have hrows : rowIncidences rows≤L := by dsimp [L,structuralSize]; omega
  have hC : C.gates≤L := by dsimp [L,structuralSize]; omega
  have hLN : L≤N := by dsimp [N,inputScale]; nlinarith
  have hg : g≤N := by
    have h := Nat.mul_le_mul_left factor (show keySize n ds.sum+1≤2*L+1 by omega)
    dsimp [g,N,inputScale]; nlinarith
  have hd := TensorQuery.Service.linear_dimensions rows C g N
    (hr.trans hLN) (hk.trans hLN) (hn.trans hLN) (hrows.trans hLN) (hC.trans hLN) hg
  have hv : max (TensorQuery.Service.variableBound rows C g)
      (density*TensorQuery.Service.clauseBound rows C g)≤(46+178*density)*N+6*density+1 := by
    apply max_le
    · nlinarith [Nat.zero_le (178*density*N),Nat.zero_le (6*density)]
    · have hh := Nat.mul_le_mul_left density hd.2
      nlinarith
  have hlin : (46+178*density)*N+6*density+1≤variableCoefficient density factor*(L+1) := by
    dsimp [N,inputScale,variableCoefficient]
    nlinarith [Nat.zero_le ((6*density+1)*L)]
  have he := extentCap_polynomial rows C density g N
    (hr.trans hLN) (hk.trans hLN) (hn.trans hLN) (hrows.trans hLN) (hC.trans hLN) hg
  exact ⟨hv.trans hlin,he.trans (Nat.add_le_add_right hlin _)⟩

variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {density : ℕ} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent)

/-- Common charge for every real request. Its only circuit premise is the
gate bound discharged by Factory.gates_all, including the empty key. -/
theorem input_request_charge (hT : Monotone T) (factor : ℕ)
    (hg : ∀ scale seed, (K.program scale seed).gates≤factor*(keySize n ds.sum+1))
    (a b c d : ℕ) (ha : 0<a) (hc : 0<c) (m : ℕ) (ω : Fin (2*m+1) → Ω)
    (key : RequestKey) (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key) :
    ((external rows C H K m ω density spec).sat
      ((external rows C H K m ω density spec).compileQuery key).bits).time≤
      Pt.eval (extentPolynomial density factor (resourceSize rows C a b c d))*
        T (variableCoefficient density factor*(structuralSize rows C a b c d+1)) := by
  have hd := resolve_caps rows C H K m ω density _ hg key valid
  have hi := input_caps rows C a b c d factor density ha hc
  rw [answer rows C H K m ω density spec key valid]
  exact (spec.request_bounds hT _ _ _ (hd.1.trans hi.1)
    ((hd.2.trans hi.2).trans (extentPolynomial_mono density factor
      (structuralSize_le_resource rows C a b c d)))).1

private theorem calls_scalar_bound (q Q B m L : ℕ) (hq : q≤2*L) (hQ : Q≤L)
    (hm : 2*m+1≤6*L+5) :
    2*Q*(2*m+1)*trialCallCap q B≤512*(L+1)^4*(B+1) := by
  have h1 : 4*B+1≤4*(B+1) := by omega
  have h2 := Nat.mul_le_mul (show 2*q≤4*L by omega) h1
  have hpre : prefixCallCap q B≤17*(L+1)*(B+1) := by
    unfold prefixCallCap
    nlinarith
  have h3 := Nat.mul_le_mul (show q+1≤2*(L+1) by omega) hpre
  have htrial : trialCallCap q B≤35*(L+1)^2*(B+1) := by
    unfold trialCallCap
    have hp : 1≤(L+1)^2*(B+1) :=
      Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (by omega : 1≤B+1)
    nlinarith
  have h4 := Nat.mul_le_mul (show 2*Q≤2*(L+1) by omega)
    (show 2*m+1≤6*(L+1) by omega)
  have h5 := Nat.mul_le_mul h4 htrial
  nlinarith only [h5,Nat.zero_le ((L+1)^4*(B+1))]

theorem total_calls_input (a b c d B : ℕ) (ha : 0<a) (hc : 0<c)
    (ω : Fin (2*rationalRepetitionBudget (2*slots ds) c d+1) → Ω) :
    let m := rationalRepetitionBudget (2*slots ds) c d
    let ext := external rows C H K m ω density spec
    CountingTrace.sideCalls (keySize n ds.sum) (slots ds-1) B m ext true (List.finRange (slots ds-1+1))+
      CountingTrace.sideCalls (keySize n ds.sum) (slots ds-1) B m ext false (List.finRange (slots ds-1+1))≤
        512*(resourceSize rows C a b c d+1)^4*(B+1) := by
  have h := total_calls_le rows C H K _ ω density spec B
  obtain ⟨_,hq,_,hm,_⟩ := resource_parameters rows C a b c d ha hc
  have hQ : slots ds≤resourceSize rows C a b c d := by unfold resourceSize; omega
  exact h.trans (calls_scalar_bound _ _ _ _ _ hq hQ hm)

/-- Total measured SAT time has one fixed polynomial input factor, linear
dependence on the numeric cell cap, and the original SAT rate at a linear
variable count. This includes the zero-cause and zero-degree cases. -/
theorem total_time_input (hT : Monotone T) (factor : ℕ) :
    ∃ P : PolynomialEnvelope, ∀ {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (H : HashStages Ω (Key n ds) (keySize n ds.sum))
    (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds)),
    (∀ scale seed, (K.program scale seed).gates≤factor*(keySize n ds.sum+1)) →
    ∀ a b c d B : ℕ, 0<a → 0<c →
    ∀ (ω : Fin (2*rationalRepetitionBudget (2*slots ds) c d+1) → Ω),
    let m := rationalRepetitionBudget (2*slots ds) c d
    let ext := external rows C H K m ω density spec
    let L := resourceSize rows C a b c d
    CountingTrace.sideTime (keySize n ds.sum) (slots ds-1) B m ext true (List.finRange (slots ds-1+1))+
      CountingTrace.sideTime (keySize n ds.sum) (slots ds-1) B m ext false (List.finRange (slots ds-1+1))≤
        P.eval L*(B+1)*T (variableCoefficient density factor*(structuralSize rows C a b c d+1)) := by
  have hp : Assembly.PolyBounded (fun L => 512*(L+1)^4*Pt.eval (extentPolynomial density factor L)) := by
    have he := extentPolynomial_pb density factor
    poly_bounded
  obtain ⟨P,hP⟩ := hp.envelope
  refine ⟨P,?_⟩
  intro Ω _ n ds rows C H K hg a b c d B ha hc ω
  let L := resourceSize rows C a b c d
  let Lstruct := structuralSize rows C a b c d
  let m := rationalRepetitionBudget (2*slots ds) c d
  let ext := external rows C H K m ω density spec
  let charge := Pt.eval (extentPolynomial density factor L)*T (variableCoefficient density factor*(Lstruct+1))
  have hcharge := input_request_charge rows C H K spec hT factor hg a b c d ha hc m ω
  have ht := CountingTrace.side_time_le (keySize n ds.sum) (slots ds-1) B m ext charge
    hcharge true (List.finRange (slots ds-1+1))
  have hf := CountingTrace.side_time_le (keySize n ds.sum) (slots ds-1) B m ext charge
    hcharge false (List.finRange (slots ds-1+1))
  have hc := total_calls_input rows C H K spec a b c d B ha hc ω
  have hsum := Nat.mul_le_mul_right charge hc
  have henv := Nat.mul_le_mul_right ((B+1)*T (variableCoefficient density factor*(Lstruct+1))) (hP L)
  dsimp only
  dsimp only [charge] at ht hf hsum
  nlinarith only [ht,hf,hsum,henv]

end QecReliability.TensorMachine.Boundary
