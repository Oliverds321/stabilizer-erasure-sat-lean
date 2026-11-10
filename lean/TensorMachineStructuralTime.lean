import TensorMachineCountingTotals

/-! The SAT exponent depends only on the code and observation circuit.
Accuracy and confidence remain in the polynomial and repetition factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachine.Boundary
open SharedCircuit TensorCoefficientCounting SharedCircuit.LatentEncoding
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate

/-- Raw combinatorial extent of the code and observation circuit. No encoding
logarithms, precision headers, or coefficient-grid cardinality enter this size. -/
def satStructuralSize {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n) : ℕ :=
  n+ds.sum+rowIncidences rows+C.gates+ds.length

/-- A common linear variable cap for all density-padded tensor queries. -/
theorem raw_input_variable_cap {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (factor density : ℕ) :
    let g := factor*(keySize n ds.sum+1)
    max (TensorQuery.Service.variableBound rows C g)
      (density*TensorQuery.Service.clauseBound rows C g) ≤
        variableCoefficient density factor*(satStructuralSize rows C+1) := by
  let V := satStructuralSize rows C
  let N := inputScale factor V
  let g := factor*(keySize n ds.sum+1)
  have hn : n≤V := by dsimp [V,satStructuralSize]; omega
  have hr : ds.sum≤V := by dsimp [V,satStructuralSize]; omega
  have hk : ds.length≤V := by dsimp [V,satStructuralSize]; omega
  have hrows : rowIncidences rows≤V := by dsimp [V,satStructuralSize]; omega
  have hC : C.gates≤V := by dsimp [V,satStructuralSize]; omega
  have hq : keySize n ds.sum≤2*V := by
    dsimp [keySize,V,satStructuralSize]
    omega
  have hVN : V≤N := by dsimp [N,inputScale]; nlinarith
  have hg : g≤N := by
    have h := Nat.mul_le_mul_left factor (show keySize n ds.sum+1≤2*V+1 by omega)
    dsimp [g,N,inputScale]
    nlinarith
  have hd := TensorQuery.Service.linear_dimensions rows C g N
    (hr.trans hVN) (hk.trans hVN) (hn.trans hVN) (hrows.trans hVN) (hC.trans hVN) hg
  have hv : max (TensorQuery.Service.variableBound rows C g)
      (density*TensorQuery.Service.clauseBound rows C g)≤(46+178*density)*N+6*density+1 := by
    apply max_le
    · nlinarith [Nat.zero_le (178*density*N),Nat.zero_le (6*density)]
    · have hh := Nat.mul_le_mul_left density hd.2
      nlinarith
  have hlin : (46+178*density)*N+6*density+1≤variableCoefficient density factor*(V+1) := by
    dsimp [N,inputScale,variableCoefficient]
    nlinarith [Nat.zero_le ((6*density+1)*V)]
  exact hv.trans hlin

variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {density : ℕ} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent)

theorem structural_total_time (hT : Monotone T) (factor : ℕ) :
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
        P.eval L*(B+1)*T (variableCoefficient density factor*(satStructuralSize rows C+1)) := by
  have hp : Assembly.PolyBounded (fun L => 512*(L+1)^4*Pt.eval (extentPolynomial density factor L)) := by
    have he := extentPolynomial_pb density factor
    poly_bounded
  obtain ⟨P,hP⟩ := hp.envelope
  refine ⟨P,?_⟩
  intro Ω _ n ds rows C H K hg a b c d B ha hc ω
  let L := resourceSize rows C a b c d
  let m := rationalRepetitionBudget (2*slots ds) c d
  let ext := external rows C H K m ω density spec
  let rate := T (variableCoefficient density factor*(satStructuralSize rows C+1))
  let charge := Pt.eval (extentPolynomial density factor L)*rate
  have hcharge : ∀ key (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key),
      (ext.sat (ext.compileQuery key).bits).time ≤ charge := by
    intro key valid
    have hd := resolve_caps rows C H K m ω density _ hg key valid
    have hvar := raw_input_variable_cap rows C factor density
    have hsize := (input_caps rows C a b c d factor density ha hc).2
    rw [answer rows C H K m ω density spec key valid]
    exact (spec.request_bounds hT _ _ _ (hd.1.trans hvar)
      ((hd.2.trans hsize).trans (extentPolynomial_mono density factor
        (structuralSize_le_resource rows C a b c d)))).1
  have ht := CountingTrace.side_time_le (keySize n ds.sum) (slots ds-1) B m ext charge
    hcharge true (List.finRange (slots ds-1+1))
  have hf := CountingTrace.side_time_le (keySize n ds.sum) (slots ds-1) B m ext charge
    hcharge false (List.finRange (slots ds-1+1))
  have hc := total_calls_input rows C H K spec a b c d B ha hc ω
  have hsum := Nat.mul_le_mul_right charge hc
  have henv := Nat.mul_le_mul_right ((B+1)*rate) (hP L)
  dsimp only
  dsimp only [charge,rate] at ht hf hsum henv
  nlinarith only [ht,hf,hsum,henv]

end QecReliability.TensorMachine.Boundary

namespace QecReliability.TensorMachine.Runtime
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape
variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent) (hT : Monotone T)

include hT in
theorem structural_time_budget : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d B : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool),
    let m := rationalRepetitionBudget (2*slots ds) c d
    let ext := external hD hd A density spec rows C m coins
    let L := Boundary.resourceSize rows C a b c d
    CountingTrace.sideTime (keySize n ds.sum) (slots ds-1) B m ext true (List.finRange (slots ds-1+1))+
      CountingTrace.sideTime (keySize n ds.sum) (slots ds-1) B m ext false (List.finRange (slots ds-1+1))≤
        P.eval L*(B+1)*T (Boundary.variableCoefficient density (data hD hd A).Cfixed*
          (Boundary.satStructuralSize rows C+1)) := by
  obtain ⟨P,hP⟩ := Boundary.structural_total_time spec hT (data hD hd A).Cfixed
  refine ⟨P,?_⟩
  intro n ds rows C a b c d B ha hc coins
  exact hP rows C (Factory.system hD hd A n ds).stages (Factory.circuits hD hd A n ds)
    (Factory.gates_all hD hd A n ds) a b c d B ha hc
    (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)
      (rationalRepetitionBudget (2*slots ds) c d) coins)

end QecReliability.TensorMachine.Runtime
