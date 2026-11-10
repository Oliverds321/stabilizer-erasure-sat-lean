import IidErasureTheorem
import PhysicalBridge.RationalOutputStorage

/-! Resource accounting as conjuncts of the closed theorems.

`isotropic_tensor_machine_guarantee_resources` extends
`isotropic_tensor_machine_guarantee_strong`, and `iid_erasure_machine_guarantee_resources`
extends `iid_erasure_machine_guarantee`, by three groups of conjuncts on every coin string:

* output bit length: every entry of the written output vector is a pair `num ≤ den`
  with `den ≤ 2 * 2^q * (4B+1)`, so both have at most `q + size(4B+1) + 1` bits, where
  `q = keySize n ds.sum` (`= 3n` in the iid case) and `B = rationalCellBudget a b`;
* SAT calls: a `Totals` record whose `calls` field is exactly the number of SAT service
  invocations made by the source-level counting schedule (`CountingTrace.sideCalls`, summed
  over both sides) against the concrete query service `ext` that answers with the fixed
  engine; the same record bounds the machine running time;
* query size: every request key in the index range of the schedule (`ValidKey`) is sent
  to the engine as the encoding of a typed width-3 CNF with at most `κ (S+1)` variables
  and at most `κ (S+1)` clauses, `κ` being the constant in the SAT-rate argument of the
  time bound. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

/-! ## Bit length of the written output coefficients -/
namespace QecReliability.TensorMachine.PhysicalAlgorithm
open RationalOutput TensorBernstein TensorLatent SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (solver : ∀ v, PrefixCNF.ExactSAT v 3) (B m : ℕ)
  (coins : CodeHash.BitTape (CodeHash.repeatBits
    (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m))

theorem bound_size (q B : ℕ) :
    (2*QecReliability.trialValueBound q B).size ≤ q+(4*B+1).size+1 := by
  apply Nat.size_le.mpr
  change 2*(2^q*(4*B+1)) < 2^(q+(4*B+1).size+1)
  calc
    _ < 2*(2^q*2^(4*B+1).size) :=
      Nat.mul_lt_mul_of_pos_left
        (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (by positivity)) (by omega)
    _ = _ := by
      rw [pow_add 2 (q+(4*B+1).size) 1, pow_add 2 q (4*B+1).size]
      ring

/-- Every entry of the actual output vector is a stored pair `num ≤ den` whose
denominator is at most `2 * 2^q * (4B+1)`, `q = keySize n ds.sum`. Repair only selects
among exact dyadic corner anchors, count ratios and the constants zero and one. -/
theorem outputVector_entry_bounds (j : Fin (slots ds-1+1)) :
    ((outputVector hD hd A rows C solver B m coins).get j).num ≤
      ((outputVector hD hd A rows C solver B m coins).get j).den ∧
    ((outputVector hD hd A rows C solver B m coins).get j).den ≤
      2*QecReliability.trialValueBound (keySize n ds.sum) B ∧
    ((outputVector hD hd A rows C solver B m coins).get j).num.size ≤
      keySize n ds.sum+(4*B+1).size+1 ∧
    ((outputVector hD hd A rows C solver B m coins).get j).den.size ≤
      keySize n ds.sum+(4*B+1).size+1 := by
  have hpos : 0 < QecReliability.trialValueBound (keySize n ds.sum) B := by
    unfold QecReliability.trialValueBound; positivity
  have h1 : 1 ≤ 2*QecReliability.trialValueBound (keySize n ds.sum) B := by omega
  have hden : ((outputVector hD hd A rows C solver B m coins).get j).den ≤
      2*QecReliability.trialValueBound (keySize n ds.sum) B := by
    rw [outputVector_get]
    unfold RationalTensorRepair.coefficient
    apply RationalPosetRepair.repair_property
      (fun x : Ratio => x.den ≤ 2*QecReliability.trialValueBound (keySize n ds.sum) B)
    · exact h1
    · exact h1
    · intro i _
      exact RationalOutput.dyadic_den_bound (r:=ds.sum) rows _ B
    · intro i _
      unfold RationalTensorConfidence.estimateRatios
      apply RationalOutput.Ratio.counts_den_le h1
      have hg := ((decisions hD hd A rows C solver) (true,i)).cachedMedian_bounds B m
        (CodeHash.repeatedSeedTapeEquiv _ _ m coins)
      have hb := ((decisions hD hd A rows C solver) (false,i)).cachedMedian_bounds B m
        (CodeHash.repeatedSeedTapeEquiv _ _ m coins)
      rw [← CachedAnswers.median_eq] at hg hb
      omega
  have hnum := ((outputVector hD hd A rows C solver B m coins).get j).num_le_den
  have hs := bound_size (keySize n ds.sum) B
  exact ⟨hnum, hden, (Nat.size_le_size (hnum.trans hden)).trans hs,
    (Nat.size_le_size hden).trans hs⟩

end QecReliability.TensorMachine.PhysicalAlgorithm

/-! ## Generic completion with call, query-size and time accounting -/
namespace QecReliability.TensorMachine.Runtime
open FL Assembly RationalOutput Final
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape QecPhysical QecPhysical.Stabilizer

private theorem overhead_split (k pre it it' post disp orc : ℕ) (hit : it ≤ it') :
    k*(pre+(disp+2)*it+orc+post+1) ≤ k*(pre+2*it'+post+1)*(disp+1)+k*orc := by
  have h1 : (disp+2)*it ≤ 2*it'*(disp+1) := by nlinarith
  have h2 : pre+post+1 ≤ (pre+post+1)*(disp+1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : pre+(disp+2)*it+orc+post+1 ≤ (pre+2*it'+post+1)*(disp+1)+orc := by nlinarith
  calc k*(pre+(disp+2)*it+orc+post+1) ≤ k*((pre+2*it'+post+1)*(disp+1)+orc) :=
        Nat.mul_le_mul_left k h3
    _ = _ := by ring

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent) (hT : Monotone T)

local notation "PP" => program hD hd A density
local notation "II" => indices hD hd A density
local notation "MACHINE" => theMachine E PP II

include hT in
/-- `bounded_completion` together with the accounting record of the run. `totals.calls`
is the number of SAT service calls of the source-level counting schedule (all operational
trials of all coefficients on both sides) against `ext`; `totals.oracleTime` is the
measured service time of those calls; `totals.dispatches` counts controller dispatches.
The machine time is bounded through these quantities. Every request key in the
schedule's index range is compiled to the encoding of a width-3 CNF of linear size. -/
theorem resource_completion : ∃ Ptime Pspace Pover : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool),
    let L := Boundary.resourceSize rows C a b c d
    let q := keySize n ds.sum
    let r := slots ds-1
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let ext := external hD hd A density spec (n:=n) (ds:=ds) rows C m coins
    let κ := Boundary.variableCoefficient density (data hD hd A).Cfixed
    let S := Boundary.satStructuralSize rows C
    let charge := Pt.eval (Boundary.extentPolynomial density (data hD hd A).Cfixed L)*T (κ*(S+1))
    ∃ (totals : Totals) (run : Completed MACHINE (input ds rows C a b c d (List.ofFn coins))),
      Outputs MACHINE run (outTape kE)
        (PhysicalAlgorithm.outputVector hD hd A (n:=n) (ds:=ds) rows C spec.service.solver B m coins) ∧
      run.time ≤ Ptime.eval L*(B+1)*(T (κ*(S+1))+1) ∧
      run.cells ≤ Pspace.eval L ∧
      totals.calls = CountingTrace.sideCalls q r B m ext true (List.finRange (r+1))+
        CountingTrace.sideCalls q r B m ext false (List.finRange (r+1)) ∧
      totals.calls ≤ 2*slots ds*(2*m+1)*trialCallCap q B ∧
      totals.calls ≤ 512*(L+1)^4*(B+1) ∧
      totals.oracleTime = CountingTrace.sideTime q r B m ext true (List.finRange (r+1))+
        CountingTrace.sideTime q r B m ext false (List.finRange (r+1)) ∧
      totals.oracleTime ≤ totals.calls*charge ∧
      totals.dispatches ≤ 8*totals.calls+2*slots ds*coefficientLocalBound q m+2*slots ds+3 ∧
      run.time ≤ Pover.eval L*(totals.dispatches+1)+(3*kE+6)*totals.oracleTime ∧
      (∀ key, ValidKey q r m key → ∃ req : SATRequest,
        (ext.compileQuery key).bits = QueryCodec.encode req ∧
        req.varCount ≤ κ*(S+1) ∧ req.formula.length ≤ κ*(S+1) ∧
        (ext.sat (ext.compileQuery key).bits).time ≤ charge) := by
  obtain ⟨P,hP⟩ := polynomial_completion hD hd A density spec
  obtain ⟨Ptot,htot⟩ := counting_bounds_of_totals hD hd A density spec hT
  obtain ⟨Poracle,horacleBound⟩ := structural_time_budget hD hd A density spec hT
  obtain ⟨Pcap,hcap⟩ := (Boundary.extentPolynomial_pb density (data hD hd A).Cfixed).envelope
  obtain ⟨Ptime,Pspace,hres⟩ := completion_resource_envelopes PP II ⟨P,P,P⟩ Pcap Ptot Poracle Ps kE
  have hover : PolyBounded (fun L => (3*kE+6)*(preBound PP II ⟨P,P,P⟩ L+
      2*(iterBound PP II ⟨P,P,P⟩ L+Ps.eval (Pcap.eval L)+1)+postBound PP II ⟨P,P,P⟩ L+1)) := by
    have hp := preBound_poly PP II ⟨P,P,P⟩
    have hb := iterBound_poly PP II ⟨P,P,P⟩
    have hz := postBound_poly PP II ⟨P,P,P⟩
    poly_bounded
  obtain ⟨Pover,hPover⟩ := hover.envelope
  refine ⟨Ptime,Pspace,Pover,?_⟩
  intro n ds rows C a b c d ha hc coins
  dsimp only
  obtain ⟨totals,run,hout,hcalls,horacle,hdispatch,htime,hspace⟩ :=
    hP (n:=n) (ds:=ds) rows C a b c d ha hc coins
  rw [Boundary.slots_pred_succ] at hdispatch
  obtain ⟨_,hdsp,_⟩ := htot (n:=n) (ds:=ds) rows C a b c d ha hc coins totals
    hcalls horacle hdispatch
  have horc := horacleBound (n:=n) (ds:=ds) rows C a b c d (rationalCellBudget a b) ha hc coins
  dsimp only at horc
  rw [← horacle] at horc
  have hi := (Boundary.input_caps rows C a b c d (data hD hd A).Cfixed density ha hc).2
  have hic := hi.trans ((Boundary.extentPolynomial_mono density (data hD hd A).Cfixed
    (Boundary.structuralSize_le_resource rows C a b c d)).trans (hcap _))
  have hr := hres (Boundary.resourceSize rows C a b c d) (rationalCellBudget a b)
    (T (Boundary.variableCoefficient density (data hD hd A).Cfixed*
      (Boundary.satStructuralSize rows C+1))) _ totals.dispatches totals.oracleTime hic hdsp horc
  -- per-request facts
  have hkey : ∀ key (valid : ValidKey (keySize n ds.sum) (slots ds-1)
      (rationalRepetitionBudget (2*slots ds) c d) key), ∃ req : SATRequest,
      ((external hD hd A density spec (n:=n) (ds:=ds) rows C
        (rationalRepetitionBudget (2*slots ds) c d) coins).compileQuery key).bits =
          QueryCodec.encode req ∧
      req.varCount ≤ Boundary.variableCoefficient density (data hD hd A).Cfixed*
        (Boundary.satStructuralSize rows C+1) ∧
      req.formula.length ≤ Boundary.variableCoefficient density (data hD hd A).Cfixed*
        (Boundary.satStructuralSize rows C+1) ∧
      ((external hD hd A density spec (n:=n) (ds:=ds) rows C
        (rationalRepetitionBudget (2*slots ds) c d) coins).sat
        ((external hD hd A density spec (n:=n) (ds:=ds) rows C
          (rationalRepetitionBudget (2*slots ds) c d) coins).compileQuery key).bits).time ≤
        Pt.eval (Boundary.extentPolynomial density (data hD hd A).Cfixed
          (Boundary.resourceSize rows C a b c d))*
        T (Boundary.variableCoefficient density (data hD hd A).Cfixed*
          (Boundary.satStructuralSize rows C+1)) := by
    intro key valid
    have hdim := Boundary.resolve_dimensions rows C (Factory.system hD hd A n ds).stages
      (Factory.circuits hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)
      (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)
        (rationalRepetitionBudget (2*slots ds) c d) coins) _
      (Factory.gates_all hD hd A n ds) key valid
    have hd2 := Boundary.resolve_caps rows C (Factory.system hD hd A n ds).stages
      (Factory.circuits hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)
      (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)
        (rationalRepetitionBudget (2*slots ds) c d) coins) density _
      (Factory.gates_all hD hd A n ds) key valid
    have hvar := Boundary.raw_input_variable_cap rows C (data hD hd A).Cfixed density
    dsimp only at hvar
    have hsize := (Boundary.input_caps rows C a b c d (data hD hd A).Cfixed density ha hc).2
    have hans := Boundary.answer rows C (Factory.system hD hd A n ds).stages
      (Factory.circuits hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)
      (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)
        (rationalRepetitionBudget (2*slots ds) c d) coins) density spec key valid
    have hpad := TensorQuery.Service.padded_dimensions density _ _ _ hdim.1 hdim.2
    have hpos := spec.positive_density_parameter
    refine ⟨padRequest density (Boundary.resolve rows C (Factory.system hD hd A n ds).stages
      (Factory.circuits hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)
      (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)
        (rationalRepetitionBudget (2*slots ds) c d) coins) key valid),
      Boundary.query_valid rows C _ _ _ _ density key valid, hd2.1.trans hvar, ?_, ?_⟩
    · exact hpad.2.trans ((Nat.le_mul_of_pos_left _ hpos).trans ((le_max_right _ _).trans hvar))
    · exact (congrArg SATReply.time hans).le.trans
        (spec.request_bounds hT _ _ _ (hd2.1.trans hvar)
          ((hd2.2.trans hsize).trans (Boundary.extentPolynomial_mono density _
            (Boundary.structuralSize_le_resource rows C a b c d)))).1
  -- calls
  have hc1 := Boundary.total_calls_le rows C (Factory.system hD hd A n ds).stages
    (Factory.circuits hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)
    (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)
      (rationalRepetitionBudget (2*slots ds) c d) coins) density spec (rationalCellBudget a b)
  have hc2 := Boundary.total_calls_input rows C (Factory.system hD hd A n ds).stages
    (Factory.circuits hD hd A n ds) spec a b c d (rationalCellBudget a b) ha hc
    (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)
      (rationalRepetitionBudget (2*slots ds) c d) coins)
  -- service time per call
  have hcharge : ∀ key, ValidKey (keySize n ds.sum) (slots ds-1)
      (rationalRepetitionBudget (2*slots ds) c d) key →
      ((external hD hd A density spec (n:=n) (ds:=ds) rows C
        (rationalRepetitionBudget (2*slots ds) c d) coins).sat
        ((external hD hd A density spec (n:=n) (ds:=ds) rows C
          (rationalRepetitionBudget (2*slots ds) c d) coins).compileQuery key).bits).time ≤
        Pt.eval (Boundary.extentPolynomial density (data hD hd A).Cfixed
          (Boundary.resourceSize rows C a b c d))*
        T (Boundary.variableCoefficient density (data hD hd A).Cfixed*
          (Boundary.satStructuralSize rows C+1)) := by
    intro key valid
    obtain ⟨_,_,_,_,h⟩ := hkey key valid
    exact h
  have hst := CountingTrace.side_time_le (keySize n ds.sum) (slots ds-1) (rationalCellBudget a b)
    (rationalRepetitionBudget (2*slots ds) c d)
    (external hD hd A density spec (n:=n) (ds:=ds) rows C
      (rationalRepetitionBudget (2*slots ds) c d) coins) _ hcharge true
    (List.finRange (slots ds-1+1))
  have hsf := CountingTrace.side_time_le (keySize n ds.sum) (slots ds-1) (rationalCellBudget a b)
    (rationalRepetitionBudget (2*slots ds) c d)
    (external hD hd A density spec (n:=n) (ds:=ds) rows C
      (rationalRepetitionBudget (2*slots ds) c d) coins) _ hcharge false
    (List.finRange (slots ds-1+1))
  have horacleCalls : totals.oracleTime ≤ totals.calls*
      (Pt.eval (Boundary.extentPolynomial density (data hD hd A).Cfixed
        (Boundary.resourceSize rows C a b c d))*
      T (Boundary.variableCoefficient density (data hD hd A).Cfixed*
        (Boundary.satStructuralSize rows C+1))) := by
    rw [horacle, hcalls, Nat.add_mul]
    exact Nat.add_le_add hst hsf
  -- machine time through the totals
  have hsplit := overhead_split (3*kE+6)
    (preBound PP II ⟨P,P,P⟩ (Boundary.resourceSize rows C a b c d))
    (iterBound PP II ⟨P,P,P⟩ (Boundary.resourceSize rows C a b c d)+
      Ps.eval (Boundary.extentCap rows C density ((data hD hd A).Cfixed*(keySize n ds.sum+1)))+1)
    (iterBound PP II ⟨P,P,P⟩ (Boundary.resourceSize rows C a b c d)+
      Ps.eval (Pcap.eval (Boundary.resourceSize rows C a b c d))+1)
    (postBound PP II ⟨P,P,P⟩ (Boundary.resourceSize rows C a b c d))
    totals.dispatches totals.oracleTime
    (Nat.add_le_add_right (Nat.add_le_add_left (Ps.monotone hic) _) 1)
  have htotal : run.time ≤ Pover.eval (Boundary.resourceSize rows C a b c d)*
      (totals.dispatches+1)+(3*kE+6)*totals.oracleTime :=
    htime.trans (hsplit.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (hPover (Boundary.resourceSize rows C a b c d))) _))
  refine ⟨totals,run,hout,htime.trans hr.1,hspace.trans hr.2,hcalls,?_,?_,horacle,horacleCalls,
    hdispatch,htotal,hkey⟩
  · rw [hcalls]; exact hc1
  · rw [hcalls]; exact hc2

end QecReliability.TensorMachine.Runtime

/-! ## The closed multiclass theorem with resource accounting -/
namespace QecReliability.TensorMachine.Runtime.FixedQuantum
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate RationalOutput Final
open QecPhysical QecPhysical.Stabilizer
open ExternalSATBridge TensorBernstein TensorLatent
open QecReliability.LatentMachine.Runtime.FixedQuantum

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => explicitCertificate

/-- `isotropic_tensor_machine_guarantee_strong` with resource accounting. Besides the
engine, rate constant and envelopes, the following are fixed before the input: the
polynomial `Pover` and the SAT envelopes `PtE, PsE` together with the proof `spec` that
the engine `E` decides every typed width-3 CNF request within
`PtE(extent) * T(variables)` steps, `T = runtimeEnvelope rateConstant`. On every coin
string, `ext` is the concrete query service of the development (`Runtime.external`):
it compiles each request key to query bits and answers them by running `E`.

* (R1) bit length: every entry of the output vector is `num/den` with `num ≤ den ≤
  2 * 2^q * (4B+1)`; hence `num` and `den` have at most `q + size(4B+1) + 1` bits.
* (R2) SAT calls: `totals.calls` is exactly `CountingTrace.sideCalls` summed over the
  good and bad sides, i.e. the number of `ext.sat` invocations performed by the
  source-level operational counting schedule (every repetition of every trial of every
  coefficient); it is at most `2 * slots ds * (2m+1) * trialCallCap q B` and at most
  `512 (L+1)^4 (B+1)`. `totals.oracleTime` is the summed service time of those calls,
  at most `calls * charge`; the machine run time is at most
  `Pover(L) * (dispatches+1) + (3 kE + 6) * oracleTime`, with dispatches linear in calls.
* (R3) query size: for every key in the schedule's index range (`ValidKey`; the time
  charge of `totals.oracleTime` is proved from exactly this range), the bits sent to
  the engine are the encoding of a request (a width-3 CNF by type) with at most
  `κ (S+1)` variables and at most `κ (S+1)` clauses, where `κ` is the same constant as
  in the SAT-rate argument of the time bound, and its service time is at most `charge`. -/
theorem isotropic_tensor_machine_guarantee_resources :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace Pover PtE PsE : PolynomialEnvelope),
    0<rateConstant ∧
    ∃ spec : ResourceEncodedSAT (PrimitiveTransport.machine (PrimitiveLink.queryMachine engine))
      1 PtE PsE (RateMajorant.runtimeEnvelope rateConstant) requestExtent,
    ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    Monotone (TensorEncoding.circuitMap C) →
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let f := multivariateCoefficients (rowSpace rows) (TensorEncoding.circuitMap C)
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n ds) (Factory.width HD HS CERT n ds) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    let q := keySize n ds.sum
    let r := slots ds-1
    let κ := Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed
    let S := Boundary.satStructuralSize rows C
    let rate := RateMajorant.runtimeEnvelope rateConstant (κ*(S+1))
    let charge := PtE.eval (Boundary.extentPolynomial 1 (data HD HS CERT).Cfixed L)*rate
    -- (a) the target is the Bernstein curve of `f`, and it is optimal over all recoveries
    (∀ p (hp : cube ds p),
      entanglementFidelity (lift.erasureFlagDecoder.comp
          (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map =
        curve ds f p ∧
      ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
        entanglementFidelity (Q.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map ≤
          entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map) ∧
    -- (b) every coin string: run, output, resources, structure, and resource accounting
    (∀ coins : Fin N → Bool,
      let ext := TensorMachine.Runtime.external HD HS CERT 1 spec (n:=n) (ds:=ds) rows C m coins
      ∃ (run : Completed M (input ds rows C a b c d (List.ofFn coins))) (v : Vector (slots ds-1))
        (totals : Totals),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(rate+1) ∧
        run.cells ≤ Pspace.eval L ∧
        lift.TensorPhysicalStructure (TensorEncoding.circuitMap C) (vectorCurve ds v) ∧
        Antitone (vectorTable ds v) ∧
        (∀ j, 0 ≤ vectorTable ds v j ∧ vectorTable ds v j ≤ 1) ∧
        (∀ b : Corner ds, vectorTable ds v (cornerIndex ds b) = f (cornerIndex ds b) ∧
          vectorTable ds v (cornerIndex ds b) =
            erasureScore (rowSpace rows) (TensorEncoding.circuitMap C (cornerCauses ds b))) ∧
        (∀ j, vectorTable ds v j = 1 ↔ f j = 1) ∧
        -- (R1) bit length of every output coefficient
        (∀ j, (v.get j).num ≤ (v.get j).den ∧
          (v.get j).den ≤ 2*QecReliability.trialValueBound q B ∧
          (v.get j).num.size ≤ q+(4*B+1).size+1 ∧
          (v.get j).den.size ≤ q+(4*B+1).size+1) ∧
        -- (R2) SAT calls of the source-level schedule, and their accounting in the run
        totals.calls = CountingTrace.sideCalls q r B m ext true (List.finRange (r+1))+
          CountingTrace.sideCalls q r B m ext false (List.finRange (r+1)) ∧
        totals.calls ≤ 2*slots ds*(2*m+1)*trialCallCap q B ∧
        totals.calls ≤ 512*(L+1)^4*(B+1) ∧
        totals.oracleTime = CountingTrace.sideTime q r B m ext true (List.finRange (r+1))+
          CountingTrace.sideTime q r B m ext false (List.finRange (r+1)) ∧
        totals.oracleTime ≤ totals.calls*charge ∧
        totals.dispatches ≤ 8*totals.calls+2*slots ds*coefficientLocalBound q m+2*slots ds+3 ∧
        run.time ≤ Pover.eval L*(totals.dispatches+1)+
          (3*(PrimitiveLink.queryMachine engine).tapeCount+6)*totals.oracleTime ∧
        -- (R3) size of every SAT query in the schedule's index range
        (∀ key, ValidKey q r m key → ∃ req : SATRequest,
          (ext.compileQuery key).bits = QueryCodec.encode req ∧
          req.varCount ≤ κ*(S+1) ∧ req.formula.length ≤ κ*(S+1) ∧
          (ext.sat (ext.compileQuery key).bits).time ≤ charge)) ∧
    -- (c) one coin event gives two-tail accuracy on the whole parameter cube
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input ds rows C a b c d (List.ofFn coins)))
        (v : Vector (slots ds-1)), Outputs M run outputTape v →
          lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b) (vectorCurve ds v)) := by
  obtain ⟨engine,PtE,PsE,rateConstant,hrate,spec,hT⟩ := ConcreteSolver.exists_resource_machine
  obtain ⟨Ptime,Pspace,Pover,hres⟩ := resource_completion HD HS CERT 1 spec hT
  obtain ⟨_,_,hclosed⟩ := tensor_machine_guarantee HD HS CERT 1 spec hT
  refine ⟨engine,rateConstant,Ptime,Pspace,Pover,PtE,PsE,hrate,spec,?_⟩
  intro n ds rows C a b c d ha hab hc hd hS hC
  obtain ⟨_,hshape,hprob⟩ := hclosed (n:=n) (ds:=ds) rows C a b c d ha hab hc hd
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS) hC
  refine ⟨?_,?_,hprob⟩
  · intro p hp
    have h := (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).multivariateLatentErasure_optimum
      (TensorEncoding.circuitMap C) p hp
    refine ⟨h.1, fun Q => ?_⟩
    rw [h.1]
    exact h.2 Q
  · intro coins
    dsimp only
    obtain ⟨totals,run,hout,htime,hspace,hcalls,hc1,hc2,horacle,horc,hdisp,htotal,hkey⟩ :=
      hres (n:=n) (ds:=ds) rows C a b c d ha hc coins
    obtain ⟨h1,h2,h3,h4⟩ := PhysicalAlgorithm.outputVector_table_structure HD HS CERT rows C
      spec.service.solver (rationalCellBudget a b) (rationalRepetitionBudget (2*slots ds) c d) coins
      (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS) hC
    exact ⟨run,_,totals,hout,htime,hspace,hshape coins run _ hout,h1,h2,h3,h4,
      fun j => PhysicalAlgorithm.outputVector_entry_bounds HD HS CERT rows C spec.service.solver
        (rationalCellBudget a b) (rationalRepetitionBudget (2*slots ds) c d) coins j,
      hcalls,hc1,hc2,horacle,horc,hdisp,htotal,hkey⟩

end QecReliability.TensorMachine.Runtime.FixedQuantum

/-! ## The iid specialisation with resource accounting -/
namespace QecReliability.IidErasure
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate RationalOutput Final
open QecPhysical QecPhysical.Stabilizer
open ExternalSATBridge TensorBernstein TensorLatent
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open QecReliability.LatentMachine.Runtime.FixedQuantum
open QecReliability.TensorMachine.Runtime.FixedQuantum

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => explicitCertificate

theorem slots_single (n : ℕ) : slots [n] = n+1 := by
  simp only [slots, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem keySize_single (n : ℕ) : keySize n [n].sum = 3*n := by
  simp only [List.sum_cons, List.sum_nil, add_zero]
  unfold keySize
  omega

/-- `iid_erasure_machine_guarantee` with resource accounting (see
`isotropic_tensor_machine_guarantee_resources`). With `ds = [n]`: every written
coefficient `f̂ j`, stored as the pair `v.get (slot n j)`, has numerator and denominator
of at most `3n + size(4B+1) + 1` bits; the source-level schedule makes exactly
`totals.calls` SAT calls, at most `2 (n+1) (2m+1) trialCallCap (3n) B` and at most
`512 (L+1)^4 (B+1)`; every query in the schedule's index range is a width-3 CNF with at
most `κ (S+1)` variables and clauses, `S = satStructuralSize rows (iidProgram n)`. -/
theorem iid_erasure_machine_guarantee_resources :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace Pover PtE PsE : PolynomialEnvelope),
    0<rateConstant ∧
    ∃ spec : ResourceEncodedSAT (PrimitiveTransport.machine (PrimitiveLink.queryMachine engine))
      1 PtE PsE (RateMajorant.runtimeEnvelope rateConstant) requestExtent,
    ∀ {n : ℕ}
    (rows : List (List (PauliCoord n))) (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let C := iidProgram n
    let F := fun (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) =>
      entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map
    let f := layerAverage (id : Causes n → Finset (Fin n)) (erasureScore (rowSpace rows))
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots [n]) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n [n])
      (Factory.width HD HS CERT n [n]) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    let q := keySize n [n].sum
    let r := slots [n]-1
    let κ := Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed
    let S := Boundary.satStructuralSize rows C
    let rate := RateMajorant.runtimeEnvelope rateConstant (κ*(S+1))
    let charge := PtE.eval (Boundary.extentPolynomial 1 (data HD HS CERT).Cfixed L)*rate
    -- (i) `F` is optimal over all recoveries and is the Bernstein curve of `f`
    (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      F p hp = bernsteinCurve n f p ∧
      ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
        entanglementFidelity (Q.comp
          (lift.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map ≤ F p hp) ∧
    -- (ii) every coin string
    (∀ coins : Fin N → Bool,
      let ext := TensorMachine.Runtime.external HD HS CERT 1 spec (n:=n) (ds:=[n]) rows C m coins
      ∃ (run : Completed M (input [n] rows C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)) (totals : Totals),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(rate+1) ∧
        run.cells ≤ Pspace.eval L ∧
        Antitone (coefficients v) ∧
        (∀ j, 0 ≤ coefficients v j ∧ coefficients v j ≤ 1) ∧
        coefficients v 0 = 1 ∧
        coefficients v (Fin.last n) = F 1 ⟨zero_le_one, le_rfl⟩ ∧
        coefficients v (Fin.last n) = erasureScore (rowSpace rows) Finset.univ ∧
        coefficients v (Fin.last n) = ((4:ℝ) ^ (n - Module.finrank Bit (rowSpace rows)))⁻¹ ∧
        (∀ j, coefficients v j = 1 ↔ f j = 1) ∧
        -- (R1) bit length of every output coefficient `f̂ j`
        (∀ j : Fin (n+1), (v.get (slot n j)).num ≤ (v.get (slot n j)).den ∧
          (v.get (slot n j)).den ≤ 2*QecReliability.trialValueBound (3*n) B ∧
          (v.get (slot n j)).num.size ≤ 3*n+(4*B+1).size+1 ∧
          (v.get (slot n j)).den.size ≤ 3*n+(4*B+1).size+1) ∧
        -- (R2) SAT calls of the source-level schedule, and their accounting in the run
        totals.calls = CountingTrace.sideCalls q r B m ext true (List.finRange (r+1))+
          CountingTrace.sideCalls q r B m ext false (List.finRange (r+1)) ∧
        totals.calls ≤ 2*(n+1)*(2*m+1)*trialCallCap (3*n) B ∧
        totals.calls ≤ 512*(L+1)^4*(B+1) ∧
        totals.oracleTime = CountingTrace.sideTime q r B m ext true (List.finRange (r+1))+
          CountingTrace.sideTime q r B m ext false (List.finRange (r+1)) ∧
        totals.oracleTime ≤ totals.calls*charge ∧
        run.time ≤ Pover.eval L*(totals.dispatches+1)+
          (3*(PrimitiveLink.queryMachine engine).tapeCount+6)*totals.oracleTime ∧
        totals.dispatches ≤ 8*totals.calls+2*(n+1)*coefficientLocalBound (3*n) m+2*(n+1)+3 ∧
        -- (R3) size of every SAT query in the schedule's index range
        (∀ key, ValidKey q r m key → ∃ req : SATRequest,
          (ext.compileQuery key).bits = QueryCodec.encode req ∧
          req.varCount ≤ κ*(S+1) ∧ req.formula.length ≤ κ*(S+1) ∧
          (ext.sat (ext.compileQuery key).bits).time ≤ charge)) ∧
    -- (iii) one coin event: both relative tails for every `p ∈ [0,1]` simultaneously
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input [n] rows C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)), Outputs M run outputTape v →
          ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
            RelPair ((a:ℝ)/b) (F p hp) (bernsteinCurve n (coefficients v) p)) := by
  obtain ⟨engine,rateConstant,Ptime,Pspace,Pover,PtE,PsE,hrate,spec,hclosed⟩ :=
    isotropic_tensor_machine_guarantee_resources
  refine ⟨engine,rateConstant,Ptime,Pspace,Pover,PtE,PsE,hrate,spec,?_⟩
  intro n rows a b c d ha hab hc hd hS
  obtain ⟨_,hruns,hprob⟩ := hclosed (n:=n) (ds:=[n]) rows (iidProgram n) a b c d ha hab hc hd hS
    (iidProgram_monotone n)
  have hopt := fun p (hp : p ∈ Set.Icc (0:ℝ) 1) =>
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).iidLatentErasure_optimum
      (id : Causes n → Finset (Fin n)) p hp.1 hp.2
  have hend := (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).iidLatentErasure_endpoints
    (id : Causes n → Finset (Fin n))
  refine ⟨?_,?_,?_⟩
  · intro p hp
    exact ⟨(hopt p hp).1, fun Q => ((hopt p hp).2 Q).trans (hopt p hp).1.symm.le⟩
  · intro coins
    dsimp only
    obtain ⟨run,v,totals,hout,htime,hspace,_,hanti,hrange,hcorner,hone,hbits,
      hcalls,hc1,hc2,horacle,horc,hdisp,htotal,hkey⟩ := hruns coins
    have hlast : coefficients v (Fin.last n) = erasureScore (rowSpace rows) Finset.univ := by
      have h := (hcorner (true, PUnit.unit)).2
      change vectorTable [n] v (Fin.last n, PUnit.unit) =
        erasureScore (rowSpace rows)
          (TensorEncoding.circuitMap (iidProgram n) (Finset.univ, PUnit.unit)) at h
      rw [vectorTable_single, iidProgram_map] at h
      exact h
    have hq := keySize_single n
    refine ⟨run,v,totals,hout,htime,hspace,?_,?_,?_,?_,hlast,?_,?_,?_,hcalls,?_,hc2,horacle,horc,
      htotal,?_,hkey⟩
    · intro i j hij
      have h := hanti (show ((i, PUnit.unit) : Grid [n]) ≤ (j, PUnit.unit) from ⟨hij, le_rfl⟩)
      rw [vectorTable_single, vectorTable_single] at h
      exact h
    · intro j
      have h := hrange (j, PUnit.unit)
      rw [vectorTable_single] at h
      exact h
    · have h := (hcorner (false, PUnit.unit)).2
      change vectorTable [n] v (⟨0, Nat.zero_lt_succ n⟩, PUnit.unit) =
        erasureScore (rowSpace rows)
          (TensorEncoding.circuitMap (iidProgram n) (∅, PUnit.unit)) at h
      rw [vectorTable_single, iidProgram_map] at h
      have e : (0 : Fin (n+1)) = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext (by simp)
      rw [e, h]
      exact score_empty _
    · rw [hlast]
      exact hend.2.symm
    · rw [hlast]
      exact score_full (rowSpace rows) hS
    · intro j
      have h := hone (j, PUnit.unit)
      rw [vectorTable_single, coefficients_single] at h
      exact h
    · intro j
      have h := hbits (slot n j)
      rw [hq] at h
      exact h
    · exact hc1.trans (le_of_eq (by rw [hq, slots_single]))
    · exact hdisp.trans (le_of_eq (by rw [hq, slots_single]))
  · apply hprob.trans
    apply FiniteProbability.prob_mono
    intro coins hgood run v hv p hp
    have h := hgood run v hv (p, PUnit.unit) ⟨hp, trivial⟩
    rw [vectorCurve_single, fidelity_single _ p hp] at h
    exact h

end QecReliability.IidErasure

#print axioms QecReliability.TensorMachine.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_resources
#print axioms QecReliability.IidErasure.iid_erasure_machine_guarantee_resources
