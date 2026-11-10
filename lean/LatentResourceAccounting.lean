import FixedQuantumClosure
import PhysicalBridge.CachedCoefficients
import PhysicalBridge.RationalOutputStorage

/-! Coefficient-level structure and resource accounting for the closed latent-circuit
machine theorem `isotropic_polynomial_endpoint_machine_guarantee`.

The latent machine writes `endpointVector rows C cache`, where `cache` is the
once-prepared SAT count table (`SharedCircuit.ConcreteQuantum.prepare`): the two end
coefficients are the exact dyadic scores, and every interior coefficient is the count
ratio `Â_j / (Â_j + B̂_j)`. No shape repair is applied (the machine runs with
`shape = false`), so no monotonicity of the coefficient vector is asserted.

`isotropic_latent_machine_guarantee_resources` adds to every conclusion of
`isotropic_polynomial_endpoint_machine_guarantee`:

* coefficient level, on every coin string: the output equals `endpointVector` of the
  cache; `f̂_j := (v.get j).value` lies in `(0,1]`; `f̂_0` and `f̂_r` are the exact
  physical scores `2^{-d_{C(0^r)}}`, `2^{-d_{C(1^r)}}` (equal to `f_0`, `f_r`); and
  `f̂_j = 1 ↔ f_j = 1` for every `j`, where `f = layerAverage (circuitMap C) score`
  is the true coefficient vector of the target Bernstein curve;
* (R1) bit length: `num ≤ den ≤ 2 * 2^q * (4B+1)`, so both have at most
  `q + size(4B+1) + 1` bits, `q = keySize n r = r + 2n`;
* (R2) SAT calls: the cache makes at most `2(r+1)(2m+1) trialCallBound q B` calls,
  with explicit bounds `B ≤ 144 ⌈b/a⌉^2` and `2m+1 ≤ 2(size(2r+1) + size(⌈d/c⌉-1)) + 1`;
  for `r > 0` the controller's macro trace against the concrete external service `ext`
  makes exactly `cache.calls` calls, its measured SAT time is that of the measured
  preparation and is at most `2(r+1)(2m+1) trialCallBound q B * charge`, and the run
  time is at most `Pover(L) (macroDispatchBound + 1) + (3 kE + 6) oracleTime`;
* (R3) query size, for `r > 0`: every request key in the schedule's index range is sent
  to the engine as the encoding of a typed width-3 CNF with at most `κ (S+1)` variables
  and at most `κ (S+1)` clauses, `κ, S` being the constant and structural extent of the
  SAT-rate argument of the time bound, and its service time is at most `charge`. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

/-! ## The coefficients written by the latent machine -/
namespace QecReliability.LatentCoefficients
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput

theorem layerAverage_score_pos {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) :
    0 < layerAverage C (score S) j := by
  classical
  have hc : 0 < Fintype.card {b : Causes r // hammingLayer b = j} := by
    rw [← Nat.card_eq_fintype_card, hamming_layer_card]
    exact Nat.choose_pos (Nat.le_of_lt_succ j.isLt)
  have : Nonempty {b : Causes r // hammingLayer b = j} := Fintype.card_pos_iff.mp hc
  unfold layerAverage
  apply div_pos
  · exact Finset.sum_pos (fun b _ => (score_range S (C b)).1) Finset.univ_nonempty
  · exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt)

theorem layer_range {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) :
    ∀ j, 0 < layerAverage C (score S) j ∧ layerAverage C (score S) j ≤ 1 := fun j =>
  ⟨layerAverage_score_pos S C j,
    (layerAverage_range C _ (fun E => ⟨(score_range S E).1.le, (score_range S E).2⟩) j).2⟩

theorem layerAverage_eq_counts {n r : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) :
    layerAverage C (score S) j =
      (goodCoefficient S C j : ℝ) / ((goodCoefficient S C j : ℝ) + badCoefficient S C j) := by
  rw [← Nat.cast_add, coefficient_partition, Nat.cast_mul]
  exact (good_coefficient_normalized S hS C j).symm

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)

/-- The cached count ratio is positive, and it equals one exactly when the true
coefficient does, on every seed. -/
theorem prepare_ratio (hS : rowSpace rows ≤ normalizer (F := Bit) (symplectic n) (rowSpace rows))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Fin (r+1)) :
    0 < (prepare rows C H K solver B m ω).ratio j ∧
    ((prepare rows C H K solver B m ω).ratio j = 1 ↔
      layerAverage (circuitMap C) (score (rowSpace rows)) j = 1) := by
  set T := prepare rows C H K solver B m ω with hT
  have hg0 := T.value_nonneg (true,j)
  have hb0 := T.value_nonneg (false,j)
  have hcg : (coefficientModels (rowSpace rows) (circuitMap C) (true,j)).card =
      goodCoefficient (rowSpace rows) (circuitMap C) j := by
    simp only [coefficientModels_card, ↓reduceIte]
  have hcb : (coefficientModels (rowSpace rows) (circuitMap C) (false,j)).card =
      badCoefficient (rowSpace rows) (circuitMap C) j := by
    simp only [coefficientModels_card, Bool.false_eq_true, ↓reduceIte]
  have hf := layerAverage_eq_counts (rowSpace rows) hS (circuitMap C) j
  have hfpos := layerAverage_score_pos (rowSpace rows) (circuitMap C) j
  have htot := coefficient_total_pos (rowSpace rows) (circuitMap C) j
  have hG : goodCoefficient (rowSpace rows) (circuitMap C) j ≠ 0 := by
    intro h0
    rw [hf, h0] at hfpos
    simp at hfpos
  have hgpos : 0 < T.value (true,j) := by
    rcases lt_or_eq_of_le hg0 with h | h
    · exact h
    · exact absurd (hcg.symm.trans
        ((prepare_value_zero_iff rows C H K solver B m ω (true,j)).mp h.symm)) hG
  have hratio : T.ratio j = T.value (true,j) / (T.value (true,j) + T.value (false,j)) := rfl
  refine ⟨?_, ?_⟩
  · rw [hratio]
    exact div_pos hgpos (by linarith)
  · rw [hratio, div_eq_one_iff_eq (by linarith), hf, div_eq_one_iff_eq htot.ne']
    have hGpos : (0:ℝ) < goodCoefficient (rowSpace rows) (circuitMap C) j := by
      exact_mod_cast Nat.pos_of_ne_zero hG
    constructor
    · intro h
      have hb : T.value (false,j) = 0 := by linarith
      have hcard := (prepare_value_zero_iff rows C H K solver B m ω (false,j)).mp hb
      rw [hcb] at hcard
      rw [hcard]
      simp
    · intro h
      have hbad : (badCoefficient (rowSpace rows) (circuitMap C) j : ℝ) = 0 := by linarith
      have hbad' : badCoefficient (rowSpace rows) (circuitMap C) j = 0 := by exact_mod_cast hbad
      have hb := (prepare_value_zero_iff rows C H K solver B m ω (false,j)).mpr (hcb.trans hbad')
      linarith

theorem endpointVector_value (T : CoefficientTable r) (j : Fin (r+1)) :
    ((endpointVector rows C T).get j).value =
      if j.val = 0 then score (rowSpace rows) (circuitMap C ∅)
      else if j.val = r then score (rowSpace rows) (circuitMap C Finset.univ)
      else T.ratio j := by
  simp only [endpointVector, Vector.get_build, endpointEntry_value, Ratio.dyadic_value,
    endpointInput, extendCoefficients_at]

/-- Deterministic structure of the coefficient vector written by the latent machine,
on every seed. `f` is the true coefficient vector of the target Bernstein curve. -/
theorem endpoint_coefficients
    (hS : rowSpace rows ≤ normalizer (F := Bit) (symplectic n) (rowSpace rows))
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    let v := endpointVector rows C (prepare rows C H K solver B m ω)
    let f := layerAverage (circuitMap C) (score (rowSpace rows))
    (∀ j, 0 < f j ∧ f j ≤ 1) ∧
    (∀ j, 0 < (v.get j).value ∧ (v.get j).value ≤ 1) ∧
    (v.get 0).value = f 0 ∧
    (v.get 0).value = score (rowSpace rows) (circuitMap C ∅) ∧
    (v.get (Fin.last r)).value = f (Fin.last r) ∧
    (v.get (Fin.last r)).value = score (rowSpace rows) (circuitMap C Finset.univ) ∧
    (∀ j, (v.get j).value = 1 ↔ f j = 1) := by
  intro v f
  have hf0 : f 0 = score (rowSpace rows) (circuitMap C ∅) := layerAverage_fin_zero _ _
  have hfr : f (Fin.last r) = score (rowSpace rows) (circuitMap C Finset.univ) :=
    layerAverage_fin_last _ _
  have hv0 : (v.get 0).value = score (rowSpace rows) (circuitMap C ∅) := by
    simp only [v, endpointVector_value]
    simp
  have hvr : (v.get (Fin.last r)).value = score (rowSpace rows) (circuitMap C Finset.univ) := by
    simp only [v, endpointVector_value, Fin.val_last]
    by_cases hr : r = 0
    · subst hr
      have he : (Finset.univ : Finset (Fin 0)) = ∅ := rfl
      simp
    · simp [hr]
  -- every coordinate is either an exact endpoint or an interior count ratio
  have hcase : ∀ j : Fin (r+1), (j = 0 ∧ (v.get j).value = f j) ∨
      (j = Fin.last r ∧ (v.get j).value = f j) ∨
      (v.get j).value = (prepare rows C H K solver B m ω).ratio j := by
    intro j
    by_cases h0 : j.val = 0
    · have hj : j = 0 := Fin.ext h0
      subst hj
      exact Or.inl ⟨rfl, hv0.trans hf0.symm⟩
    · by_cases hr : j.val = r
      · have hj : j = Fin.last r := Fin.ext hr
        subst hj
        exact Or.inr (Or.inl ⟨rfl, hvr.trans hfr.symm⟩)
      · refine Or.inr (Or.inr ?_)
        simp only [v, endpointVector_value, h0, hr, ↓reduceIte]
  have hfrange : ∀ j, 0 < f j ∧ f j ≤ 1 := layer_range _ _
  refine ⟨hfrange, ?_, hv0.trans hf0.symm, hv0, hvr.trans hfr.symm, hvr, ?_⟩
  · intro j
    refine ⟨?_, (Ratio.value_range _).2⟩
    rcases hcase j with ⟨_, h⟩ | ⟨_, h⟩ | h
    · rw [h]; exact (hfrange j).1
    · rw [h]; exact (hfrange j).1
    · rw [h]; exact (prepare_ratio rows C H K solver hS B m ω j).1
  · intro j
    rcases hcase j with ⟨_, h⟩ | ⟨_, h⟩ | h
    · rw [h]
    · rw [h]
    · rw [h]; exact (prepare_ratio rows C H K solver hS B m ω j).2

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

/-- (R1) Every written coefficient is a stored pair `num ≤ den ≤ 2 * 2^q * (4B+1)`. -/
theorem endpoint_entry_bounds (B m : ℕ) (ω : Fin (2*m+1) → Ω) (j : Fin (r+1)) :
    ((endpointVector rows C (prepare rows C H K solver B m ω)).get j).num ≤
      ((endpointVector rows C (prepare rows C H K solver B m ω)).get j).den ∧
    ((endpointVector rows C (prepare rows C H K solver B m ω)).get j).den ≤
      2*QecReliability.trialValueBound (keySize n r) B ∧
    ((endpointVector rows C (prepare rows C H K solver B m ω)).get j).num.size ≤
      keySize n r+(4*B+1).size+1 ∧
    ((endpointVector rows C (prepare rows C H K solver B m ω)).get j).den.size ≤
      keySize n r+(4*B+1).size+1 := by
  have hden := (vector_den_bound rows C _ (prepare_count_bounds rows C H K solver B m ω)).1 j
  have hnum := ((endpointVector rows C (prepare rows C H K solver B m ω)).get j).num_le_den
  have hs := bound_size (keySize n r) B
  exact ⟨hnum, hden, (Nat.size_le_size (hnum.trans hden)).trans hs,
    (Nat.size_le_size hden).trans hs⟩

/-- Explicit value bounds for the two budgets (the statements of
`PhysicalBridge.ValueParameterBounds`, which is not part of this graph). -/
theorem cellBudget_value_bound {a b : ℕ} (ha : 0 < a) :
    rationalCellBudget a b ≤ 144 * (ceilDiv b a) ^ 2 := by
  have hb : b ≤ a * ceilDiv b a := ceilDiv_spec ha
  have hs := Nat.mul_le_mul hb hb
  unfold rationalCellBudget
  apply (ceilDiv_le_iff (show 0 < a * a by positivity)).mpr
  calc
    144 * b * b = 144 * (b * b) := by ring
    _ ≤ 144 * ((a * ceilDiv b a) * (a * ceilDiv b a)) :=
      Nat.mul_le_mul_left 144 hs
    _ = a * a * (144 * (ceilDiv b a) ^ 2) := by ring

theorem repetitionBudget_value_bound {K c d : ℕ} (hK : 0 < K) (hc : 0 < c) (hd : 0 < d) :
    2 * rationalRepetitionBudget K c d + 1 ≤ 2 * ((K - 1).size + (ceilDiv d c - 1).size) + 1 := by
  have hz : 0 < rationalRepetitionTarget K c d := ceilDiv_pos (by positivity) hc
  have hk : K ≤ 2 ^ (K - 1).size := (size_pred_le_iff hK).mp le_rfl
  have hv : d ≤ c * 2 ^ (ceilDiv d c - 1).size := by
    have h : ceilDiv d c ≤ 2 ^ (ceilDiv d c - 1).size :=
      (size_pred_le_iff (ceilDiv_pos hd hc)).mp le_rfl
    exact (ceilDiv_le_iff hc).mp h
  have hproduct : K * d ≤ c * 2 ^ ((K - 1).size + (ceilDiv d c - 1).size) := by
    calc
      K * d ≤ K * (c * 2 ^ (ceilDiv d c - 1).size) := Nat.mul_le_mul_left K hv
      _ ≤ 2 ^ (K - 1).size * (c * 2 ^ (ceilDiv d c - 1).size) := Nat.mul_le_mul_right _ hk
      _ = c * 2 ^ ((K - 1).size + (ceilDiv d c - 1).size) := by rw [pow_add]; ring
  have ht : rationalRepetitionTarget K c d ≤ 2 ^ ((K - 1).size + (ceilDiv d c - 1).size) :=
    (ceilDiv_le_iff hc).mpr hproduct
  have hs : (rationalRepetitionTarget K c d - 1).size ≤ (K - 1).size + (ceilDiv d c - 1).size :=
    (size_pred_le_iff hz).mpr ht
  unfold rationalRepetitionBudget
  omega

end QecReliability.LatentCoefficients

/-! ## The closed latent theorem with coefficient structure and resource accounting -/
namespace QecReliability.LatentMachine.Runtime.FixedQuantum
open scoped Classical
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open RationalOutput QecPhysical QecPhysical.Stabilizer
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence
open ExternalSATBridge

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => fixedCertificate

/-- `isotropic_polynomial_endpoint_machine_guarantee` with the coefficient-level
structure of the written vector and resource accounting. Fixed before all inputs: the
engine, the rate constant, the envelopes `Pspace, Ptime, Pover, PtE, PsE`, and the proof
`spec` that the engine decides every typed width-3 request within
`PtE(extent) * T(variables)` steps, `T = runtimeEnvelope rateConstant`. -/
theorem isotropic_latent_machine_guarantee_resources :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Pspace Ptime Pover PtE PsE : PolynomialEnvelope),
    0 < rateConstant ∧
    ∃ spec : ResourceEncodedSAT (PrimitiveTransport.machine (PrimitiveLink.queryMachine engine))
      1 PtE PsE (RateMajorant.runtimeEnvelope rateConstant) requestExtent,
    ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let f := layerAverage (circuitMap C) (score (rowSpace rows))
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let N := CodeHash.repeatBits
      (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) assemblyIndices
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    let q := keySize n r
    let G := gateConstant HD HS CERT
    let κ := InputEncoding.queryVariableCoeff G 1
    let S := satExtent rows C
    let rate := RateMajorant.runtimeEnvelope rateConstant (κ*(S+1))
    let timeBound := Ptime.eval L*(b/a+1)^2*(rate+1)
    let charge := PtE.eval (InputEncoding.queryExtentPolynomial G 1 L)*rate
    PhysicalTargetOptimality rows C lift ∧
    -- the target is the Bernstein curve of the true coefficient vector `f`
    (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map = bernsteinCurve r f p) ∧
    (∀ j, 0 < f j ∧ f j ≤ 1) ∧
    -- explicit budgets: B = O(ε⁻²), 2m+1 = O(log(2(r+1)/δ))
    B ≤ 144*(ceilDiv b a)^2 ∧
    2*m+1 ≤ 2*((2*(r+1)-1).size+(ceilDiv d c-1).size)+1 ∧
    (∀ w : Fin N → Bool,
      let seeds := decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r) m w
      let Hh := actualCodeHash (Factory.system HD HS CERT n r)
      let Kc := Factory.circuits HD HS CERT n r
      let cache := SharedCircuit.ConcreteQuantum.prepare rows C Hh Kc spec.service.solver B m seeds
      let ext := resourceExternal HD HS CERT 1 spec rows C m w
      ∃ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
        Final.Outputs M run outputTape v ∧
        run.time ≤ timeBound ∧ run.cells ≤ Pspace.eval L ∧
        EndpointStructure (rowSpace rows) (circuitMap C) v.curve ∧
        (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
          TailExact (entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map) (v.curve p)) ∧
        -- (a) coefficient level: `f̂_j = (v.get j).value`
        v = endpointVector rows C cache ∧
        v.curve = bernsteinCurve r (fun j => (v.get j).value) ∧
        (∀ j, 0 < (v.get j).value ∧ (v.get j).value ≤ 1) ∧
        (v.get 0).value = f 0 ∧
        (v.get 0).value = score (rowSpace rows) (circuitMap C ∅) ∧
        (v.get (Fin.last r)).value = f (Fin.last r) ∧
        (v.get (Fin.last r)).value = score (rowSpace rows) (circuitMap C Finset.univ) ∧
        (∀ j, (v.get j).value = 1 ↔ f j = 1) ∧
        -- (R1) bit length of every output coefficient
        (∀ j, (v.get j).num ≤ (v.get j).den ∧
          (v.get j).den ≤ 2*QecReliability.trialValueBound q B ∧
          (v.get j).num.size ≤ q+(4*B+1).size+1 ∧
          (v.get j).den.size ≤ q+(4*B+1).size+1) ∧
        -- (R2) SAT calls of the cache, and their accounting in the run
        cache.calls ≤ 2*(r+1)*(2*m+1)*trialCallBound q B ∧
        (0 < r → ∃ totals final events,
          OracleCost.WholeWrapperCandidate.Trace q r B m false ext
            (OracleCost.WholeWrapperCandidate.initial q r m) totals events final ∧
          totals.calls = cache.calls ∧
          totals.calls ≤ totalCallCap q r B m ∧
          totals.oracleTime =
            (QuantumService.prepareMeasured rows C Hh Kc spec.service B m seeds).oracleTime ∧
          totals.oracleTime ≤ 2*(r+1)*(2*m+1)*trialCallBound q B*charge ∧
          totals.dispatches ≤ macroDispatchBound q r B m ∧
          run.time ≤ Pover.eval L*(macroDispatchBound q r B m+1)+
            (3*(PrimitiveLink.queryMachine engine).tapeCount+6)*totals.oracleTime) ∧
        -- (R3) size of every SAT query in the schedule's index range
        (0 < r → ∀ key, ValidKey q r m key → ∃ req : SATRequest,
          (ext.compileQuery key).bits = QueryCodec.encode req ∧
          req.varCount ≤ κ*(S+1) ∧ req.formula.length ≤ κ*(S+1) ∧
          (ext.sat (ext.compileQuery key).bits).time ≤ charge)) ∧
    (1-(c:ℝ)/d)*(2:ℝ)^N ≤
      ((Finset.univ.filter (fun w : Fin N → Bool =>
        ∀ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
          Final.Outputs M run outputTape v →
          lift.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b) v.curve)).card : ℝ) := by
  obtain ⟨engine, PtE, PsE, rateConstant, hrate, spec, hT⟩ :=
    ConcreteSolver.exists_resource_machine
  obtain ⟨Pspace, Ptime, hclosed⟩ := polynomial_endpoint_machine_guarantee HD HS CERT 1 spec hT
  obtain ⟨_, _, hR⟩ := uniform_run_refinement HD HS CERT 1 spec hT
  obtain ⟨_, Pover, hpos⟩ := positive_machine_execution HD HS CERT 1 spec
  obtain ⟨_, _, hreg⟩ := positive_register_execution HD HS CERT 1 spec
  refine ⟨engine, rateConstant, Pspace, Ptime, Pover, PtE, PsE, hrate, spec, ?_⟩
  intro n r rows C a b c d ha hab hc hd hS
  obtain ⟨hopt, hruns, hprob⟩ := hclosed rows C a b c d ha hab hc hd
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS)
  have hfr := LatentCoefficients.layer_range (rowSpace rows) (circuitMap C)
  refine ⟨hopt, ?_, hfr, LatentCoefficients.cellBudget_value_bound ha,
    LatentCoefficients.repetitionBudget_value_bound (by omega) hc hd, ?_, hprob⟩
  · intro p hp
    rw [(hopt p hp).1, latentCurve_eq_bernstein]
  · intro w
    dsimp only
    obtain ⟨run, v, hout, htime, hspace, hend, htails⟩ := hruns w
    have hv := (hR rows C a b c d ha hc).2 w run v hout
    have hsem : semanticOutput rows C (actualCodeHash (Factory.system HD HS CERT n r))
        (Factory.circuits HD HS CERT n r) spec.service.solver a b c d
        (decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r)
          (rationalRepetitionBudget (2*(r+1)) c d) w) =
        endpointVector rows C (SharedCircuit.ConcreteQuantum.prepare rows C
          (actualCodeHash (Factory.system HD HS CERT n r)) (Factory.circuits HD HS CERT n r)
          spec.service.solver (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d)
          (decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r)
            (rationalRepetitionBudget (2*(r+1)) c d) w)) := by
      unfold semanticOutput
      rw [LinearRepair.prepare_coefficients]
      rfl
    rw [hsem] at hv
    obtain ⟨_, hrange, h0, h0s, hl, hls, hone⟩ := LatentCoefficients.endpoint_coefficients rows C
      (actualCodeHash (Factory.system HD HS CERT n r)) (Factory.circuits HD HS CERT n r)
      spec.service.solver hS (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d)
      (decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r)
        (rationalRepetitionBudget (2*(r+1)) c d) w)
    have hbits := LatentCoefficients.endpoint_entry_bounds rows C
      (actualCodeHash (Factory.system HD HS CERT n r)) (Factory.circuits HD HS CERT n r)
      spec.service.solver (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d)
      (decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r)
        (rationalRepetitionBudget (2*(r+1)) c d) w)
    have hcalls := SharedCircuit.ConcreteQuantum.prepare_calls rows C
      (actualCodeHash (Factory.system HD HS CERT n r)) (Factory.circuits HD HS CERT n r)
      spec.service.solver (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d)
      (decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r)
        (rationalRepetitionBudget (2*(r+1)) c d) w)
    refine ⟨run, v, hout, htime, hspace, hend, htails, hv, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, hcalls, ?_, ?_⟩
    · subst hv; exact hrange
    · subst hv; exact h0
    · subst hv; exact h0s
    · subst hv; exact hl
    · subst hv; exact hls
    · subst hv; exact hone
    · subst hv; exact hbits
    · -- (R2)
      intro hr
      obtain ⟨final, totals, events, _, htrace, _, htc, hot, hcap, hdisp, _, _⟩ :=
        hreg rows C a b c d ha hc hr w
      obtain ⟨run', _, hrt', _⟩ := hpos rows C a b c d ha hc hr w
      have heq := (OracleCost.MultiTape.Completed.unique run run').2.1
      have hpt := LatentMachine.Factory.prepare_resource_time HD HS CERT spec hT rows C hr
        (rationalCellBudget a b) (rationalRepetitionBudget (2*(r+1)) c d) w
      have hcapPoly := InputEncoding.queryExtentCap_input_polynomial rows C a b c d
        (gateConstant HD HS CERT) 1
      have hvar := hT (engine_variables_satExtent rows C (gateConstant HD HS CERT) 1)
      refine ⟨totals, final, events, htrace, htc, hcap, hot, ?_, hdisp, ?_⟩
      · rw [hot]
        refine hpt.trans ?_
        rw [Nat.mul_assoc (2*(r+1)*(2*(rationalRepetitionBudget (2*(r+1)) c d)+1)*
          trialCallBound (keySize n r) (rationalCellBudget a b))]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (PtE.monotone hcapPoly) hvar)
      · rw [heq, hot]
        exact hrt'
    · -- (R3)
      intro hr key valid
      have hg := LatentMachine.Factory.gates_of_latent_positive HD HS CERT (n:=n) hr
      have hdim := resolveRequest_dimensions rows C
        (actualCodeHash (Factory.system HD HS CERT n r)) (Factory.circuits HD HS CERT n r)
        (rationalRepetitionBudget (2*(r+1)) c d)
        (decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r)
          (rationalRepetitionBudget (2*(r+1)) c d) w)
        (gateConstant HD HS CERT * keySize n r) hg key valid
      have hev := engine_variables_satExtent rows C (gateConstant HD HS CERT) 1
      have hcapPoly := InputEncoding.queryExtentCap_input_polynomial rows C a b c d
        (gateConstant HD HS CERT) 1
      have htm := (spec.dimension_request_bounds hT _ _ _ hdim.1 hdim.2).1
      have hbitsEq := Final.concreteQuery_valid rows C
        (actualCodeHash (Factory.system HD HS CERT n r)) (Factory.circuits HD HS CERT n r)
        (rationalRepetitionBudget (2*(r+1)) c d)
        (decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r)
          (rationalRepetitionBudget (2*(r+1)) c d) w) 1 key valid
      refine ⟨padRequest 1 (resolveRequest rows C
        (actualCodeHash (Factory.system HD HS CERT n r)) (Factory.circuits HD HS CERT n r)
        (rationalRepetitionBudget (2*(r+1)) c d)
        (decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r)
          (rationalRepetitionBudget (2*(r+1)) c d) w) key valid), hbitsEq, ?_, ?_, ?_⟩
      · refine le_trans ?_ hev
        change max _ _ ≤ max _ _
        exact max_le_max hdim.1 (Nat.mul_le_mul_left 1 hdim.2)
      · refine le_trans ?_ hev
        rw [padRequest_length]
        refine hdim.2.trans ?_
        unfold QuantumService.engineVariables
        exact (le_of_eq (Nat.one_mul _).symm).trans (le_max_right _ _)
      · change (Final.Resource.satReply spec (Final.concreteQuery rows C
          (actualCodeHash (Factory.system HD HS CERT n r)) (Factory.circuits HD HS CERT n r)
          (rationalRepetitionBudget (2*(r+1)) c d)
          (decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r)
            (rationalRepetitionBudget (2*(r+1)) c d) w) 1 key)).time ≤ _
        rw [hbitsEq, Final.Resource.satReply_encode]
        exact htm.trans (Nat.mul_le_mul (PtE.monotone hcapPoly) (hT hev))

end QecReliability.LatentMachine.Runtime.FixedQuantum

#print axioms QecReliability.LatentCoefficients.endpoint_coefficients
#print axioms QecReliability.LatentMachine.Runtime.FixedQuantum.isotropic_latent_machine_guarantee_resources
