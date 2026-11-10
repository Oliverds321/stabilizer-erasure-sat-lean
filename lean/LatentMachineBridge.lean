import LatentMachineInput
import Final.Statement
import PhysicalBridge.LinearRepairEdges

/-!
Conditional assembly bridge, not a completed latent finite-tape implementation.
The fixed machine M must separately satisfy deterministic run refinement and
the decoder must realize the exact repeated seed law. Neither premise assumes
statistical accuracy. No monotonicity premise or shape repair is used here.
-/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine
open scoped Classical
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput QecPhysical QecPhysical.Stabilizer
open OracleCost OracleCost.MultiTape

variable {Ω : Type} [Fintype Ω] {n r : ℕ}
  (rows : List (List (PauliCoord n))) (C : Program r n)
  (H : HashStages Ω (CoefficientKey n r) (keySize n r))
  (K : SuppliedHashCircuits H (keyBits n r))
  (solver : ∀ v, PrefixCNF.ExactSAT v 3) (a b c d : ℕ)

abbrev repetitions : ℕ := rationalRepetitionBudget (2*(r+1)) c d

def semanticOutput (ω : Fin (2*repetitions (r:=r) c d+1) → Ω) : Vector r :=
  (LinearRepair.prepare false rows C H K solver a b c d ω).coefficients

/-- Exact uniform coin realization for EVERY seed predicate. It may not be
replaced by an unproved assertion that decoded seeds are independent/uniform. -/
def RealizesCoins (N : ℕ)
    (decode : (Fin N → Bool) → (Fin (2*repetitions (r:=r) c d+1) → Ω)) : Prop :=
  ∀ P : (Fin (2*repetitions (r:=r) c d+1) → Ω) → Prop,
    (repeatedLaw H.law (repetitions (r:=r) c d)).prob P * (2:ℝ)^N =
      ((Finset.univ.filter (fun w : Fin N → Bool => P (decode w))).card : ℝ)

variable {kM : ℕ} {ΓM ΛM : Type} [Fintype ΓM] [Inhabited ΓM] [Fintype ΛM]
  (M : Machine kM ΓM ΛM) (o : Fin (kM+1))

/-- The obligations the NEW general-circuit parser/evaluator/loop must discharge.
`cells` is Completed.cells: all visited cells, including coins and all tapes.
Output equality is for every completed decoded output, not a chosen witness.
Uniformity requires this predicate for all inputs with the SAME M and o.
-/
def RunRefinement (N timeBound spaceBound : ℕ)
    (decode : (Fin N → Bool) → (Fin (2*repetitions (r:=r) c d+1) → Ω)) : Prop :=
  (∀ w : Fin N → Bool,
    ∃ run : Completed M (input rows C a b c d (List.ofFn w)),
      Final.Outputs M run o (semanticOutput rows C H K solver a b c d (decode w)) ∧
      run.time ≤ timeBound ∧ run.cells ≤ spaceBound) ∧
  (∀ (w : Fin N → Bool)
    (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
    Final.Outputs M run o v →
      v = semanticOutput rows C H K solver a b c d (decode w))

theorem endpoint_machine_bridge (L : Lift (rowSpace rows))
    (ha : 0<a) (hab : a≤b) (hc : 0<c) (hd : 0<d)
    (N timeBound spaceBound : ℕ)
    (decode : (Fin N → Bool) → (Fin (2*repetitions (r:=r) c d+1) → Ω))
    (hcoins : RealizesCoins H c d N decode)
    (hrun : RunRefinement rows C H K solver a b c d M o N timeBound spaceBound decode) :
    (∀ w : Fin N → Bool,
      ∃ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
        Final.Outputs M run o v ∧ run.time ≤ timeBound ∧ run.cells ≤ spaceBound ∧
        EndpointStructure (rowSpace rows) (circuitMap C) v.curve ∧
        ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
          TailExact (entanglementFidelity (L.erasureFlagDecoder.comp
            (L.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map) (v.curve p)) ∧
    (1-(c:ℝ)/d) * (2:ℝ)^N ≤
      ((Finset.univ.filter (fun w : Fin N → Bool =>
        ∀ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
          Final.Outputs M run o v →
          L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b) v.curve)).card : ℝ) := by
  classical
  have hb : 0<b := lt_of_lt_of_le ha hab
  have hconf := Lift.linear_endpoint_confidence rows L C H K solver a b c d ha hb hc hd hab
  constructor
  · intro w
    obtain ⟨run, hout, htime, hspace⟩ := hrun.1 w
    refine ⟨run, semanticOutput rows C H K solver a b c d (decode w),
      hout, htime, hspace, (hconf.1 (decode w)).2, ?_⟩
    exact Lift.linear_endpoint_tails rows L C H K solver a b c d (decode w)
  · let P := fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
      (semanticOutput rows C H K solver a b c d ω).curve
    have hp : 1-(c:ℝ)/d ≤ (repeatedLaw H.law (repetitions (r:=r) c d)).prob P := hconf.2
    have hh := mul_le_mul_of_nonneg_right hp (show (0:ℝ)≤2^N by positivity)
    rw [hcoins P] at hh
    apply hh.trans
    exact_mod_cast Finset.card_le_card (fun w hw => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      intro run v hv
      rw [hrun.2 w run v hv]
      exact hw)

end QecReliability.LatentMachine
