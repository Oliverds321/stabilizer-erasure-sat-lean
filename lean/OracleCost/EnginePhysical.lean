import OracleCost.EncodedSAT
import OracleCost.QuantumQueryBound

/-! The same cached physical estimator, now backed by a fixed encoded-input
SAT machine. This charges its actual finite executions, with density padding,
and keeps the external time function linear. It does not charge serialization,
wrapper execution or cleanup, and is therefore not a total-complexity theorem.
-/
namespace QecReliability.OracleCost.QuantumService
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput QecPhysical.Stabilizer MultiTape

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))
    {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : Machine k Γ Λ} {D : ℕ} {Ptime Pspace : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT M D Ptime Pspace T) (hT : Monotone T)

def engineVariables (D g : ℕ) : ℕ :=
  max (variableBound rows C g) (D*clauseBound rows C g)

def engineInputBound (D g : ℕ) : ℕ :=
  QueryCodec.sizeBound (engineVariables rows C D g) (clauseBound rows C g)

include hT

theorem engine_request_bounds (g : ℕ) (hg : ∀ s seed, (K.program s seed).gates≤g) :
    (∀ i pre, (spec.service.run (baseRequest rows C i pre)).time≤
      Ptime.eval (engineInputBound rows C D g)*T (engineVariables rows C D g)) ∧
    (∀ i s seed pre, (spec.service.run (cellRequest rows C H K i s seed pre)).time≤
      Ptime.eval (engineInputBound rows C D g)*T (engineVariables rows C D g)) := by
  constructor
  · intro i pre
    have hb := base_dimensions rows C g i pre
    exact (spec.request_bounds hT _ _ _ hb.1 hb.2).1
  · intro i s seed pre
    have hb := cell_dimensions rows C H K g i s seed pre (hg s seed)
    exact (spec.request_bounds hT _ _ _ hb.1 hb.2).1

theorem prepare_engine_time (B m g : ℕ) (hg : ∀ s seed, (K.program s seed).gates≤g)
    (ω : Fin (2*m+1) → Ω) :
    (prepareMeasured rows C H K spec.service B m ω).oracleTime≤
      2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B*
        Ptime.eval (engineInputBound rows C D g)*T (engineVariables rows C D g) := by
  have hs := engine_request_bounds rows C H K spec hT g hg
  have ht := prepareMeasured_time rows C H K spec.service B m _ ω
    (fun i => hs.1 i []) (fun i s seed pre _ => hs.2 i s seed pre)
  simpa only [Nat.mul_assoc] using ht

/-- Every seed has the old structural/payload guarantees and a bound on
summed actual SAT-machine time. Only simultaneous approximation is random.
The machine's complete halting-run hypothesis replaces a semantic callback.
No wrapper-time, engine-reset or all-length hash-factory assumption is hidden
in this statement, and none is discharged by it. -/
theorem engine_shape_confidence (L : Lift (rowSpace rows))
    (a b c d : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hab : a≤b)
    (hanti : Antitone (layerAverage (circuitMap C) (score (rowSpace rows))))
    (g : ℕ) (hg : ∀ s seed, (K.program s seed).gates≤g) :
    (∀ ω,
      let B := rationalCellBudget a b
      let m := rationalRepetitionBudget (2*(r+1)) c d
      let O := output rows C H K spec.service true a b c d ω
      (prepareMeasured rows C H K spec.service B m ω).oracleTime≤
        2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B*
          Ptime.eval (engineInputBound rows C D g)*T (engineVariables rows C D g) ∧
      LinearRepair.Resources n r B m O ∧
      ShapeStructure (rowSpace rows) (circuitMap C) O.coefficients.curve) ∧
    1-(c:ℝ)/d ≤ (repeatedLaw H.law (rationalRepetitionBudget (2*(r+1)) c d)).prob
      (fun ω => L.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b)
        (output rows C H K spec.service true a b c d ω).coefficients.curve) := by
  have hs := engine_request_bounds rows C H K spec hT g hg
  have result := measured_shape_confidence rows L C H K spec.service a b c d
    ha hb hc hd hab hanti _ (fun i => hs.1 i [])
    (fun i s seed pre _ => hs.2 i s seed pre)
  simpa only [Nat.mul_assoc] using result

omit hT spec in
/-- Padding preserves the explicit incidence-linear variable bound. The
density parameter is fixed with the SAT engine, independent of precision. -/
theorem iid_engine_variables {n : ℕ} (rows : List (List (PauliCoord n))) (c h D : ℕ)
    (hn : 1≤n) (hw : rowIncidences rows≤c*n) :
    engineVariables rows (Program.pure (fun i : Fin n => i)) D (h*(3*n))≤
      max (41+4*c+3*h) (D*(158+18*c+12*h))*n := by
  have hb := iid_dimensions rows c h hn hw
  unfold engineVariables
  calc
    _ ≤ max ((41+4*c+3*h)*n) (D*((158+18*c+12*h)*n)) :=
      max_le_max hb.1 (Nat.mul_le_mul_left D hb.2)
    _ = _ := by rw [← Nat.mul_assoc, max_mul_of_nonneg _ _ (Nat.zero_le n)]

end QecReliability.OracleCost.QuantumService
