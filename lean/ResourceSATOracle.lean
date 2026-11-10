import ResourceEncodedSAT
import RegMachine.SATOracle

/-! Resource caps restrict proof-level admissibility only. Answer and cost are
those of the same completed run used by `satOracle`; no runtime changes. -/
namespace QecReliability.RegMachine
open OracleCost OracleCost.MultiTape

variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

noncomputable def resourceSatOracle (E : Machine kE ΓE ΛE) (D : ℕ)
    (resource : SATRequest → ℕ) (cap : ℕ) : OracleSpec :=
  { satOracle E D 0 with
    qok := fun w => ∃ q : SATRequest, D*q.formula.length ≤ q.varCount ∧
      w = QueryCodec.encode q ∧ resource q ≤ cap }

theorem resourceSatOracle_run (E : Machine kE ΓE ΛE) (D : ℕ)
    (resource : SATRequest → ℕ) (cap : ℕ) {w : List Bool} (run : Completed E w) :
    (resourceSatOracle E D resource cap).oracle w = run.output ∧
    (resourceSatOracle E D resource cap).ocost w = run.time + run.cells :=
  satOracle_run E D 0 run

/-- Precisely the hypothesis of the existing `oracle_sprog_completed`. -/
theorem resourceSatOracle_realizes {E : Machine kE ΓE ΛE} {D : ℕ}
    {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ} {resource : SATRequest → ℕ}
    (spec : ResourceEncodedSAT E D Pt Ps T resource) (cap : ℕ) :
    ∀ w, (resourceSatOracle E D resource cap).qok w →
      ∃ run : Completed E w,
        run.output = (resourceSatOracle E D resource cap).oracle w ∧
        run.time + run.cells ≤ (resourceSatOracle E D resource cap).ocost w ∧
        run.cells ≤ Ps.eval cap := by
  intro w hw
  obtain ⟨q, hd, rfl, hcap⟩ := hw
  obtain ⟨run, _, _, hs⟩ := spec.complete q hd
  obtain ⟨ho, hc⟩ := resourceSatOracle_run E D resource cap run
  exact ⟨run, ho.symm, hc.ge, hs.trans (Ps.monotone hcap)⟩

theorem resourceSatOracle_padded {E : Machine kE ΓE ΛE} {D cap : ℕ}
    {resource : SATRequest → ℕ} (q : SATRequest)
    (hcap : resource (padRequest D q) ≤ cap) :
    (resourceSatOracle E D resource cap).qok (QueryCodec.encode (padRequest D q)) :=
  ⟨padRequest D q, padRequest_density D q, rfl, hcap⟩

/-- Retain both dimension and payload bounds when extracting a typed query. -/
theorem resourceSatOracle_extent_witness {E : Machine kE ΓE ΛE} {D cap : ℕ}
    {w : List Bool} (hw : (resourceSatOracle E D requestExtent cap).qok w) :
    ∃ q : SATRequest, D*q.formula.length ≤ q.varCount ∧
      w = QueryCodec.encode q ∧ q.varCount ≤ cap ∧ w.length ≤ cap := by
  obtain ⟨q, hd, rfl, hcap⟩ := hw
  unfold requestExtent at hcap
  exact ⟨q, hd, rfl, by omega, by omega⟩

end QecReliability.RegMachine
