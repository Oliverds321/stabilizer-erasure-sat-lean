import PhysicalBridge.PhysicalApproximation
import QecReliability.CachedStorage

/-! The actual compiled/cached SAT estimator approximates the optimal fidelity
of the actual flagged erasure channel. Hash laws, supplied hash DAGs and the
exact width-three SAT callback are explicit; no confidence premise is assumed.
Resource bounds concern callback counts and stored natural-number payload. -/
noncomputable section
namespace QecPhysical.Stabilizer
open QecReliability QecReliability.Binary
open QecReliability.SharedCircuit
open QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.ConcreteQuantum

theorem layerGoodCount_eq_coefficient {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) :
    layerGoodCount S C j = goodCoefficient S C j := rfl

theorem layerBadCount_eq_coefficient {n r : ℕ} (S : Submodule Bit (Pauli n))
    (C : Causes r → Finset (Fin n)) (j : Fin (r+1)) :
    layerBadCount S C j = badCoefficient S C j := rfl

/-- The compiler projects exactly onto (latent cause,z). Physical witnesses,
cleaning coefficients and deterministic gate outputs are not counted. -/
theorem quantumLayer_physical_count {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n) (i : CoefficientIndex r) :
    PrefixEnumeration.modelCount (PrefixCNF.Projected (quantumLayer rows C i).projectedFormula) =
      if i.1 then layerGoodCount (rowSpace rows) (circuitMap C) i.2
      else layerBadCount (rowSpace rows) (circuitMap C) i.2 :=
  quantumLayer_count rows C i

/-- Prefix restrictions add unit clauses (or a contradictory empty clause).
This bounds base queries as well as the hash-cell queries bounded in M12. -/
theorem quantumLayer_prefix_size {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : CoefficientIndex r) (pre : List Bool) :
    PrefixCNF.Width 3 (PrefixCNF.restrict (quantumLayer rows C i).projectedFormula pre) ∧
    (PrefixCNF.restrict (quantumLayer rows C i).projectedFormula pre).length ≤
      18*rowIncidences rows+20*n+82*r+4*C.gates+53 ∧
    keySize n r + (quantumWitness rows i.1 + (quantumLayer rows C i).aux) ≤
      21*r+8*n+4*rowIncidences rows+C.gates+12 := by
  have h := quantumLayer_contract rows C i
  refine ⟨PrefixCNF.restrict_width h.1 (by omega) pre, ?_, h.2.2.1⟩
  have hl := PrefixCNF.restrict_length_bound (quantumLayer rows C i).projectedFormula pre
  unfold keySize at *
  omega

namespace Lift
variable {n r : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

theorem physical_fidelity_eq_latentCurve (C : Causes r → Finset (Fin n))
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp hp1)).map =
      latentCurve C (score S) p := by
  rw [(L.iidLatentErasure_optimum C p hp hp1).1, latentCurve_eq_bernstein]
  rfl

/-- A result contract, never an input hypothesis. The reference value is attained
by a physical decoder and bounds EVERY CPTP decoder seeing only the erasure flag.
RelPair controls fidelity and its complement simultaneously, including zeros. -/
def PhysicalCurveContract (C : Causes r → Finset (Fin n))
    (ε : ℝ) (T : CoefficientTable r) : Prop :=
  ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
    RelPair ε
      (entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp.1 hp.2)).map)
      (T.curve p) ∧
    0≤T.curve p ∧ T.curve p≤1 ∧
    ∀ Q : Channel (ErasureFlagOutput n) L.LogicalIndex,
      entanglementFidelity (Q.comp (L.iidLatentErasure C p hp.1 hp.2)).map ≤
        entanglementFidelity (L.erasureFlagDecoder.comp (L.iidLatentErasure C p hp.1 hp.2)).map

/-- End-to-end correctness and confidence for the actual compiled SAT evaluator.
The same output table has both-tail whole-curve accuracy, an exact entry count,
a proved binary payload bound and the recorded decision-callback bound. -/
theorem cached_physical_confidence {Ω : Type*} [Fintype Ω]
    (rows : List (List (PauliCoord n))) (L : Lift (rowSpace rows)) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε≤1) (hδ : 0<δ) :
    1-δ ≤ (repeatedLaw H.law (repetitionBudget (Fintype.card (CoefficientIndex r)) δ hδ)).prob
      (fun ω =>
        let B := cellBudget (ε/3)
        let m := repetitionBudget (Fintype.card (CoefficientIndex r)) δ hδ
        let T := prepare rows C H K solver B m ω
        T.calls ≤ 2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B ∧
        T.good.entries.length+T.bad.entries.length = 2*(r+1) ∧
        T.payloadBits ≤ 2*(r+1)*(keySize n r+(4*B+1).size+
          ((2*m+1)*trialCallBound (keySize n r) B).size) ∧
        L.PhysicalCurveContract (circuitMap C) ε T) := by
  apply (cached_curve_confidence rows L.isotropic C H K solver hε hε1 hδ).trans
  apply FiniteProbability.prob_mono
  intro ω hω
  refine ⟨hω.1, prepare_entry_count rows C H K solver _ _ ω,
    prepare_payload rows C H K solver _ _ ω, ?_⟩
  intro p hp
  rw [L.physical_fidelity_eq_latentCurve (circuitMap C) p hp.1 hp.2]
  refine ⟨(hω.2 p hp).1, (hω.2 p hp).2.1, (hω.2 p hp).2.2, ?_⟩
  intro Q
  have h := (L.iidLatentErasure_optimum (circuitMap C) p hp.1 hp.2).2 Q
  rw [latentCurve_eq_bernstein]
  exact h

end Lift
end QecPhysical.Stabilizer
