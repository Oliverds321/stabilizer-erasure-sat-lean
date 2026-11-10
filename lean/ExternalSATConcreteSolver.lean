import ExternalSATLinkedPolynomial
import ExternalSATResourceBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final

/-! A fixed native SAT machine obtained from the verified solver and the
canonical query frontend. The solver supplies the execution used by the
handoff theorem for each request. -/
namespace QecReliability.ExternalSATBridge.ConcreteSolver

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open Computation SqrtLogSpace

theorem exists_bounded_machine :
    ∃ (engine : PrimitiveMachine) (Ptime Pspace : PolynomialEnvelope) (A : ℝ),
      0 < A ∧ ∀ q : SATRequest,
      ∃ run : MultiTape.Completed
        (PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)) (QueryCodec.encode q),
        (run.output = true ↔ ∃ a, PrefixCNF.eval q.formula a = true) ∧
        run.time ≤ Ptime.eval (requestExtent q) * RateMajorant.runtimeEnvelope A q.varCount ∧
        run.cells ≤ Pspace.eval (requestExtent q) := by
  obtain ⟨labels, program, C, A, S, d, e, _hout, _hC, hA, _hS, _hd, _he, hsolver⟩ :=
    sat_polynomial_space 3 (by omega)
  refine ⟨GuardedCompiler.primitive program, pipelineEnvelope 4194304 (Nat.ceil C) d,
    pipelineEnvelope 268435456 (Nat.ceil S) e, A, hA, ?_⟩
  intro q
  have hwidth : SAT.WidthAtMost 3 (FormulaBridge.formula q.formula) :=
    FormulaBridge.formula_width q.formula q.width
  obtain ⟨answer, steps, final, htrace, _hcount, _hanswer, hhalt, _hpositive,
    hsat, htime, hspace⟩ := hsolver q.varCount (FormulaBridge.formula q.formula) hwidth
  obtain ⟨run, hout, ht, hs⟩ :=
    PrimitiveLink.query_then_engine_polynomial (GuardedCompiler.primitive program) q htrace hhalt
  have hrate := PrimitiveTransport.external_rate_dominated A (n := q.varCount) le_rfl
  have hbaseNonneg :
      (0 : ℝ) ≤ (Encoding.formulaBitLength (FormulaBridge.formula q.formula) : ℝ) + 1 :=
    add_nonneg (Nat.cast_nonneg _) zero_le_one
  have hcoefficient :
      C * ((Encoding.formulaBitLength (FormulaBridge.formula q.formula) : ℝ) + 1) ^ d ≤
      (Nat.ceil C : ℝ) *
        ((Encoding.formulaBitLength (FormulaBridge.formula q.formula) : ℝ) + 1) ^ d :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil C) (pow_nonneg hbaseNonneg d)
  have htimeReal : (steps : ℝ) ≤
      (Nat.ceil C : ℝ) *
        ((Encoding.formulaBitLength (FormulaBridge.formula q.formula) : ℝ) + 1) ^ d *
        (RateMajorant.runtimeEnvelope A q.varCount : ℝ) :=
    htime.trans (mul_le_mul hcoefficient hrate (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbaseNonneg d)))
  have htimeNat : steps ≤ Nat.ceil C *
      (Encoding.formulaBitLength (FormulaBridge.formula q.formula) + 1) ^ d *
      RateMajorant.runtimeEnvelope A q.varCount := by exact_mod_cast htimeReal
  have hspaceReal : (visitedSpace final : ℝ) ≤
      (Nat.ceil S : ℝ) *
        ((Encoding.formulaBitLength (FormulaBridge.formula q.formula) : ℝ) + 1) ^ e :=
    (hspace steps final le_rfl htrace).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil S) (pow_nonneg hbaseNonneg e))
  have hspaceNat : visitedSpace final ≤ Nat.ceil S *
      (Encoding.formulaBitLength (FormulaBridge.formula q.formula) + 1) ^ e := by
    exact_mod_cast hspaceReal
  refine ⟨run, ?_, ?_, ?_⟩
  · rw [hout]
    exact hsat.trans (FormulaBridge.satisfiable_iff q.formula)
  · change run.time ≤ 4194304 * (requestExtent q + 1) ^ 5 + steps at ht
    have hpositive : 1 ≤ RateMajorant.runtimeEnvelope A q.varCount :=
      RateMajorant.runtimeEnvelope_pos A q.varCount
    have hfront : 4194304 * (requestExtent q + 1) ^ 5 ≤
        4194304 * (requestExtent q + 1) ^ 5 * RateMajorant.runtimeEnvelope A q.varCount := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (4194304 * (requestExtent q + 1) ^ 5) hpositive
    calc
      run.time ≤ 4194304 * (requestExtent q + 1) ^ 5 + steps := ht
      _ ≤ 4194304 * (requestExtent q + 1) ^ 5 * RateMajorant.runtimeEnvelope A q.varCount +
          Nat.ceil C * (Encoding.formulaBitLength (FormulaBridge.formula q.formula) + 1) ^ d *
            RateMajorant.runtimeEnvelope A q.varCount :=
        Nat.add_le_add hfront htimeNat
      _ = (4194304 * (requestExtent q + 1) ^ 5 +
          Nat.ceil C * (Encoding.formulaBitLength (FormulaBridge.formula q.formula) + 1) ^ d) *
            RateMajorant.runtimeEnvelope A q.varCount := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (pipelineEnvelope_bound q 4194304 (Nat.ceil C) d)
  · change run.cells ≤ 268435456 * (requestExtent q + 1) ^ 5 + visitedSpace final at hs
    exact (hs.trans (Nat.add_le_add_left hspaceNat _)).trans
      (pipelineEnvelope_bound q 268435456 (Nat.ceil S) e)

theorem exists_correct_machine :
    ∃ engine : PrimitiveMachine, ∀ q : SATRequest,
      ∃ run : MultiTape.Completed
        (PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)) (QueryCodec.encode q),
        (run.output = true ↔ ∃ a, PrefixCNF.eval q.formula a = true) := by
  obtain ⟨engine, Ptime, Pspace, A, _hA, hrun⟩ := exists_bounded_machine
  refine ⟨engine, ?_⟩
  intro q
  obtain ⟨run, hsat, _ht, _hs⟩ := hrun q
  exact ⟨run, hsat⟩

/-- The density parameter is fixed at one. The stronger preceding result
handles every typed width-three request, including requests outside that
density restriction. -/
theorem exists_resource_machine :
    ∃ (engine : PrimitiveMachine) (Ptime Pspace : PolynomialEnvelope) (A : ℝ),
      0 < A ∧
      ResourceEncodedSAT (PrimitiveTransport.machine (PrimitiveLink.queryMachine engine))
        1 Ptime Pspace (RateMajorant.runtimeEnvelope A) requestExtent ∧
      Monotone (RateMajorant.runtimeEnvelope A) := by
  obtain ⟨engine, Ptime, Pspace, A, hA, hrun⟩ := exists_bounded_machine
  refine ⟨engine, Ptime, Pspace, A, hA, ?_, RateMajorant.runtimeEnvelope_monotone A⟩
  exact ⟨by decide, fun q _hdensity => hrun q⟩

end QecReliability.ExternalSATBridge.ConcreteSolver
