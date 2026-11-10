import ExternalSATOuterCandidateTraversal
import ExternalSATCanonicalHeader

/-! Numerical hierarchy for the actual finite traversal budgets. The final
reverse/output-length charge is intentionally not asserted here: it needs the
separate exact canonical-byte endpoint. No observed-space statement is made. -/
namespace QecReliability.ExternalSATBridge.TraversalBudgetHierarchy
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem one_le_power (R k : ℕ) : 1 ≤ (R + 1) ^ k :=
  Nat.succ_le_of_lt (by positivity)

theorem base_le_power (R k : ℕ) : R + 1 ≤ (R + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      R + 1 ≤ (R + 1) ^ (k + 1) := ih
      _ = (R + 1) ^ (k + 1) * 1 := by omega
      _ ≤ (R + 1) ^ (k + 1) * (R + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (R + 1) ^ (k + 1 + 1) := (pow_succ (R + 1) (k + 1)).symm

theorem deep_budget_le (U R : ℕ) (clauses : List (List ℕ))
    (hU : U ≤ 2 * R) (hm : clauses.length ≤ R) :
    DeepCandidateTraversal.budget U clauses ≤ 2048 * (R + 1) ^ 2 := by
  have hp := Nat.mul_le_mul hm (show 288 * U + 707 ≤ 576 * R + 707 from by omega)
  dsimp only [DeepCandidateTraversal.budget]
  nlinarith

theorem middle_budget_le (U R : ℕ) (clauses : List (List ℕ))
    (hU : U ≤ 2 * R) (hm : clauses.length ≤ R) :
    MiddleCandidateTraversal.budget U clauses ≤ 8192 * (R + 1) ^ 3 := by
  have hd := deep_budget_le U R clauses hU hm
  have hp := Nat.mul_le_mul (show U + 1 ≤ 2 * (R + 1) from by omega)
    (Nat.add_le_add_right hd 16)
  have h1 := one_le_power R 3
  have hlin := base_le_power R 2
  norm_num only at hlin
  have hb : MiddleCandidateTraversal.budget U clauses ≤
      4096 * (R + 1) ^ 3 + 32 * (R + 1) + 64 := by
    dsimp only [MiddleCandidateTraversal.budget]
    nlinarith
  omega

theorem outer_budget_le (U R : ℕ) (clauses : List (List ℕ))
    (hU : U ≤ 2 * R) (hm : clauses.length ≤ R) :
    OuterCandidateTraversal.budget U clauses ≤ 32768 * (R + 1) ^ 4 := by
  have hd := middle_budget_le U R clauses hU hm
  have hp := Nat.mul_le_mul (show U + 1 ≤ 2 * (R + 1) from by omega)
    (Nat.add_le_add_right hd 16)
  have h1 := one_le_power R 4
  have hlin := base_le_power R 3
  norm_num only at hlin
  have hb : OuterCandidateTraversal.budget U clauses ≤
      16384 * (R + 1) ^ 4 + 32 * (R + 1) + 64 := by
    dsimp only [OuterCandidateTraversal.budget]
    nlinarith
  omega

theorem outer_range_le (v R : ℕ) (clauses : List (List ℕ))
    (hv : v ≤ R) (hm : clauses.length ≤ R) :
    2 * v * (OuterCandidateTraversal.budget (2 * v) clauses + 7) + 4 ≤
      131072 * (R + 1) ^ 5 := by
  have hd := outer_budget_le (2 * v) R clauses (by omega) hm
  have hp := Nat.mul_le_mul (show 2 * v ≤ 2 * (R + 1) from by omega)
    (Nat.add_le_add_right hd 7)
  have h1 := one_le_power R 5
  have hlin := base_le_power R 4
  norm_num only at hlin
  have hb : 2 * v * (OuterCandidateTraversal.budget (2 * v) clauses + 7) + 4 ≤
      65536 * (R + 1) ^ 5 + 14 * (R + 1) + 4 := by nlinarith
  omega

theorem header_le (v R : ℕ) (hv : v ≤ R) (hs : v.size ≤ R) :
    CanonicalHeader.timeBound v.size v ≤ 64 * (R + 1) ^ 2 := by
  have hp := Nat.mul_le_mul (Nat.add_le_add_right hv 1) (Nat.add_le_add_right hs 1)
  dsimp only [CanonicalHeader.timeBound]
  nlinarith

/-- This expression is definitionally the actual CanonicalRawController.boundCost. -/
theorem boundCost_le (v R : ℕ) (hv : v ≤ R) (hs : v.size ≤ R) :
    7 * v.size + 7 + 32 * (2 * v + 1) * (v.size + 2) ≤ 256 * (R + 1) ^ 2 := by
  have hp := Nat.mul_le_mul (show 2 * v + 1 ≤ 2 * R + 1 from by omega)
    (Nat.add_le_add_right hs 2)
  nlinarith

theorem root_visit_le (v R : ℕ) (clauses : List (List ℕ))
    (hv : v ≤ R) (hm : clauses.length ≤ R) (hw : ∀ c ∈ clauses, c.length ≤ 3)
    (hn : ∀ c ∈ clauses, ∀ n ∈ c, n ≤ 2 * v) :
    CandidateVisit.timeBound ![[], [], []] clauses ≤ 2048 * (R + 1) ^ 2 := by
  apply VisitBounds.timeBound_quadratic _ (2 * v) R clauses _ hw hn (by omega) hm
  intro i; fin_cases i <;> simp

theorem clear_final_code_le (v R : ℕ) (hv : v ≤ R) :
    2 * (2 * v + 1) + 3 ≤ 8 * (R + 1) := by omega

end QecReliability.ExternalSATBridge.TraversalBudgetHierarchy
#print axioms QecReliability.ExternalSATBridge.TraversalBudgetHierarchy.outer_range_le
#print axioms QecReliability.ExternalSATBridge.TraversalBudgetHierarchy.root_visit_le
