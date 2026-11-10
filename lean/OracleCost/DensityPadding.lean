import OracleCost.QuerySize
import QecReliability.SharedCircuit

/-! Explicit unused-variable padding for a density-restricted SAT engine.
The integer parameter D avoids a runtime operation on a real density. Only
decision semantics is changed at this boundary, so projected keys are untouched.
-/
namespace QecReliability.OracleCost
open PrefixCNF SharedCircuit

def paddedVariables (D : ℕ) (request : SATRequest) : ℕ :=
  max request.varCount (D*request.formula.length)

def padRequest (D : ℕ) (request : SATRequest) : SATRequest where
  varCount := paddedVariables D request
  formula := rename (Fin.castLE (Nat.le_max_left _ _)) request.formula
  width := width_rename _ _ request.width

@[simp] theorem padRequest_length (D : ℕ) (request : SATRequest) :
    (padRequest D request).formula.length=request.formula.length := by
  simp [padRequest]

theorem padRequest_density (D : ℕ) (request : SATRequest) :
    D*(padRequest D request).formula.length≤(padRequest D request).varCount := by
  rw [padRequest_length]
  exact Nat.le_max_right _ _

theorem padRequest_sat (D : ℕ) (request : SATRequest) :
    (∃ assignment, eval (padRequest D request).formula assignment=true) ↔
      ∃ assignment, eval request.formula assignment=true := by
  simp only [padRequest, paddedVariables, eval_rename]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨fun i => a (Fin.castLE (Nat.le_max_left _ _) i), ha⟩
  · rintro ⟨a,ha⟩
    let extend : Fin (max request.varCount (D * request.formula.length)) → Bool :=
      fun i => if h : i.val<request.varCount then a ⟨i.val,h⟩ else false
    refine ⟨extend,?_⟩
    have h : (fun i => extend (Fin.castLE (Nat.le_max_left _ _) i))=a := by
      funext i
      simp [extend,i.isLt]
    rwa [h]

theorem padRequest_size {D V M : ℕ} (request : SATRequest)
    (hv : request.varCount≤V) (hm : request.formula.length≤M) :
    (padRequest D request).varCount≤max V (D*M) ∧
    (QueryCodec.encode (padRequest D request)).length≤
      QueryCodec.sizeBound (max V (D*M)) M := by
  have vp : (padRequest D request).varCount≤max V (D*M) := by
    exact max_le_max hv (Nat.mul_le_mul_left D hm)
  exact ⟨vp,QueryCodec.encode_length_le _ _ _ vp (by simpa using hm)⟩

end QecReliability.OracleCost
