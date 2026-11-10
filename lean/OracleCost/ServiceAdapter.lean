import OracleCost.Interface

/-! A width-checked adapter from the measured external service to the existing
exact SAT interface. The check is executable, but its local cost is not yet
charged by the callback-time theorem. Invalid-width inputs return false and
are never used by the verified quantum compiler. -/
namespace QecReliability.OracleCost

instance widthDecidable {v k : ℕ} (F : PrefixCNF.Formula v) :
    Decidable (PrefixCNF.Width k F) := by
  unfold PrefixCNF.Width
  infer_instance

def SATService.solver (service : SATService) (v : ℕ) : PrefixCNF.ExactSAT v 3 where
  solve F := if h : PrefixCNF.Width 3 F then (service.run ⟨v,F,h⟩).value else false
  correct F h := by simp only [dif_pos h]; exact service.correct ⟨v,F,h⟩

@[simp] theorem SATService.solve_width (service : SATService) {v : ℕ}
    (F : PrefixCNF.Formula v) (h : PrefixCNF.Width 3 F) :
    (service.solver v).solve F = (service.run ⟨v,F,h⟩).value := by
  simp only [SATService.solver,dif_pos h]

end QecReliability.OracleCost
