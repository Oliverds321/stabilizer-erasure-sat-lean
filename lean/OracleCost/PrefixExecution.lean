import OracleCost.PrefixMachine
import OracleCost.PrefixSAT

/-! The explicit-prefix, single-invocation evaluator refines the exact projected
counter. Its service peak and prefix-copy bounds describe this actual recursion;
converting all local arithmetic and allocation to a standard machine is separate.
-/
namespace QecReliability.OracleCost.PrefixSAT
open PrefixEnumeration PrefixCNF

def execute {q w : ℕ} (service : SATService) (F : Formula (q+w))
    (hF : Width 3 F) (cap : ℕ) : PrefixMachine.Result :=
  PrefixMachine.execute q (fun pre => service.run (request F hF pre)) [] cap

theorem execute_control {q w : ℕ} (service : SATService) (F : Formula (q+w))
    (hF : Width 3 F) (cap : ℕ) :
    (execute service F hF cap).control=measured service F hF cap := by
  simpa only [execute,measured,decision,List.nil_append] using
    PrefixMachine.control_eq q (fun pre => service.run (request F hF pre)) [] cap

theorem execute_spec {q w : ℕ} (service : SATService) (F : Formula (q+w))
    (hF : Width 3 F) (cap bound : ℕ)
    (hworkspace : ∀ pre, pre.length≤q → (service.run (request F hF pre)).workspace≤bound) :
    (execute service F hF cap).control.count=min cap (modelCount (Projected F)) ∧
    (execute service F hF cap).control.calls≤1+2*q*cap ∧
    (execute service F hF cap).control.peakFrames≤q+1 ∧
    (execute service F hF cap).prefixCopies≤2*(q+1)*(1+2*q*cap) ∧
    (execute service F hF cap).oraclePeak≤bound := by
  have he := exact_count service F hF cap
  have hb := structural_bounds service F hF cap
  have hp : (execute service F hF cap).prefixCopies≤
      2*(q+1)*(execute service F hF cap).control.calls := by
    simpa only [execute,List.length_nil,Nat.zero_add] using
      PrefixMachine.prefixCopies_le q (fun pre => service.run (request F hF pre)) [] cap
  have ho : (execute service F hF cap).oraclePeak≤bound := by
    exact PrefixMachine.oraclePeak_le q _ [] cap bound (by simpa using hworkspace)
  rw [execute_control] at hp ⊢
  exact ⟨he.1,hb.1,hb.2.2,hp.trans (Nat.mul_le_mul_left _ hb.1),ho⟩

end QecReliability.OracleCost.PrefixSAT
