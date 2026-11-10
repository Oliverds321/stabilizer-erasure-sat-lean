import OracleCost.PrefixControl

/-! Concrete SAT requests along the existing prefix traversal. Query dimensions
and width are proved from construction. A bit serializer and the cost of
constructing these requests are deliberately not supplied by this module. -/
namespace QecReliability.OracleCost.PrefixSAT
open PrefixEnumeration PrefixCNF

def request {q w : ℕ} (F : Formula (q+w)) (hF : Width 3 F)
    (pre : List Bool) : SATRequest :=
  ⟨q+w, restrict F pre, restrict_width hF (by omega) pre⟩

def decision {q w : ℕ} (service : SATService) (F : Formula (q+w))
    (hF : Width 3 F) : ExactDecision (Projected F) where
  answer pre := (service.run (request F hF pre)).value
  correct pre := (service.correct (request F hF pre)).trans (restrict_sat F pre)

def measured {q w : ℕ} (service : SATService) (F : Formula (q+w))
    (hF : Width 3 F) (cap : ℕ) : PrefixControl.Result :=
  PrefixControl.run q (decision service F hF).answer
    (fun pre => (service.run (request F hF pre)).time) cap

theorem request_dimensions {q w : ℕ} (F : Formula (q+w)) (hF : Width 3 F)
    (pre : List Bool) (hlen : pre.length≤q) :
    (request F hF pre).varCount=q+w ∧
    (request F hF pre).formula.length=F.length+pre.length ∧
    (request F hF pre).formula.length≤F.length+q := by
  exact ⟨rfl,restrict_length F pre hlen,by
    change (restrict F pre).length≤F.length+q
    rw [restrict_length F pre hlen]
    omega⟩

theorem exact_count {q w : ℕ} (service : SATService) (F : Formula (q+w))
    (hF : Width 3 F) (cap : ℕ) :
    (measured service F hF cap).count=min cap (modelCount (Projected F)) ∧
    (measured service F hF cap).calls≤1+2*q*min cap (modelCount (Projected F)) :=
  PrefixControl.exact_count_and_calls (decision service F hF) _ cap

theorem structural_bounds {q w : ℕ} (service : SATService) (F : Formula (q+w))
    (hF : Width 3 F) (cap : ℕ) :
    (measured service F hF cap).calls≤1+2*q*cap ∧
    (measured service F hF cap).visits≤2*(1+2*q*cap)+1 ∧
    (measured service F hF cap).peakFrames≤q+1 := by
  have hc : (measured service F hF cap).calls≤1+2*q*cap :=
    (exact_count service F hF cap).2.trans (by gcongr; exact Nat.min_le_left _ _)
  refine ⟨hc,?_,PrefixControl.peakFrames_le _ _ _ _⟩
  exact (PrefixControl.visits_le _ _ _ _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 1)

/-- Oracle time is linear in the external SAT bound. `encoded_bound` is a
local serializer-size obligation, not a wrapper runtime assumption. -/
theorem oracle_time_bound {q w : ℕ} (service : SATService)
    (inputBits : SATRequest → ℕ) (factor time space : ℕ → ℕ)
    (hservice : ServiceBound service inputBits factor time space)
    (factor_mono : Monotone factor) (F : Formula (q+w)) (hF : Width 3 F)
    (cap encodedBound : ℕ)
    (encoded_bound : ∀ pre, pre.length≤q → inputBits (request F hF pre)≤encodedBound) :
    (measured service F hF cap).oracleTime ≤
      (1+2*q*cap)*factor encodedBound*time (q+w) := by
  have hcharge : ∀ pre : List Bool, pre.length≤q →
      (service.run (request F hF pre)).time≤factor encodedBound*time (q+w) := by
    intro pre hp
    exact (hservice _).1.trans (Nat.mul_le_mul_right _ (factor_mono (encoded_bound pre hp)))
  have ht := PrefixControl.oracleTime_le q (decision service F hF).answer
    (fun pre => (service.run (request F hF pre)).time) cap
    (factor encodedBound*time (q+w)) hcharge
  have hc := (structural_bounds service F hF cap).1
  change (measured service F hF cap).oracleTime≤
    (measured service F hF cap).calls*(factor encodedBound*time (q+w)) at ht
  calc
    _ ≤ (measured service F hF cap).calls*(factor encodedBound*time (q+w)) := ht
    _ ≤ (1+2*q*cap)*(factor encodedBound*time (q+w)) := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

theorem oracle_workspace_bound {q w : ℕ} (service : SATService)
    (inputBits : SATRequest → ℕ) (factor time space : ℕ → ℕ)
    (hservice : ServiceBound service inputBits factor time space)
    (space_mono : Monotone space) (F : Formula (q+w)) (hF : Width 3 F)
    (encodedBound : ℕ)
    (encoded_bound : ∀ pre, pre.length≤q → inputBits (request F hF pre)≤encodedBound)
    (pre : List Bool) (hlen : pre.length≤q) :
    (service.run (request F hF pre)).workspace≤space encodedBound :=
  (hservice _).2.trans (space_mono (encoded_bound pre hlen))

end QecReliability.OracleCost.PrefixSAT
