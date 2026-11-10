import PhysicalBridge.ExactEndpoints
import PhysicalBridge.RationalCurveEvaluator

/-! Executable nonnegative rational pairs bounded by one. Comparison selects an
existing pair, so repair does not multiply denominators in stored coefficients. -/
namespace QecReliability.RationalOutput

structure Ratio where
  num : ℕ
  den : ℕ
  den_pos : 0<den
  num_le_den : num≤den

namespace Ratio
noncomputable def value (x : Ratio) : ℝ := (x.num:ℝ)/x.den

def counts (a b : ℕ) : Ratio :=
  if h : a+b=0 then ⟨0,1,by omega,by omega⟩
  else ⟨a,a+b,Nat.pos_of_ne_zero h,Nat.le_add_right _ _⟩

theorem counts_value (a b : ℕ) : (counts a b).value=(a:ℝ)/((a:ℝ)+b) := by
  unfold counts value
  split_ifs with h
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    simp [ha,hb]
  · simp

def dyadic {n : ℕ} (rows : List (List (SharedCircuit.PauliCoord n))) (E : Finset (Fin n)) : Ratio :=
  ⟨(BinaryElimination.scorePair rows E).1,(BinaryElimination.scorePair rows E).2,
    (BinaryElimination.scorePair_valid rows E).1,(BinaryElimination.scorePair_valid rows E).2⟩

theorem dyadic_value {n : ℕ} (rows : List (List (SharedCircuit.PauliCoord n))) (E : Finset (Fin n)) :
    (dyadic rows E).value=Binary.score (SharedCircuit.rowSpace rows) E :=
  BinaryElimination.scorePair_correct rows E

theorem value_range (x : Ratio) : 0≤x.value ∧ x.value≤1 := by
  have hd : (0:ℝ)<x.den := by exact_mod_cast x.den_pos
  exact ⟨div_nonneg (Nat.cast_nonneg _) hd.le,
    (div_le_one hd).mpr (by exact_mod_cast x.num_le_den)⟩

def lesser (x y : Ratio) : Ratio := if x.num*y.den≤y.num*x.den then x else y

def greater (x y : Ratio) : Ratio := if x.num*y.den≤y.num*x.den then y else x

theorem compare_value (x y : Ratio) :
    x.num*y.den≤y.num*x.den ↔ x.value≤y.value := by
  have hx : (0:ℝ)<x.den := by exact_mod_cast x.den_pos
  have hy : (0:ℝ)<y.den := by exact_mod_cast y.den_pos
  rw [value,value,div_le_div_iff₀ hx hy]
  exact_mod_cast Iff.rfl

theorem lesser_value (x y : Ratio) : (lesser x y).value=min x.value y.value := by
  unfold lesser
  split_ifs with h
  · exact (min_eq_left ((compare_value x y).mp h)).symm
  · exact (min_eq_right (le_of_not_ge (fun hh => h ((compare_value x y).mpr hh)))).symm

theorem greater_value (x y : Ratio) : (greater x y).value=max x.value y.value := by
  unfold greater
  split_ifs with h
  · exact (max_eq_right ((compare_value x y).mp h)).symm
  · exact (max_eq_left (le_of_not_ge (fun hh => h ((compare_value x y).mpr hh)))).symm

def prefixMinimum (e : ℕ → Ratio) : ℕ → Ratio
  | 0 => e 0
  | j+1 => lesser (prefixMinimum e j) (e (j+1))

theorem prefixMinimum_value (e : ℕ → Ratio) (j : ℕ) :
    (prefixMinimum e j).value=runningMin (fun i => (e i).value) j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [prefixMinimum,lesser_value,ih,runningMin]

def payload (x : Ratio) : ℕ := x.num.size+x.den.size

theorem lesser_payload (x y : Ratio) : (lesser x y).payload≤max x.payload y.payload := by
  unfold lesser
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem greater_payload (x y : Ratio) : (greater x y).payload≤max x.payload y.payload := by
  unfold greater
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _

end Ratio
end QecReliability.RationalOutput
