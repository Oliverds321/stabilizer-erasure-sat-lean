import WholeWrapperRepresentation
import PhysicalBridge.RationalBudgets

/-! The intended SPACE variable is encoded input length, not
1/epsilon. B may be exponential in that length. These bodies bound stored
COUNTER BIT LENGTHS, never list cardinality by B or by the total call count. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

private theorem size_add_bound (x y : ℕ) : (x+y).size≤x.size+y.size+1 := by
  have hx : x<2^(x.size+y.size) := (Nat.lt_size_self x).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hy : y<2^(x.size+y.size) := (Nat.lt_size_self y).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  apply Nat.size_le.mpr
  rw [pow_succ]
  omega

theorem cap_bit_length (B : ℕ) : (4*B+1).size≤B.size+5 := by
  have hs4 : (4 : ℕ).size ≤ 3 := Nat.size_le.mpr (by norm_num)
  have ha := size_add_bound (4*B) 1
  have hm := QecReliability.size_mul_bound 4 B
  norm_num at ha hm
  omega

theorem call_counter_bit_length (q B : ℕ) :
    (trialCallCap q B).size≤2*q.size+B.size+13 := by
  have hs2 : (2 : ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
  have hc := cap_bit_length B
  have hmul1 := QecReliability.size_mul_bound 2 q
  have hmul2 := QecReliability.size_mul_bound (2*q) (4*B+1)
  have hadd1 := size_add_bound 1 (2*q*(4*B+1))
  have haddq := size_add_bound q 1
  have hmul3 := QecReliability.size_mul_bound (q+1) (1+2*q*(4*B+1))
  have hadd2 := size_add_bound 1 ((q+1)*(1+2*q*(4*B+1)))
  norm_num at hmul1 hadd1 haddq hadd2
  unfold trialCallCap prefixCallCap
  omega

def stateListBound (q r m : ℕ) : ℕ :=
  22+3*(program q r m).length+2*(q+1)+2*(2*m+1)+2*(r+1)

def stateValueBound (q r B m : ℕ) : ℕ :=
  let R := 2*m+1
  20+q+r+R+R*trialCallCap q B+2*trialValueBound q B+2*(r+1)

/-- Numeric V contains B, but the representation theorem consumes V.size.
The resulting bound depends only on B.size, not B. -/
theorem stateValueBound_bit_length (q r B m : ℕ) :
    (stateValueBound q r B m).size≤
      q+3*q.size+2*r.size+2*(2*m+1).size+2*B.size+35 := by
  let R := 2*m+1
  have hs2 : (2 : ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
  have hs20 : (20 : ℕ).size ≤ 5 := Nat.size_le.mpr (by norm_num)
  have hc := call_counter_bit_length q B
  have hcap := cap_bit_length B
  have hv := QecReliability.trialValueBound_size q B
  have hrc := QecReliability.size_mul_bound R (trialCallCap q B)
  have htv := QecReliability.size_mul_bound 2 (trialValueBound q B)
  have hr1 := size_add_bound r 1
  have hr2 := QecReliability.size_mul_bound 2 (r+1)
  have h1 := size_add_bound 20 q
  have h2 := size_add_bound (20+q) r
  have h3 := size_add_bound (20+q+r) R
  have h4 := size_add_bound (20+q+r+R) (R*trialCallCap q B)
  have h5 := size_add_bound (20+q+r+R+R*trialCallCap q B) (2*trialValueBound q B)
  have h6 := size_add_bound (20+q+r+R+R*trialCallCap q B+2*trialValueBound q B) (2*(r+1))
  norm_num at htv hr1 hr2 h1
  change (20+q+r+R+R*trialCallCap q B+2*trialValueBound q B+2*(r+1)).size≤_
  change _≤q+3*q.size+2*r.size+2*R.size+2*B.size+35
  omega

/-- These rational-precision inequalities already exist as source lemmas;
they ensure stored trial-table CARDINALITY is logarithmic in 1/delta while
counter WIDTH is logarithmic in 1/epsilon. -/
theorem rational_storage_parameters (q r a b c d : ℕ) (ha : 0<a) (hc : 0<c) :
    (rationalCellBudget a b).size≤8+2*b.size ∧
    2*rationalRepetitionBudget (2*(r+1)) c d+1≤
      2*((2*(r+1)).size+d.size)+1 ∧
    (trialValueBound q (rationalCellBudget a b)).size≤q+13+2*b.size := by
  have hb := rationalCellBudget_size (b:=b) ha
  have hr := rationalTrialCount_bound (K:=2*(r+1)) (d:=d) hc
  have hcap := cap_bit_length (rationalCellBudget a b)
  have hv := trialValueBound_size q (rationalCellBudget a b)
  exact ⟨hb,hr,by omega⟩

/-- Precise OPEN preservation target with polynomial-list-cardinality choices.
Its type deliberately does not assert an arbitrary polynomial in B is enough. -/
def InputBitLengthInvariant (q r B m Q : ℕ) (s : Config) : Prop :=
  RepresentationInvariant q B Q 22 (stateListBound q r m) (stateValueBound q r B m) s

end QecReliability.OracleCost.WholeWrapperCandidate
