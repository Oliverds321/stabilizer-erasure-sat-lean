import PhysicalBridge.PhysicalShapeConfidence

/-! Executable integer budgets. No real ceiling or noncomputable search occurs
in these definitions; real-valued inequalities are proved specifications. -/
namespace QecReliability

def ceilDiv (x y : ℕ) : ℕ := (x+y-1)/y

theorem ceilDiv_le_iff {x y v : ℕ} (hy : 0<y) : ceilDiv x y≤v ↔ x≤y*v := by
  unfold ceilDiv
  rw [←Nat.lt_succ_iff,Nat.div_lt_iff_lt_mul hy,Nat.succ_mul,Nat.mul_comm v y]
  omega

theorem ceilDiv_pos {x y : ℕ} (hx : 0<x) (hy : 0<y) : 0<ceilDiv x y := by
  have h := ceilDiv_le_iff (x:=x) (v:=0) hy
  simp only [Nat.mul_zero,Nat.le_zero] at h
  omega

theorem ceilDiv_spec {x y : ℕ} (hy : 0<y) : x≤y*ceilDiv x y :=
  (ceilDiv_le_iff hy).mp le_rfl

theorem ceilDiv_le_self {x y : ℕ} (hy : 0<y) : ceilDiv x y≤x := by
  apply (ceilDiv_le_iff hy).mpr
  nlinarith

theorem size_mul_bound (x y : ℕ) : (x*y).size≤x.size+y.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self x) (Nat.lt_size_self y)

def rationalCellBudget (a b : ℕ) : ℕ := ceilDiv (144*b*b) (a*a)

theorem rationalCellBudget_pos {a b : ℕ} (ha : 0<a) (hb : 0<b) :
    0<rationalCellBudget a b := ceilDiv_pos (by positivity) (by positivity)

theorem rationalCellBudget_integer_spec {a b : ℕ} (ha : 0<a) :
    144*b*b≤a*a*rationalCellBudget a b := ceilDiv_spec (by positivity)

theorem rationalCellBudget_le {a b : ℕ} (ha : 0<a) :
    rationalCellBudget a b≤144*b*b := ceilDiv_le_self (by positivity)

theorem rationalCellBudget_size {a b : ℕ} (ha : 0<a) :
    (rationalCellBudget a b).size≤8+2*b.size := by
  have h1 := Nat.size_le_size (rationalCellBudget_le (b:=b) ha)
  have h2 := size_mul_bound (144*b) b
  have h3 := size_mul_bound 144 b
  have h144 : (144:ℕ).size≤8 := Nat.size_le.mpr (by norm_num)
  omega

theorem rational_epsilon {a b : ℕ} (ha : 0<a) (hb : 0<b) (hab : a≤b) :
    0<(a:ℝ)/b ∧ (a:ℝ)/b≤1 := by
  have hb' : (0:ℝ)<b := by exact_mod_cast hb
  exact ⟨div_pos (by exact_mod_cast ha) hb',(div_le_one hb').mpr (by exact_mod_cast hab)⟩

theorem rationalCellBudget_spec {a b : ℕ} (ha : 0<a) (hb : 0<b) :
    16≤(((a:ℝ)/b)/3)^2*(rationalCellBudget a b:ℝ) := by
  have hi : (144:ℝ)*b*b≤(a:ℝ)*a*rationalCellBudget a b := by
    exact_mod_cast rationalCellBudget_integer_spec (b:=b) ha
  have hb' : (0:ℝ)<b := by exact_mod_cast hb
  have h : (16:ℝ)≤((a:ℝ)*a*rationalCellBudget a b)/(9*b^2) :=
    (le_div_iff₀ (show (0:ℝ)<9*b^2 by positivity)).mpr (by nlinarith [hi])
  convert h using 1
  field_simp
  ring

def rationalRepetitionTarget (K c d : ℕ) : ℕ := ceilDiv (K*d) c

def rationalRepetitionBudget (K c d : ℕ) : ℕ := (rationalRepetitionTarget K c d-1).size-2

theorem size_pred_le_iff {z e : ℕ} (hz : 0<z) : (z-1).size≤e ↔ z≤2^e := by
  rw [Nat.size_le]
  omega

theorem rationalRepetitionBudget_le_iff_integer {K c d t : ℕ}
    (hK : 0<K) (hc : 0<c) (hd : 0<d) :
    rationalRepetitionBudget K c d≤t ↔ K*d≤c*2^(t+2) := by
  have hz : 0<rationalRepetitionTarget K c d := ceilDiv_pos (by positivity) hc
  unfold rationalRepetitionBudget
  rw [Nat.sub_le_iff_le_add,size_pred_le_iff hz]
  exact ceilDiv_le_iff hc

theorem rational_failure_iff {K c d t : ℕ} (hd : 0<d) :
    (K:ℝ)*(1/2:ℝ)^(t+2)≤(c:ℝ)/d ↔ K*d≤c*2^(t+2) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hp : (0:ℝ)<2^(t+2) := by positivity
  rw [one_div_pow,mul_one_div,div_le_div_iff₀ hp hd']
  exact_mod_cast Iff.rfl

/-- Minimal for this source failure inequality, not optimal statistical repetitions. -/
theorem rationalRepetitionBudget_le_iff {K c d t : ℕ}
    (hK : 0<K) (hc : 0<c) (hd : 0<d) :
    rationalRepetitionBudget K c d≤t ↔ (K:ℝ)*(1/2:ℝ)^(t+2)≤(c:ℝ)/d :=
  (rationalRepetitionBudget_le_iff_integer hK hc hd).trans (rational_failure_iff hd).symm

theorem rationalRepetitionBudget_spec {K c d : ℕ}
    (hK : 0<K) (hc : 0<c) (hd : 0<d) :
    (K:ℝ)*(1/2:ℝ)^(rationalRepetitionBudget K c d+2)≤(c:ℝ)/d :=
  (rationalRepetitionBudget_le_iff hK hc hd).mp le_rfl

theorem rationalRepetitionBudget_minimal {K c d t : ℕ}
    (hK : 0<K) (hc : 0<c) (hd : 0<d)
    (ht : (K:ℝ)*(1/2:ℝ)^(t+2)≤(c:ℝ)/d) : rationalRepetitionBudget K c d≤t :=
  (rationalRepetitionBudget_le_iff hK hc hd).mpr ht

theorem rationalRepetitionBudget_eq_source {K c d : ℕ}
    (hK : 0<K) (hc : 0<c) (hd : 0<d) :
    rationalRepetitionBudget K c d = repetitionBudget K ((c:ℝ)/d)
      (div_pos (by exact_mod_cast hc) (by exact_mod_cast hd)) := by
  apply Nat.le_antisymm
  · exact rationalRepetitionBudget_minimal hK hc hd (repetitionBudget_spec _ _ _)
  · exact repetitionBudget_minimal _ _ _ (rationalRepetitionBudget_spec hK hc hd)

theorem rationalRepetitionBudget_size_bound {K c d : ℕ} (hc : 0<c) :
    rationalRepetitionBudget K c d≤K.size+d.size := by
  have hz : rationalRepetitionTarget K c d≤K*d := ceilDiv_le_self hc
  have hs := Nat.size_le_size ((Nat.sub_le (rationalRepetitionTarget K c d) 1).trans hz)
  have hm := Nat.sub_le (rationalRepetitionTarget K c d-1).size 2
  exact hm.trans (hs.trans (size_mul_bound K d))

theorem rationalTrialCount_bound {K c d : ℕ} (hc : 0<c) :
    2*rationalRepetitionBudget K c d+1≤2*(K.size+d.size)+1 := by
  have h := rationalRepetitionBudget_size_bound (K:=K) (d:=d) hc
  omega

theorem rationalRepetitionBudget_bit_size {K c d : ℕ} (hc : 0<c) :
    (rationalRepetitionBudget K c d).size≤(K.size+d.size).size :=
  Nat.size_le_size (rationalRepetitionBudget_size_bound hc)

/-- Includes large confidence tolerances; the number of seeds is still one. -/
theorem rationalRepetitionBudget_zero_iff {K c d : ℕ}
    (hK : 0<K) (hc : 0<c) (hd : 0<d) :
    rationalRepetitionBudget K c d=0 ↔ K*d≤4*c := by
  simpa [Nat.mul_comm] using
    rationalRepetitionBudget_le_iff_integer (t:=0) hK hc hd

end QecReliability
