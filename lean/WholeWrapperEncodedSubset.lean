import WholeWrapperCounterSubset

/-! Input length L is the encoded bytes/bits of the immutable
problem, rational parameters, and addressed seed/hash descriptions, not inverse
precision and not number of queries. Encoding-size premises are explicit. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

private theorem self_lt_two_pow (x : ℕ) : x<2^x := by
  induction x with
  | zero => norm_num
  | succ x ih =>
      have hp : 0<2^x := pow_pos (by decide) _
      rw [pow_succ]
      omega

private theorem size_le_value (x : ℕ) : x.size≤x :=
  Nat.size_le.mpr (self_lt_two_pow x)

/-- Three source-level outputs may differ in all costs while inducing the
same retained next state. In particular T is not a stored clock register. -/
theorem step_next_ignores_costs (q r B m : ℕ) (shape : Bool) (a b : External)
    (hquery : ∀ key, (a.compileQuery key).bits=(b.compileQuery key).bits)
    (hsat : ∀ query, (a.sat query).value=(b.sat query).value)
    (hendpoint : ∀ side, (a.endpoint side).value=(b.endpoint side).value)
    (s : Config) :
    (step q r B m shape a s).map Edge.next=
      (step q r B m shape b s).map Edge.next := by
  cases hp : s.pc <;> simp [step,hp,hquery,hsat,hendpoint]

def codePolynomial (L : ℕ) : ℕ :=
  2*(L+1)*((6*L+5)*(2*L+3)+3)+1

def fieldPolynomial (L : ℕ) : ℕ := 36+18*L+3*codePolynomial L

def prefixPolynomial (L : ℕ) : ℕ := 28*L^2+78*L+32

/-- The previous rational-budget theorem supplies R≤6L+5 after input
length charges dimension extent and the raw denominator d. -/
theorem rational_trial_count_input_bound (r c d L : ℕ) (hc : 0<c)
    (hr : r≤L) (hd : d.size≤L) :
    2*rationalRepetitionBudget (2*(r+1)) c d+1≤6*L+5 := by
  have ht := rationalTrialCount_bound (K:=2*(r+1)) (d:=d) hc
  have hs := size_le_value (2*(r+1))
  omega

theorem program_length_input_bound (q r m L : ℕ)
    (hq : q≤2*L) (hr : r≤L) (hR : 2*m+1≤6*L+5) :
    (program q r m).length≤codePolynomial L := by
  rw [program_length]
  unfold coefficientCodeLength codePolynomial
  gcongr <;> omega

theorem stateListBound_input_bound (q r m L : ℕ)
    (hq : q≤2*L) (hr : r≤L) (hR : 2*m+1≤6*L+5) :
    stateListBound q r m≤fieldPolynomial L := by
  have hp := program_length_input_bound q r m L hq hr hR
  unfold stateListBound fieldPolynomial
  omega

/-- The cap contributes ONLY its binary width, despite exponential B. -/
theorem prefix_bound_input_polynomial (q B L : ℕ)
    (hq : q≤2*L) (hB : B.size≤8+2*L) :
    PrefixTransitions.configBitBound q (4*B+1)≤prefixPolynomial L := by
  have hqs : q.size≤2*L := (size_le_value q).trans hq
  have hcap : (4*B+1).size≤13+2*L := by have := cap_bit_length B; omega
  have hf : PrefixTransitions.frameBitBound q (4*B+1)≤14*L+30 := by
    unfold PrefixTransitions.frameBitBound
    omega
  have hm : q*PrefixTransitions.frameBitBound q (4*B+1)≤(2*L)*(14*L+30) :=
    Nat.mul_le_mul hq hf
  unfold PrefixTransitions.configBitBound prefixPolynomial
  nlinarith

/-- A genuine reachable-space subset polynomial in encoded L. The separate
immutable-input tape costs L in addition to these mutable fields. -/
theorem reachable_input_length_subset {q r B m L : ℕ} {shape : Bool} {ext : External}
    {s : Config} (hq : q≤2*L) (hr : r≤L) (hR : 2*m+1≤6*L+5)
    (hB : B.size≤8+2*L) (h : Reachable q r B m shape ext s) :
    (∀ f∈configFields s, f.length≤fieldPolynomial L) ∧
    (PrefixTransitions.configBits s.prefixState).length≤prefixPolynomial L ∧
    s.scaleFactor.size≤codePolynomial L+1 := by
  exact ⟨fun f hf => (reachable_field_lengths h f hf).trans
      (stateListBound_input_bound q r m L hq hr hR),
    (reachable_prefix_bit_bound h).trans (prefix_bound_input_polynomial q B L hq hB),
    (reachable_scaleFactor_size h).trans (by
      have := program_length_input_bound q r m L hq hr hR; omega)⟩

end QecReliability.OracleCost.WholeWrapperCandidate
