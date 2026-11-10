import Assembly.Instance

/-! Absorb the actual interpreter and oracle charges into uniform polynomial
envelopes. The oracle rate remains a separate argument: output cardinality is
charged only in the polynomial work factor. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.Runtime
open FL Assembly OracleCost OracleCost.MultiTape

private theorem absorb_cost (pre body post dispatch oracle Pd Po B rate : ℕ)
    (hd : dispatch ≤ Pd*(B+1)) (ho : oracle ≤ Po*(B+1)*rate) :
    pre+(dispatch+2)*body+oracle+post+1 ≤
      (pre+(Pd+2)*body+Po+post+1)*(B+1)*(rate+1) := by
  have hdm : dispatch+2 ≤ (Pd+2)*(B+1) := by nlinarith
  have hmul := Nat.mul_le_mul_right body hdm
  have hpre : pre+post+1 ≤ (pre+post+1)*(B+1) := by nlinarith
  have hfirst : pre+(dispatch+2)*body+oracle+post+1 ≤
      (pre+(Pd+2)*body+post+1)*(B+1)+Po*(B+1)*rate := by
    nlinarith only [hmul,hpre,ho]
  have hrate := Nat.zero_le ((pre+(Pd+2)*body+post+1)*(B+1)*rate)
  have hpo := Nat.zero_le (Po*(B+1))
  nlinarith only [hfirst,hrate,hpo]

/-- A generic fixed-program resource composition. The SAT rate is not absorbed
into an input polynomial, and a rate of zero still allows interpreter work. -/
theorem completion_resource_envelopes (P : FL.Program) (I : Assembly.Indices)
    (Bd : Assembly.Budget) (Pcap Pdispatch Poracle Ps : PolynomialEnvelope) (kE : ℕ) :
    ∃ Ptime Pspace : PolynomialEnvelope, ∀ L B rate cap dispatch oracle : ℕ,
      cap ≤ Pcap.eval L → dispatch ≤ Pdispatch.eval L*(B+1) →
      oracle ≤ Poracle.eval L*(B+1)*rate →
      (3*kE+6)*(preBound P I Bd L+
        (dispatch+2)*(iterBound P I Bd L+Ps.eval cap+1)+oracle+postBound P I Bd L+1) ≤
          Ptime.eval L*(B+1)*(rate+1) ∧
      (19+kE+1+1)*(2*max (regBound P I Bd L) (Ps.eval cap)+3) ≤ Pspace.eval L := by
  have hp := preBound_poly P I Bd
  have hb := iterBound_poly P I Bd
  have hz := postBound_poly P I Bd
  have hr := regBound_poly P I Bd
  have ht : PolyBounded (fun L => (3*kE+6)*(preBound P I Bd L+
      (Pdispatch.eval L+2)*(iterBound P I Bd L+Ps.eval (Pcap.eval L)+1)+
      Poracle.eval L+postBound P I Bd L+1)) := by poly_bounded
  have hs : PolyBounded (fun L => (19+kE+1+1)*
      (2*max (regBound P I Bd L) (Ps.eval (Pcap.eval L))+3)) := by poly_bounded
  obtain ⟨Pt,ht⟩ := ht.envelope
  obtain ⟨Psp,hs⟩ := hs.envelope
  refine ⟨Pt,Psp,?_⟩
  intro L B rate cap dispatch oracle hcap hd ho
  have hps : Ps.eval cap ≤ Ps.eval (Pcap.eval L) := Ps.monotone hcap
  constructor
  · have hc := absorb_cost (preBound P I Bd L)
      (iterBound P I Bd L+Ps.eval (Pcap.eval L)+1) (postBound P I Bd L)
      dispatch oracle (Pdispatch.eval L) (Poracle.eval L) B rate hd ho
    have hsmall : preBound P I Bd L+
        (dispatch+2)*(iterBound P I Bd L+Ps.eval cap+1)+oracle+postBound P I Bd L+1 ≤
        preBound P I Bd L+(dispatch+2)*(iterBound P I Bd L+Ps.eval (Pcap.eval L)+1)+
          oracle+postBound P I Bd L+1 := by gcongr
    have h := Nat.mul_le_mul_left (3*kE+6) (hsmall.trans hc)
    have he := Nat.mul_le_mul_right ((B+1)*(rate+1)) (ht L)
    simpa only [Nat.mul_assoc] using h.trans (by simpa only [Nat.mul_assoc] using he)
  · exact (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 (max_le_max le_rfl hps)) 3)).trans (hs L)

end QecReliability.TensorMachine.Runtime
