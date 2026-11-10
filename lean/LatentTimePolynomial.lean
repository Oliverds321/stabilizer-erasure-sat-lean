import LatentUniformRunRefinement

/-! Concrete simplification of the executed-machine time bound. All-q broad
controller bounds are used; numerical inverse precision appears only in time,
quadratically. The SAT rate argument remains the actual padded variable bound. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open OracleCost OracleCost.WholeWrapperCandidate

/-- Includes q=0 and q=1; no iid dispatch sharpening is invoked. -/
theorem structural_work_bounds {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (a b c d : ℕ) (ha : 0<a) (hc : 0<c) :
    let L := InputEncoding.paperLength rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*(r+1)) c d
    macroDispatchBound (keySize n r) r B m+1 ≤ 4097*(L+1)^4*(B+1) ∧
    2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B ≤ 384*(L+1)^4*(B+1) := by
  let L := InputEncoding.paperLength rows C a b c d
  let B := rationalCellBudget a b
  let m := rationalRepetitionBudget (2*(r+1)) c d
  obtain ⟨_,hq,hr,hm,_⟩ := InputEncoding.budget_parameters rows C a b c d ha hc
  have hm' : m ≤ 3*L+2 := by dsimp only [m,L]; omega
  have hdisp := (Final.macroDispatchBound_mono (B:=B) hq hr hm').trans (Final.dispatchPoly_le L B)
  have hone : 1 ≤ (L+1)^4*(B+1) := Nat.succ_le_of_lt (by positivity)
  have hdp : macroDispatchBound (keySize n r) r B m+1 ≤ 4097*(L+1)^4*(B+1) := by
    nlinarith only [hdisp,hone]
  have htrial : trialCallBound (keySize n r) B ≤ trialCallBound (2*L) B := by
    unfold trialCallBound
    gcongr
  have hcalls : 2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B ≤ Final.callPoly L B := by
    unfold Final.callPoly
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hr 1)) hm) htrial
  exact ⟨hdp,hcalls.trans (Final.callPoly_le L B)⟩

/-- A uniform polynomial coefficient for the actual time expression. This is
an inequality about the checked bound, not a new resource premise. -/
theorem time_bound_polynomial (P Pt : PolynomialEnvelope) (G density F : ℕ)
    (T : ℕ → ℕ) : ∃ Q : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c →
    let L := InputEncoding.paperLength rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*(r+1)) c d
    P.eval L*(macroDispatchBound (keySize n r) r B m+1)+
      F*oracleWorkBound rows C G density B m Pt T ≤
    Q.eval L*(b/a+1)^2*
      (T (QuantumService.engineVariables rows C density (G*keySize n r))+1) := by
  have hp : Assembly.PolyBounded P.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hq : Assembly.PolyBounded (fun L => Pt.eval (InputEncoding.queryExtentPolynomial G density L)) := by
    unfold PolynomialEnvelope.eval InputEncoding.queryExtentPolynomial InputEncoding.queryPolynomial
    poly_bounded
  have hpoly : Assembly.PolyBounded (fun L => 145*(P.eval L*4097*(L+1)^4+
      F*384*(L+1)^4*Pt.eval (InputEncoding.queryExtentPolynomial G density L))) := by poly_bounded
  obtain ⟨Q,hQ⟩ := hpoly.envelope
  refine ⟨Q,?_⟩
  intro n r rows C a b c d ha hc
  dsimp only
  let L := InputEncoding.paperLength rows C a b c d
  let B := rationalCellBudget a b
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let rate := T (QuantumService.engineVariables rows C density (G*keySize n r))
  let qcap := InputEncoding.queryExtentPolynomial G density L
  let W := P.eval L*4097*(L+1)^4+F*384*(L+1)^4*Pt.eval qcap
  obtain ⟨hdisp,hcalls⟩ := structural_work_bounds rows C a b c d ha hc
  have hquery := Pt.monotone (InputEncoding.queryExtentCap_input_polynomial rows C a b c d G density)
  have hfirst : P.eval L*(macroDispatchBound (keySize n r) r B m+1) ≤
      P.eval L*(4097*(L+1)^4*(B+1))*(rate+1) :=
    (Nat.mul_le_mul_left _ hdisp).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos rate))
  have hsecond : F*oracleWorkBound rows C G density B m Pt T ≤
      F*(384*(L+1)^4*(B+1)*Pt.eval qcap*(rate+1)) := by
    unfold oracleWorkBound
    exact Nat.mul_le_mul_left F (Nat.mul_le_mul
      (Nat.mul_le_mul hcalls hquery) (Nat.le_succ rate))
  have hraw := Nat.add_le_add hfirst hsecond
  have heq : P.eval L*(4097*(L+1)^4*(B+1))*(rate+1)+
      F*(384*(L+1)^4*(B+1)*Pt.eval qcap*(rate+1)) = W*(B+1)*(rate+1) := by dsimp only [W]; ring
  rw [heq] at hraw
  have hb0 := Final.rationalCellBudget_le b ha
  have hb : B+1 ≤ 145*(b/a+1)^2 := by
    have hsq : 1 ≤ (b/a+1)^2 := Nat.succ_le_of_lt (by positivity)
    dsimp only [B]
    nlinarith only [hb0,hsq]
  have hscaled := Nat.mul_le_mul_right (rate+1) (Nat.mul_le_mul_left W hb)
  have heq' : W*(145*(b/a+1)^2)*(rate+1) = (145*W)*(b/a+1)^2*(rate+1) := by ring
  rw [heq'] at hscaled
  have hfinal := Nat.mul_le_mul_right (rate+1) (Nat.mul_le_mul_right ((b/a+1)^2) (hQ L))
  exact hraw.trans (hscaled.trans hfinal)

end QecReliability.LatentMachine.Runtime
