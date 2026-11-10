import LatentGateListBounds

/-! Measured output-address loop and full program parser. Bounds charge all
encoded gates, outputs, and the untouched suffix; n and r remain independent.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ParserFL
open FL FL.Lib Trans.Wire SharedCircuit
open Trans.Query Trans.Query.Bound Trans.BoundsRest
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)
open OracleCost OracleCost.WholeWrapperCandidate.InputEncoding

theorem naturals_magnitude (xs : List ℕ) (V : ℕ) (h : ∀ x ∈ xs, x ≤ V) :
    mag (.list .nat) xs ≤ xs.length*(V+1)+1 := by
  induction xs with
  | nil => simp [mag, magL]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    change x+1+mag (.list .nat) xs ≤ (xs.length+1)*(V+1)+1
    nlinarith

theorem outputs_bounds (L : Lib) (h : HIx) (i : Indices) {Q : ℕ}
    (xs : List ℕ) (rest : List Bool)
    (hQ : (xs.flatMap QueryCodec.natHeader ++ rest).length ≤ Q)
    (hN : xs.length ≤ Q) (hV : ∀ x ∈ xs, x ≤ Q) :
    (outputsF L h i).cost (xs.length,xs.flatMap QueryCodec.natHeader ++ rest) ≤ 1000*(Q+2)^3 ∧
    (outputsF L h i).depth (xs.length,xs.flatMap QueryCodec.natHeader ++ rest) ≤ 12*Q+40 ∧
    (outputsF L h i).msize (xs.length,xs.flatMap QueryCodec.natHeader ++ rest) ≤ 1000*(Q+2)^2 := by
  have hread : ∀ x rest, (hdrF L h).den (QueryCodec.natHeader x ++ rest) = (id x,rest) :=
    fun x rest => by rw [hdrF_den, hdr_natHeader]; rfl
  have hsuf : ∀ j, ((xs.drop j).flatMap QueryCodec.natHeader ++ rest).length ≤ Q :=
    fun j => (suffix_flatMap QueryCodec.natHeader xs rest j).length_le.trans hQ
  obtain ⟨c,d,m⟩ := many_bounds L (hdrF L h) i.outputStep i.outputFold i.outputMany
    QueryCodec.natHeader id hread xs rest (400*(Q+2)^2) (10*Q+20) (100*Q+100)
    (fun j _ => hdr_le L h (Q:=Q) _ (hsuf j))
  simp only [List.map_id] at m
  have hmag := naturals_magnitude xs Q hV
  have hsize := sz_bools (xs.flatMap QueryCodec.natHeader ++ rest)
  have hsquare : (xs.length+1)*(xs.length+1) ≤ (Q+2)^2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hwork := Nat.mul_le_mul_left (400*(Q+2)^2+60) hN
  have hmag' := Nat.mul_le_mul_right (Q+1) hN
  change (manyF L (hdrF L h) i.outputStep i.outputFold i.outputMany).cost _ ≤ _ ∧
    (manyF L (hdrF L h) i.outputStep i.outputFold i.outputMany).depth _ ≤ _ ∧
    (manyF L (hdrF L h) i.outputStep i.outputFold i.outputMany).msize _ ≤ _
  refine ⟨?_, by omega, ?_⟩ <;> nlinarith

theorem outputBits_as_headers {n r : ℕ} (C : SharedCircuit.Program r n) :
    outputBits C = (List.ofFn (fun j : Fin n => (C.output j).val)).flatMap QueryCodec.natHeader := by
  simp [outputBits, List.flatMap, List.map_ofFn] <;> rfl

/-- Actual sequential composition of the header, gates and output readers. -/
theorem program_bounds (L : Lib) (h : HIx) (i : Indices) {n r Q : ℕ}
    (C : SharedCircuit.Program r n) (rest : List Bool)
    (hQ : (programBits C ++ rest).length ≤ Q) (hV : n+r+C.gates ≤ Q) :
    (programF L h i).cost (n,programBits C ++ rest) ≤ 8000*(Q+2)^3 ∧
    (programF L h i).depth (n,programBits C ++ rest) ≤ 100*Q+300 ∧
    (programF L h i).msize (n,programBits C ++ rest) ≤ 10000*(Q+2)^2 := by
  let outs := List.ofFn (fun j : Fin n => (C.output j).val)
  have ho : outputBits C = outs.flatMap QueryCodec.natHeader := outputBits_as_headers C
  have hol : outs.length = n := List.length_ofFn
  have hov : ∀ x ∈ outs, x ≤ Q := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    have hj := (C.output j).isLt
    omega
  have hgQ : (circuitBits C.circuit ++ (outputBits C ++ rest)).length ≤ Q := by
    simp only [programBits, List.length_append] at hQ ⊢
    omega
  have hoQ : (outs.flatMap QueryCodec.natHeader ++ rest).length ≤ Q := by
    rw [← ho]
    simp only [List.length_append] at hgQ ⊢
    omega
  obtain ⟨hc,hd,hm⟩ := hdr_le L h (Q:=Q) (programBits C ++ rest) hQ
  obtain ⟨gc,gd,gm⟩ := gates_bounds L h i C.circuit (outputBits C ++ rest) hgQ (by omega)
  obtain ⟨oc,od,om⟩ := outputs_bounds L h i outs rest hoQ (by omega) hov
  rw [hol, ← ho] at oc od om
  have eh : hdr (programBits C ++ rest) =
      (C.gates,circuitBits C.circuit ++ (outputBits C ++ rest)) := by
    simp only [programBits, List.append_assoc, hdr_natHeader]
  have eg : (gatesF L h i).den (C.gates,circuitBits C.circuit ++ (outputBits C ++ rest)) =
      (encCirc C.circuit, outputBits C ++ rest) := by
    change (manyF L (gateF L h i.gate) i.gateStep i.gateFold i.gateMany).den _ = _
    rw [manyF_den, show (gateF L h i.gate).den = Parser.gateR from funext (gateF_den L h i.gate)]
    exact Parser.gatesR_circuitBits C.circuit _
  have eo : (outputsF L h i).den (n,outputBits C ++ rest) = (outs,rest) := by
    change (manyF L (hdrF L h) i.outputStep i.outputFold i.outputMany).den _ = _
    rw [manyF_den, show (hdrF L h).den = hdr from funext (hdrF_den L h)]
    exact Parser.outputsR_outputBits C rest
  have hgmag := circuit_magnitude C.circuit
  have homag := naturals_magnitude outs Q hov
  have zg := size_le_mag (.list GateTy) (encCirc C.circuit)
  have zo := size_le_mag (.list .nat) outs
  have zr := sz_bools rest
  have zn := nat_sz_le_self n
  have zosuf := sz_bools (outputBits C ++ rest)
  have hosuf : (outputBits C ++ rest).length ≤ Q := by
    simpa only [ho] using hoQ
  have hrlen : rest.length ≤ Q := by simp only [List.length_append] at hoQ; omega
  have hgm : C.gates*(2*(r+C.gates)+7) ≤ Q*(2*Q+7) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hom := Nat.mul_le_mul_right (Q+1) (show outs.length≤Q by omega)
  obtain ⟨hlin,hsqcube,hcubefour,hQsq,hQcube,hsqeq,hlinear⟩ := pow_facts Q
  have zgb : (Ty.enc (.list GateTy) (encCirc C.circuit)).size ≤ 100*(Q+2)^2 := by
    nlinarith only [zg, hgmag, hgm]
  have zob : (Ty.enc (.list .nat) outs).size ≤ 100*(Q+2)^2 := by
    nlinarith only [zo, homag, hom]
  refine ⟨?_, ?_, ?_⟩
  · simp only [programF, bodySig_cost, programBody, Tm.cost, Tm.den, Env.get,
      hdrF_den, eh, eg, eo, Nat.add_assoc]
    nlinarith only [hc, gc, oc, hsqcube, hlin]
  · simp only [programF, bodySig_depth, programBody, Tm.depth, Tm.den, Env.get,
      hdrF_den, eh, eg, eo]
    omega
  · simp only [programF, bodySig_msize, programBody, Tm.msize, Tm.den, Env.get,
      hdrF_den, eh, eg, eo, Ty.sz_prod, max_le_iff]
    repeat' apply And.intro
    all_goals omega

end QecReliability.LatentMachine.ParserFL
