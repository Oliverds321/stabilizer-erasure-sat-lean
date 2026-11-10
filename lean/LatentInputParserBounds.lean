import LatentProgramParserBounds
import LatentMachineInput

/-! Full general-latent input parser: measured FL time/depth/value-size bounds
in the represented input extent, including the exact retained coin suffix.
These are compiler-facing measures, not yet the installed machine theorem.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ParserFL
open FL FL.Lib Trans.Wire SharedCircuit
open Trans.Query Trans.Query.Bound Trans.BoundsRest
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)
open OracleCost OracleCost.WholeWrapperCandidate.InputEncoding

private theorem inputParser_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem inputParser_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

theorem program_encoding_size {n r Q : ℕ} (C : SharedCircuit.Program r n)
    (hV : n+r+C.gates ≤ Q) :
    (Ty.enc ProgramTy (encProg C)).size ≤ 300*(Q+2)^2 := by
  have hg := circuit_magnitude C.circuit
  have zg := size_le_mag (.list GateTy) (encCirc C.circuit)
  have ho := naturals_magnitude (List.ofFn (fun j : Fin n => (C.output j).val)) Q
    (fun x hx => by
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      have hj := (C.output j).isLt
      omega)
  have zo := size_le_mag (.list .nat) (List.ofFn (fun j : Fin n => (C.output j).val))
  simp only [List.length_ofFn] at ho
  have hgm : C.gates*(2*(r+C.gates)+7) ≤ Q*(2*Q+7) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hom : n*(Q+1) ≤ Q*(Q+1) := Nat.mul_le_mul_right _ (by omega)
  change 1 + (Ty.enc (.list GateTy) (encCirc C.circuit)).size +
    (Ty.enc (.list .nat) (List.ofFn (fun j : Fin n => (C.output j).val))).size ≤ _
  nlinarith only [hg,zg,ho,zo,hgm,hom]

theorem precision_result_size (L : Lib) (h : HIx) (p : PIx) {Q : ℕ}
    (bs : List Bool) (hQ : bs.length ≤ Q) :
    (Ty.enc (.prod .nat (.prod .nat (.prod .nat (.prod .nat (.list .bool)))))
      ((precF L h p).den bs)).size ≤ 30*Q+30 := by
  rw [precF_den]
  have v1 := hdr_val_sz bs
  have q1 := hdr_suf_le bs hQ
  have v2 := hdr_val_sz (hdr bs).2
  have q2 := hdr_suf_le _ q1
  have v3 := hdr_val_sz (hdr (hdr bs).2).2
  have q3 := hdr_suf_le _ q2
  have v4 := hdr_val_sz (hdr (hdr (hdr bs).2).2).2
  have q4 := hdr_suf_le _ q3
  have z := sz_bools (hdr (hdr (hdr (hdr bs).2).2).2).2
  simp only [precR, Ty.sz_prod]
  omega

private theorem inputParser_cost_sum {Q S T U u1 u2 u3 u4 u5 : ℕ}
    (hQS : Q + 2 ≤ S) (hST : S ≤ T) (hTU : T ≤ U)
    (h1 : u1 ≤ 400*S) (h2 : u2 ≤ 400*S) (h3 : u3 ≤ 2000*U)
    (h4 : u4 ≤ 8000*T) (h5 : u5 ≤ 2000*S) :
    u1 + u2 + u3 + u4 + u5 + 30 ≤ 16000*U := by
  omega

set_option maxHeartbeats 1000000 in
theorem parse_bounds (L : Lib) (h : HIx) (p : PIx) (i : Indices) {n r Q : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ) (coins : List Bool)
    (hQ : (problemBits rows C a b c d ++ coins).length ≤ Q)
    (hV : n+r+C.gates ≤ Q) (hrows : rows.length+rowIncidences rows ≤ Q) :
    (parseF L h p i).cost (problemBits rows C a b c d ++ coins) ≤ 16000*(Q+2)^4 ∧
    (parseF L h p i).depth (problemBits rows C a b c d ++ coins) ≤ 120*Q+400 ∧
    (parseF L h p i).msize (problemBits rows C a b c d ++ coins) ≤ 20000*(Q+2)^2 := by
  let s4 := precisionBits a b c d ++ coins
  let s3 := programBits C ++ s4
  let s2 := rowsBits rows ++ s3
  let s1 := QueryCodec.natHeader r ++ s2
  have e0 : problemBits rows C a b c d ++ coins = QueryCodec.natHeader n ++ s1 := by
    simp only [problemBits,s1,s2,s3,s4,List.append_assoc]
  have l1 : s1.length ≤ Q := by rw [e0] at hQ; simp only [List.length_append] at hQ; omega
  have l2 : s2.length ≤ Q := by dsimp only [s1] at l1; simp only [List.length_append] at l1; omega
  have l3 : s3.length ≤ Q := by dsimp only [s2] at l2; simp only [List.length_append] at l2; omega
  have l4 : s4.length ≤ Q := by dsimp only [s3] at l3; simp only [List.length_append] at l3; omega
  have d1 : (hdrF L h).den (problemBits rows C a b c d ++ coins) = (n,s1) := by
    rw [hdrF_den,e0,hdr_natHeader]
  have d2 : (hdrF L h).den s1 = (r,s2) := by
    dsimp only [s1]; rw [hdrF_den,hdr_natHeader]
  have d3 : (rowsF L h p).den s2 = (encRows rows,s3) := by
    dsimp only [s2]; rw [rowsF_den,rowsR_rowsBits]
  have d4 : (programF L h i).den (n,s3) = (encProg C,s4) := by
    dsimp only [s3]; rw [programF_den,Parser.programR_programBits]
  obtain ⟨a1,b1,c1⟩ := hdr_le L h (Q:=Q) _ hQ
  obtain ⟨a2,b2,c2⟩ := hdr_le L h (Q:=Q) _ l1
  obtain ⟨a3,b3,c3⟩ := rows_le L h p rows s3 l2 (by omega) hrows
  obtain ⟨a4,b4,c4⟩ := program_bounds L h i C s4 l3 hV
  obtain ⟨a5,b5,c5⟩ := prec_le L h p (Q:=Q) s4 l4
  change (rowsF L h p).cost s2 ≤ 2000*(Q+2)^4 at a3
  change (rowsF L h p).depth s2 ≤ 16*Q+100 at b3
  change (rowsF L h p).msize s2 ≤ 1000*(Q+2)^2 at c3
  change (programF L h i).cost (n,s3) ≤ 8000*(Q+2)^3 at a4
  change (programF L h i).depth (n,s3) ≤ 100*Q+300 at b4
  change (programF L h i).msize (n,s3) ≤ 10000*(Q+2)^2 at c4
  obtain ⟨f1,f2,f3,f4,f5,f6,f7⟩ := pow_facts Q
  have zn := nat_sz_le_self n
  have zr := nat_sz_le_self r
  have zs3 := sz_bools s3
  have zprog := program_encoding_size C hV
  have zprog' := zprog
  simp only [ProgramTy,Ty.sz_prod] at zprog'
  have zrows : (Ty.enc TRowsW (encRows rows)).size ≤ 10*(Q+2)^2+1 := by
    have h1 := Trans.BoundsQH.sz_le TRowsW (encRows rows)
    have h2 := mag_rows_le rows
    have h3 := Nat.mul_le_mul (show rowIncidences rows≤Q by omega) (show n+2≤Q+2 by omega)
    have h4 : Q*(Q+2) ≤ (Q+2)^2 := by rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have zprec := precision_result_size L h p s4 l4
  have zprec' := zprec
  simp only [Ty.sz_prod] at zprec'
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [parseF,bodySig_cost,parseBody,Tm.cost,Tm.den,Env.one,inputParser_get_zero,inputParser_get_succ]
    rw [d1,d2,d3,d4]
    dsimp only
    simp only [Nat.add_assoc]
    generalize (hdrF L h).cost (problemBits rows C a b c d ++ coins) = u1 at a1 ⊢
    generalize (hdrF L h).cost s1 = u2 at a2 ⊢
    generalize (rowsF L h p).cost s2 = u3 at a3 ⊢
    generalize (programF L h i).cost (n,s3) = u4 at a4 ⊢
    generalize (precF L h p).cost s4 = u5 at a5 ⊢
    clear * - a1 a2 a3 a4 a5 f1 f2 f3
    calc
      _ = u1 + u2 + u3 + u4 + u5 + 30 := by
        clear * - u1 u2 u3 u4 u5
        omega
      _ ≤ _ := inputParser_cost_sum f1 f2 f3 a1 a2 a3 a4 a5
  · dsimp only [parseF,bodySig_depth,parseBody,Tm.depth,Tm.den,Env.one,inputParser_get_zero,inputParser_get_succ]
    rw [d1,d2,d3,d4]
    dsimp only
    generalize (hdrF L h).depth (problemBits rows C a b c d ++ coins) = u1 at b1 ⊢
    generalize (hdrF L h).depth s1 = u2 at b2 ⊢
    generalize (rowsF L h p).depth s2 = u3 at b3 ⊢
    generalize (programF L h i).depth (n,s3) = u4 at b4 ⊢
    generalize (precF L h p).depth s4 = u5 at b5 ⊢
    clear * - b1 b2 b3 b4 b5
    omega
  · dsimp only [parseF,bodySig_msize,parseBody,Tm.msize,Tm.den,Env.one,inputParser_get_zero,inputParser_get_succ]
    rw [d1,d2,d3,d4]
    dsimp only
    simp only [Ty.sz_prod,max_le_iff]
    generalize (hdrF L h).msize (problemBits rows C a b c d ++ coins) = u1 at c1 ⊢
    generalize (hdrF L h).msize s1 = u2 at c2 ⊢
    generalize (rowsF L h p).msize s2 = u3 at c3 ⊢
    generalize (programF L h i).msize (n,s3) = u4 at c4 ⊢
    generalize (precF L h p).msize s4 = u5 at c5 ⊢
    clear * - c1 c2 c3 c4 c5 zn zr zs3 zprog' zrows zprec' l3 hV f1 f2 f3 f7
    repeat' apply And.intro
    all_goals omega

/-- Instantiation in the actual structural input length plus ALL supplied coins. -/
theorem parse_paper_bounds (L : Lib) (h : HIx) (p : PIx) (i : Indices) {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ) (coins : List Bool) :
    let Q := paperLength rows C a b c d + coins.length
    (parseF L h p i).cost (input rows C a b c d coins) ≤ 16000*(Q+2)^4 ∧
    (parseF L h p i).depth (input rows C a b c d coins) ≤ 120*Q+400 ∧
    (parseF L h p i).msize (input rows C a b c d coins) ≤ 20000*(Q+2)^2 := by
  have hv := satExtent_le_paperLength rows C a b c d
  have hr := (paperLength_components rows C a b c d).2.2.1
  unfold satExtent circuitExtent at hv
  exact parse_bounds L h p i rows C a b c d coins
    (input_length_le rows C a b c d coins) (by omega) (by omega)

end QecReliability.LatentMachine.ParserFL
