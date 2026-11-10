import LatentContextFL
import Final.Init.Ctx

/-! Measured FL context resources. The general parsed program is retained
verbatim and charged by encoded size. Precision arithmetic is charged by bit
width, so the workspace bound has no numerical inverse-epsilon factor.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ContextFL
open FL FL.Lib Trans.Wire ParserFL
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize TCtx)

private theorem context_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem context_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

private theorem context_cost_bound {n r Q S W ns rs nns cellCost repCost seedCost : ℕ}
    (hn : ns ≤ n) (hr : rs ≤ r) (hnn : nns ≤ max ns ns + 1)
    (hnr : n+r ≤ Q) (hcell : cellCost ≤ 1000*W)
    (hrep : repCost ≤ 1000*W+1000) (hseed : seedCost ≤ S)
    (hW : 2*Q+10 ≤ W) :
    50*(ns+ns)+50*(rs+nns)+cellCost+repCost+seedCost+203 ≤ 4000*W+S := by
  omega

variable (L : Lib) (a : AIx)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams) (base den idx : ℕ)

theorem context_result_size (X : ParsedTy.den) :
    (Ty.enc (TCtx TX) ((contextF L a Fp base den idx).den X)).size ≤
      (contextF L a Fp base den idx).msize X :=
  le_max_of_le_right (le_max_right _ _)

set_option maxHeartbeats 1000000 in
theorem context_bounds (n r : ℕ) (R : TRowsW.den) (Cdata : ProgramTy.den)
    (x z c d : ℕ) (coins : List Bool) (Q S : ℕ)
    (hnr : n+r ≤ Q) (hsz : x.size+z.size+c.size+d.size ≤ Q)
    (hR : (Ty.enc TRowsW R).size ≤ 10*((2*Q+10)*(2*Q+10)))
    (hC : (Ty.enc ProgramTy Cdata).size ≤ 300*((2*Q+10)*(2*Q+10)))
    (hco : coins.length ≤ Q)
    (h1 : (seedBF L a Fp base den).cost (r+(n+n)) ≤ S)
    (h2 : (seedBF L a Fp base den).depth (r+(n+n)) ≤ S)
    (h3 : (seedBF L a Fp base den).msize (r+(n+n)) ≤ S)
    (h4 : (seedBF L a Fp base den).den (r+(n+n)) ≤ S) :
    (contextF L a Fp base den idx).cost (n,r,R,Cdata,x,z,c,d,coins) ≤
      4000*((2*Q+10)*(2*Q+10))+S ∧
    (contextF L a Fp base den idx).depth (n,r,R,Cdata,x,z,c,d,coins) ≤ 100*Q+1000+S ∧
    (contextF L a Fp base den idx).msize (n,r,R,Cdata,x,z,c,d,coins) ≤
      5000*((2*Q+10)*(2*Q+10))+10*S := by
  have sn := NatSize.size_le_self n
  have sr := NatSize.size_le_self r
  have s2 := NatSize.size_add_le n n
  have s3 := NatSize.size_add_le r (n+n)
  obtain ⟨b1,b2,b3,b4⟩ := Final.Init.cellB_le L a x z Q (by omega) (by omega)
  obtain ⟨r1,r2,r3,r4⟩ := Final.Init.repB_le L a r c d Q (by omega) (by omega) (by omega)
  have hlin : 2*Q+10 ≤ (2*Q+10)*(2*Q+10) := Nat.le_mul_of_pos_left _ (by omega)
  have hC' := hC
  simp only [ProgramTy,GateTy,Ty.sz_prod] at hC'
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [contextF,bodySig_cost,contextBody,pN,pR,pRows,pProgram,pA,pB,pC,pD,pCoins,
      Tm.cost,Tm.den,Env.one,context_get_zero,context_get_succ,addF_cost,addF_den]
    simp only [Nat.add_assoc]
    generalize (cellBF L a).cost (x,z) = cellCost at b1 ⊢
    generalize (repBF L a).cost (r,c,d) = repCost at r1 ⊢
    generalize (seedBF L a Fp base den).cost (r+(n+n)) = seedCost at h1 ⊢
    generalize (2*Q+10)*(2*Q+10) = W at b1 r1 hlin ⊢
    generalize n.size = ns at sn s2 ⊢
    generalize r.size = rs at sr ⊢
    generalize (n+n).size = nns at s2 ⊢
    clear * - sn sr s2 hnr b1 r1 h1 hlin
    calc
      _ = 50*(ns+ns)+50*(rs+nns)+cellCost+repCost+seedCost+203 := by ring
      _ ≤ _ := context_cost_bound sn sr s2 hnr b1 r1 h1 hlin
  · dsimp only [contextF,bodySig_depth,contextBody,pN,pR,pRows,pProgram,pA,pB,pC,pD,pCoins,
      Tm.depth,Tm.den,Env.one,context_get_zero,context_get_succ,addF_depth,addF_den]
    omega
  · dsimp only [contextF,bodySig_msize,contextBody,pN,pR,pRows,pProgram,pA,pB,pC,pD,pCoins,
      Tm.msize,Tm.den,Env.one,context_get_zero,context_get_succ,addF_msize,addF_den]
    simp only [max_le_iff,Ty.sz_prod]
    have zn := Final.Init.sz_enc_nat n
    have zr := Final.Init.sz_enc_nat r
    have z2 := Final.Init.sz_enc_nat (n+n)
    have z3 := Final.Init.sz_enc_nat (r+(n+n))
    have zb := Final.Init.sz_enc_nat ((cellBF L a).den (x,z))
    have zm := Final.Init.sz_enc_nat ((repBF L a).den (r,c,d))
    have zx := Final.Init.sz_enc_nat x
    have zz := Final.Init.sz_enc_nat z
    have zc := Final.Init.sz_enc_nat c
    have zd := Final.Init.sz_enc_nat d
    have zco := Trans.Bounds.sz_boolList coins
    have zseed := Trans.Bounds.sz_nat_le_self ((seedBF L a Fp base den).den (r+(n+n)))
    have sseed := NatSize.size_le_self ((seedBF L a Fp base den).den (r+(n+n)))
    obtain ⟨sv,hsv⟩ : ∃ sv : ℕ, (seedBF L a Fp base den).den (r+(n+n)) = sv := ⟨_,rfl⟩
    rw [hsv] at h4 zseed sseed ⊢
    have h4' : sv ≤ S := h4
    repeat' apply And.intro
    all_goals omega

end QecReliability.LatentMachine.ContextFL
