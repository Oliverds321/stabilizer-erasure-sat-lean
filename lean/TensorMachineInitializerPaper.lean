import TensorMachineInitializerBounds
import TensorMachineContextSpace
import TensorMachineGridEnvelope
import TensorMachineProgram
import LatentInitializerBudget

/-! Actual tensor initializer bounds. The size parameter charges the input,
class list and complete coefficient table. Precision values are charged by
binary length, including when their numerical values are large. -/

set_option autoImplicit false
set_option maxRecDepth 2048
namespace QecReliability.TensorMachine.InitializerFL
open FL FL.Lib FL.Tm Trans.Wire Trans.Control Trans.Query Trans.Query.Bound
open Trans.BoundsQH Trans.BoundsRest SharedCircuit SharedCircuit.LatentEncoding
open OracleCost OracleCost.WholeWrapperCandidate InputEncoding

private theorem lookup_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl
private theorem lookup_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

/-- Shared arithmetic/list-callee budget, independent of runtime inputs. -/
def basicBudget (N : ℕ) : ℕ :=
  1000000*(N+2)^4 + G 2 300 (100*(N+2)^3)

def initialBudget (N Gd Sd Id : ℕ) : ℕ :=
  10000*(basicBudget N+Gd+Sd+Id)

theorem basicBudget_polynomial : Assembly.PolyBounded basicBudget := by
  have hg := G_comp_pb 2 300 (show Assembly.PolyBounded (fun N => 100*(N+2)^3) by poly_bounded)
  unfold basicBudget
  poly_bounded

private theorem basic_small (N : ℕ) :
    50000*(N+2)^2+20000*(N+2)^3+20000*(N+2)^4+
      10000*((2*N+10)*(2*N+10))+10000*N+10000 ≤ basicBudget N := by
  have h2 : (N+2)^2 ≤ (N+2)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (N+2)^3 ≤ (N+2)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn : N ≤ (N+2)^4 := (show N≤(N+2)^2 by nlinarith).trans h2
  have h1 : 1 ≤ (N+2)^4 := Nat.one_le_pow _ _ (by omega)
  have ht : (2*N+10)*(2*N+10) ≤ 25*(N+2)^4 := by
    calc
      _ ≤ (5*(N+2))*(5*(N+2)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 25*(N+2)^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2
  unfold basicBudget
  omega

private theorem old_parser_result (L : Lib) (h : HIx) (wp : PIx)
    (p : LatentMachine.ParserFL.Indices) (bs : List Bool) :
    (Ty.enc LatentMachine.ParserFL.ParsedTy ((LatentMachine.ParserFL.parseF L h wp p).den bs)).size ≤
      (LatentMachine.ParserFL.parseF L h wp p).msize bs := by
  dsimp only [LatentMachine.ParserFL.ParsedTy,LatentMachine.ParserFL.parseF,bodySig_den,bodySig_msize,
    LatentMachine.ParserFL.parseBody,Tm.msize,Tm.den,Env.one,lookup_zero,lookup_succ]
  omega

set_option maxHeartbeats 2000000 in
theorem parser_resources (L : Lib) (h : HIx) (wp : PIx)
    (p : LatentMachine.ParserFL.Indices) (di pi : ℕ) {ds : List ℕ} {n N : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ) (coins : List Bool)
    (hw : (input ds rows C a b c d coins).length ≤ N)
    (hdim : n+ds.sum+C.gates ≤ N) (hr : rows.length+rowIncidences rows ≤ N)
    (hlen : ds.length ≤ N) :
    let F := ParserFL.parseF L h wp p di pi
    let w := input ds rows C a b c d coins
    F.cost w ≤ basicBudget N ∧ F.depth w ≤ basicBudget N ∧
      F.msize w ≤ basicBudget N ∧ (Ty.enc ParserFL.ParsedTy (F.den w)).size ≤ basicBudget N := by
  dsimp only
  have hrest : (problemBits rows C a b c d ++ coins).length ≤ N := by
    simp only [input,LatentMachine.input,List.length_append] at hw ⊢
    omega
  obtain ⟨d1,d2,d3⟩ := ParserFL.degrees_bounds L h p di ds
    (problemBits rows C a b c d ++ coins) hw hlen
    (fun r hr => (List.single_le_sum (fun _ _ => Nat.zero_le _) r hr).trans (by omega))
  obtain ⟨p1,p2,p3⟩ := LatentMachine.ParserFL.parse_bounds L h wp p rows C a b c d coins hrest hdim hr
  obtain ⟨t1,t2,t3⟩ := ParserFL.parse_composition L h wp p di pi ds
    (problemBits rows C a b c d ++ coins)
  have zd := sz_le (.list .nat) ds
  rw [GridFL.natList_mag] at zd
  have zr := sz_bools (problemBits rows C a b c d ++ coins)
  have zp := old_parser_result L h wp p (problemBits rows C a b c d ++ coins)
  rw [LatentMachine.ParserFL.parseF_problemBits] at zp
  have zfull : (Ty.enc ParserFL.ParsedTy ((ParserFL.parseF L h wp p di pi).den
      (input ds rows C a b c d coins))).size ≤
        (Ty.enc (.list .nat) ds).size+20000*(N+2)^2+1 := by
    rw [ParserFL.parseF_den,parse_input]
    change 1 + (Ty.enc (.list .nat) ds).size + _ ≤ _
    dsimp only
    omega
  have hb := basic_small N
  simp only [input,LatentMachine.input] at zfull ⊢
  refine ⟨?_,?_,?_,?_⟩ <;> omega

set_option maxHeartbeats 2000000 in
theorem context_resources (L : Lib) (aI : AIx) (gi : GridFL.Indices)
    (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
    (base den oldCtx lengthIdx ctxIdx : ℕ) {ds : List ℕ} {n N Gd Sd : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ) (coins : List Bool)
    (hdim : n+ds.sum+C.gates ≤ N) (hr : rows.length+rowIncidences rows ≤ N)
    (hprec : a.size+b.size+c.size+d.size ≤ N) (hcoins : coins.length ≤ N)
    (hlen : ds.length ≤ N) (hslots : slots ds ≤ N)
    (hp : (Ty.enc ParserFL.ParsedTy (ds,n,ds.sum,encRows rows,encProg C,a,b,c,d,coins)).size ≤ basicBudget N)
    (hg : (GridFL.gridF L gi).cost ds ≤ Gd ∧ (GridFL.gridF L gi).depth ds ≤ Gd ∧
      (GridFL.gridF L gi).msize ds ≤ Gd ∧ (Ty.enc GridFL.Table (grid ds)).size ≤ Gd)
    (hs : (seedBF L aI Fp base den).cost (keySize n ds.sum) ≤ Sd ∧
      (seedBF L aI Fp base den).depth (keySize n ds.sum) ≤ Sd ∧
      (seedBF L aI Fp base den).msize (keySize n ds.sum) ≤ Sd ∧
      (seedBF L aI Fp base den).den (keySize n ds.sum) ≤ Sd) :
    let p : ParserFL.ParsedTy.den := (ds,n,ds.sum,encRows rows,encProg C,a,b,c,d,coins)
    let F := ContextFL.contextF L aI gi Fp base den oldCtx lengthIdx ctxIdx
    let R := basicBudget N+Gd+Sd
    F.cost p ≤ 2000*R ∧ F.depth p ≤ 2000*R ∧ F.msize p ≤ 2000*R := by
  dsimp only
  have hb := basic_small N
  have hrow := Final.Init.rows_sz_le rows (show n≤N by omega) hr
  have hprog := (LatentMachine.InitializerFL.data_bounds rows C hdim hr).1
  obtain ⟨o1,o2,o3⟩ := LatentMachine.ContextFL.context_bounds L aI Fp base den oldCtx
    n ds.sum (encRows rows) (encProg C) a b c d coins N Sd (by omega) hprec hrow hprog
    hcoins hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have oz := LatentMachine.ContextFL.context_result_size L aI Fp base den oldCtx
    (n,ds.sum,encRows rows,encProg C,a,b,c,d,coins)
  have hm := GridFL.grid_magnitude ds
  have hm' : mag GridFL.Table (grid ds) ≤ 100*(N+2)^3 := by
    have hx : slots ds*(ds.length*(ds.sum+1)+2)+1 ≤ N*(N*(N+1)+2)+1 := by
      gcongr
      omega
    nlinarith
  obtain ⟨l1,l2,l3,_⟩ := lengthF_B GridFL.Row lengthIdx (grid ds)
  have lg := G_mono (k:=2) (c:=300) le_rfl le_rfl hm'
  have l1' := l1.trans lg
  have l2' := l2.trans lg
  have l3' := l3.trans lg
  obtain ⟨v1,v2,v3,_⟩ := predF_B L.pred (slots ds)
  have vg := G_mono (k:=2) (c:=300) le_rfl le_rfl
    (show mag .nat (slots ds) ≤ 100*(N+2)^3 by change slots ds ≤ _; nlinarith)
  have v1' := v1.trans vg
  have v2' := v2.trans vg
  have v3' := v3.trans vg
  have hvsz : (slots ds-1).size ≤ N := (NatSize.size_le_self _).trans (by omega)
  obtain ⟨r1,r2,r3,r4⟩ := Final.Init.repB_le L aI (slots ds-1) c d N hvsz (by omega) (by omega)
  have rz := Final.Init.sz_enc_nat ((repBF L aI).den (slots ds-1,c,d))
  have lz := Trans.Bounds.sz_nat_le_self (slots ds)
  have vz := Trans.Bounds.sz_nat_le_self (slots ds-1)
  have hc := ContextFL.context_cost L aI gi Fp base den oldCtx lengthIdx ctxIdx
    (ds,n,ds.sum,encRows rows,encProg C,a,b,c,d,coins)
  have hd := ContextFL.context_depth L aI gi Fp base den oldCtx lengthIdx ctxIdx
    (ds,n,ds.sum,encRows rows,encProg C,a,b,c,d,coins)
  have hz := ContextFL.context_msize L aI gi Fp base den oldCtx lengthIdx ctxIdx
    (ds,n,ds.sum,encRows rows,encProg C,a,b,c,d,coins)
  simp only [ContextFL.contextCost,ContextFL.contextDepth,ContextFL.contextSpace,
    GridFL.gridF_den,lengthF_den,grid_length,predF_den] at hc hd hz
  have hj : G 2 300 (100*(N+2)^3) ≤ basicBudget N := by unfold basicBudget; omega
  simp only [Ty.enc_nat] at lz vz rz
  have hr1 : (repBF L aI).cost (slots ds-1,c,d) ≤ basicBudget N := r1.trans (by omega)
  have hr2 : (repBF L aI).depth (slots ds-1,c,d) ≤ basicBudget N := r2.trans (by omega)
  have hr3 : (repBF L aI).msize (slots ds-1,c,d) ≤ basicBudget N := r3.trans (by omega)
  refine ⟨?_,?_,?_⟩ <;> omega

set_option maxHeartbeats 2000000 in
theorem initial_paper_bounds (source : FL.Program) (base den : ℕ)
    {Kg Cg Ks Cs Ki Ci : ℕ}
    (hg : ∀ ds N, ds.sum≤N → ds.length≤N → slots ds≤N →
      (GridFL.gridF Install.wL Installed.gridIndices).cost ds ≤ GridFL.gridBudget Kg Cg N ∧
      (GridFL.gridF Install.wL Installed.gridIndices).depth ds ≤ GridFL.gridBudget Kg Cg N ∧
      (GridFL.gridF Install.wL Installed.gridIndices).msize ds ≤ GridFL.gridBudget Kg Cg N ∧
      (Ty.enc GridFL.Table (grid ds)).size ≤ GridFL.gridBudget Kg Cg N)
    (hs : ∀ q, FnBAt (G Ks Cs) (seedBF Install.wL Install.wA Install.paramsFn base den) q)
    (hi : FnB (G Ki Ci) (initF Install.yI)) {n N : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ) (coins : List Bool)
    (hw : (input ds rows C a b c d coins).length≤N)
    (hdim : n+ds.sum+C.gates≤N) (hr : rows.length+rowIncidences rows≤N)
    (hprec : a.size+b.size+c.size+d.size≤N) (hlen : ds.length≤N) (hslots : slots ds≤N)
    (hm : rationalRepetitionBudget (2*slots ds) c d ≤ 3*N+2) :
    let F := Program.initializer source base den
    let w := input ds rows C a b c d coins
    let B := initialBudget N (GridFL.gridBudget Kg Cg N) (G Ks Cs (2*N)) (G Ki Ci (7*N+5))
    F.cost w≤B ∧ F.depth w≤B ∧ F.msize w≤B ∧ ((Ty.list .bool).enc w).size≤B := by
  let parser := ParserFL.parseF Install.wL Install.wH Install.wP
    LatentMachine.ParserInstalled.indices Installed.degreesIdx Installed.parseIdx
  let ctx := Program.context source base den
  let w := input ds rows C a b c d coins
  have he : parser.den w = (ds,n,ds.sum,encRows rows,encProg C,a,b,c,d,coins) := by
    simp only [parser,w,ParserFL.parseF_den,parse_input]
  obtain ⟨p1,p2,p3,p4⟩ := parser_resources Install.wL Install.wH Install.wP
    LatentMachine.ParserInstalled.indices Installed.degreesIdx Installed.parseIdx rows C a b c d coins hw hdim hr hlen
  have hP : (Ty.enc ParserFL.ParsedTy (ds,n,ds.sum,encRows rows,encProg C,a,b,c,d,coins)).size ≤ basicBudget N := by
    simpa only [ParserFL.parseF_den,parse_input] using p4
  have hco : coins.length≤N := by rw [input_length] at hw; omega
  have hq : keySize n ds.sum≤2*N := by unfold keySize; omega
  obtain ⟨s1,s2,s3,s4⟩ := hs (keySize n ds.sum)
  have sg := G_mono (k:=Ks) (c:=Cs) le_rfl le_rfl hq
  obtain ⟨c1,c2,c3⟩ := context_resources Install.wL Install.wA Installed.gridIndices Install.paramsFn
    base den 295 13 (source.length+9) rows C a b c d coins hdim hr hprec hco hlen hslots hP
    (hg ds N (by omega) hlen hslots) ⟨s1.trans sg,s2.trans sg,s3.trans sg,s4.trans sg⟩
  have ec := ContextFL.context_den Install.wL Install.wA Installed.gridIndices Install.paramsFn
    base den 295 13 (source.length+9) (fun _ => rfl) ds rows C a b c d coins
  have zc := ContextFL.context_result_size Install.wL Install.wA Installed.gridIndices Install.paramsFn
    base den 295 13 (source.length+9) (parser.den w)
  obtain ⟨t1,t2,t3⟩ := initial_split parser ctx Install.yI (source.length+10) w zc
  rw [he] at t1 t2 t3
  change ctx.den _ = _ at ec
  rw [ec] at t1 t2 t3
  dsimp only [encCtx] at t1 t2 t3
  let I := (keySize n ds.sum,slots ds-1,rationalRepetitionBudget (2*slots ds) c d)
  have hI : mag (.prod .nat (.prod .nat .nat)) I ≤ 7*N+5 := by
    change keySize n ds.sum+(slots ds-1+rationalRepetitionBudget (2*slots ds) c d+1)+1≤_
    omega
  obtain ⟨i1,i2,i3,_⟩ := hi I
  have ig := G_mono (k:=Ki) (c:=Ci) le_rfl le_rfl hI
  have i1' := i1.trans ig
  have i2' := i2.trans ig
  have i3' := i3.trans ig
  have zi := sz_le (.prod .nat (.prod .nat .nat)) I
  have zw := sz_bools w
  have hb := basic_small N
  change _ ≤ initialBudget N _ _ _ ∧ _
  unfold initialBudget
  dsimp only [Program.initializer,Program.context,parser,ctx,w,I] at t1 t2 t3 p1 p2 p3 c1 c2 c3 i1' i2' i3' zi zw hI ⊢
  refine ⟨?_,?_,?_,?_⟩ <;> omega

end QecReliability.TensorMachine.InitializerFL
