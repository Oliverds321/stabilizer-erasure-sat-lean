import LatentContextBounds
import LatentInitializerFL
import Final.Init.Top
import Trans.BoundsRest.Endpoint

/-! Measured initializer composition, preserving binary precision and exact
rank-output bit sizes. The singleton terminal constructor never traverses the
numeric denominator; its cost/depth are fixed and its value storage is linear
in the encoded ratio size. All callee resource terms below are actual bodies. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.InitializerFL
open FL FL.Lib FL.Tm Trans.Wire Trans.Control
open ParserFL ContextFL

private theorem split_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem split_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

abbrev terminalCost : ℕ := (terminalF 0).cost (0,0)
abbrev terminalDepth : ℕ := (terminalF 0).depth (0,0)
abbrev terminalSize : ℕ := (terminalF 0).msize (0,0)

theorem terminal_cost (idx : ℕ) (v : TR.den) : (terminalF idx).cost v = terminalCost := rfl
theorem terminal_depth (idx : ℕ) (v : TR.den) : (terminalF idx).depth v = terminalDepth := by
  simp only [terminalF,bodySig_depth,terminalBody,terminalDepth,Tm.depth,Nat.max_self]

theorem terminal_size (idx : ℕ) (v : TR.den) :
    (terminalF idx).msize v ≤ terminalSize+(TR.enc v).size := by
  have sv : (TR.list.enc [v]).size = 1+(TR.enc v).size+1 := rfl
  have s0 : (TR.list.enc [(0,0)]).size = 1+(TR.enc (0,0)).size+1 := rfl
  dsimp only [terminalF,bodySig_msize,terminalBody,terminalSize,Tm.msize,Tm.den,
    Env.one,split_get_zero,split_get_succ]
  simp only [sv,s0,Ty.sz_prod,Nat.max_self,Nat.zero_max,Nat.max_zero,Nat.add_assoc]
  simp only [max_le_iff]
  all_goals repeat' apply And.intro
  all_goals omega

theorem endpoint_result_size (z : IxR) (e : Trans.BoundsRest.TEArg.den) :
    (TR.enc ((endpointF z).den e)).size ≤ (endpointF z).msize e :=
  le_max_of_le_right (le_max_right _ _)

theorem terminal_result_size (idx : ℕ) (v : TR.den) :
    (TCfg.enc ((terminalF idx).den v)).size ≤ (terminalF idx).msize v :=
  le_max_of_le_right (le_max_right _ _)

variable (L : Lib) (h : HIx) (p : PIx) (i : ParserFL.Indices) (a : AIx)
  (y : IxI) (z : IxR)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
  (base den ctxIdx terminalIdx topIdx : ℕ)

/-- Exact body decomposition with sums dominating either runtime branch.
Evaluating both terms in the mathematical bound does not execute both branches. -/
theorem initial_split (w : List Bool) (X : ParsedTy.den)
    (hX : (ParserFL.parseF L h p i).den w = X) (C : (TCtx TX).den)
    (hC : (contextF L a Fp base den ctxIdx).den X = C) :
    let I := (C.1.1,X.2.1,C.1.2.2.2)
    let E : Trans.BoundsRest.TEArg.den := ((X.1,X.2.1,X.2.2.1,X.2.2.2.1),false)
    (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).cost w ≤
      (ParserFL.parseF L h p i).cost w+(contextF L a Fp base den ctxIdx).cost X+
        (initF y).cost I+(endpointF z).cost E+terminalCost+100 ∧
    (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).depth w ≤
      (ParserFL.parseF L h p i).depth w+(contextF L a Fp base den ctxIdx).depth X+
        (initF y).depth I+(endpointF z).depth E+terminalDepth+20 ∧
    (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).msize w ≤
      (ParserFL.parseF L h p i).msize w+2*(contextF L a Fp base den ctxIdx).msize X+
        2*(initF y).msize I+3*(endpointF z).msize E+2*terminalSize+
        2*((Ty.prod .nat (.prod .nat .nat)).enc I).size+
        2*(Trans.BoundsRest.TEArg.enc E).size+100 := by
  dsimp only
  let I := (C.1.1,X.2.1,C.1.2.2.2)
  let E : Trans.BoundsRest.TEArg.den := ((X.1,X.2.1,X.2.2.1,X.2.2.2.1),false)
  have hc := context_result_size L a Fp base den ctxIdx X
  rw [hC] at hc
  have hi := Final.Init.init_res_le y I
  have he := endpoint_result_size z E
  have ht := terminal_size terminalIdx ((endpointF z).den E)
  have htr := terminal_result_size terminalIdx ((endpointF z).den E)
  have htc := terminal_cost terminalIdx ((endpointF z).den E)
  have htd := terminal_depth terminalIdx ((endpointF z).den E)
  dsimp only [I,E] at hi he ht htr htc htd
  have hIs : ((Ty.prod .nat (.prod .nat .nat)).enc I).size =
      1+(Ty.nat.enc C.1.1).size+((Ty.prod .nat .nat).enc (X.2.1,C.1.2.2.2)).size := rfl
  have hEs : ((Ty.prod (.prod .nat (.prod .nat (.prod TRowsP TProgP))) .bool).enc E).size =
      1+((Ty.prod .nat (.prod .nat (.prod TRowsP TProgP))).enc E.1).size+
        (Ty.bool.enc false).size := rfl
  have hEsOpaque : (Trans.BoundsRest.TEArg.enc E).size =
      1+((Ty.prod .nat (.prod .nat (.prod TRowsP TProgP))).enc E.1).size+
        (Ty.bool.enc false).size := rfl
  have hE1 := Ty.sz_prod .nat (.prod .nat (.prod TRowsP TProgP)) E.1
  have hE2 := Ty.sz_prod .nat (.prod TRowsP TProgP) E.1.2
  have hE3 := Ty.sz_prod TRowsP TProgP E.1.2.2
  dsimp only [I,E] at hIs hEs hEsOpaque hE1 hE2 hE3
  refine ⟨?_,?_,?_⟩
  · dsimp only [initialF,bodySig_cost,initialBody,Tm.cost,Tm.den,
      Env.one,split_get_zero,split_get_succ,pN,pR,pRows,pProgram]
    rw [hX,hC]
    clear hc hi he ht htr htd hIs hEs hEsOpaque hE1 hE2 hE3 hX hC
    generalize (ParserFL.parseF L h p i).cost w = pc
    generalize (contextF L a Fp base den ctxIdx).cost X = cc
    generalize (initF y).cost (C.1.1,X.2.1,C.1.2.2.2) = ic
    generalize (endpointF z).cost
      ((X.1,X.2.1,X.2.2.1,X.2.2.2.1),false) = ec
    generalize (terminalF terminalIdx).cost ((endpointF z).den
      ((X.1,X.2.1,X.2.2.1,X.2.2.2.1),false)) = tc at htc ⊢
    generalize terminalCost = tc0 at htc ⊢
    split_ifs <;> simp only [Nat.add_assoc] <;> omega
  · dsimp only [initialF,bodySig_depth,initialBody,Tm.depth,Tm.den,
      Env.one,split_get_zero,split_get_succ,pN,pR,pRows,pProgram]
    rw [hX,hC]
    clear hc hi he ht htr htc hIs hEs hEsOpaque hE1 hE2 hE3 hX hC
    generalize (ParserFL.parseF L h p i).depth w = pd
    generalize (contextF L a Fp base den ctxIdx).depth X = cd
    generalize (initF y).depth (C.1.1,X.2.1,C.1.2.2.2) = id
    generalize (endpointF z).depth
      ((X.1,X.2.1,X.2.2.1,X.2.2.2.1),false) = ed
    generalize (terminalF terminalIdx).depth ((endpointF z).den
      ((X.1,X.2.1,X.2.2.1,X.2.2.2.1),false)) = td at htd ⊢
    generalize terminalDepth = td0 at htd ⊢
    split_ifs <;> omega
  · dsimp only [initialF,bodySig_msize,initialBody,Tm.msize,Tm.den,
      Env.one,split_get_zero,split_get_succ,pN,pR,pRows,pProgram]
    rw [hX,hC,Ty.sz_prod (TCtx TX) TCfg]
    clear htc htd hX hC
    split_ifs <;> simp only [max_le_iff]
    all_goals repeat' apply And.intro
    all_goals omega

end QecReliability.LatentMachine.InitializerFL
