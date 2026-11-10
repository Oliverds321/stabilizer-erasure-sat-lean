import LatentInitializerSplit
import LatentArgumentMagnitude

/-! Actual initializer resource bounds on arbitrary latent circuit inputs. Q
charges the structural instance extent and every supplied coin bit. Numeric B
and the endpoint denominator do not enter this workspace envelope. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.InitializerFL
open FL FL.Lib Trans.Wire Trans.Control Trans.Query Trans.Query.Bound
open Trans.BoundsQH Trans.BoundsRest ParserFL ContextFL
open SharedCircuit SharedCircuit.LatentEncoding
open OracleCost OracleCost.WholeWrapperCandidate
open InputEncoding

/-- Polynomial-sized circuit and endpoint arguments, including all wire occurrences. -/
theorem data_bounds {n r Q : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (hdim : n+r+C.gates ≤ Q)
    (hrows : rows.length+rowIncidences rows ≤ Q) :
    (WProg.enc (encProg C)).size ≤ 300*((2*Q+10)*(2*Q+10)) ∧
    mag TEArg ((n,r,encRows rows,encProg C),false) ≤ 10*(Q+2)^2 := by
  have hr := mag_rows_le rows
  have hp := ArgumentMagnitude.program_magnitude C
  have hz := sz_le WProg (encProg C)
  have hrp := Nat.mul_le_mul (show rowIncidences rows≤Q by omega) (show n+2≤Q+2 by omega)
  have hgp := Nat.mul_le_mul (show C.gates≤Q by omega) (show 2*(r+C.gates)+7≤2*Q+7 by omega)
  have hop := Nat.mul_le_mul (show n≤Q by omega) (show r+C.gates+1≤Q+1 by omega)
  have hr' : mag TRowsW (encRows rows) ≤ Q*(Q+2)+2*Q+1 := by omega
  have hp' : mag WProg (encProg C) ≤ Q*(2*Q+7)+Q*(Q+1)+3 := by omega
  refine ⟨?_,?_⟩
  · nlinarith only [hz,hp']
  · change n+(r+(mag TRowsW (encRows rows)+mag WProg (encProg C)+1)+1)+1+1+1 ≤ _
    nlinarith only [hr',hp',hdim]

def initialBudget (Q S I E : ℕ) : ℕ :=
  16000*(Q+2)^4+40000*(Q+2)^2+20000*((2*Q+10)*(2*Q+10))+
    20*S+20*I+20*E+terminalCost+terminalDepth+2*terminalSize+1000

variable (L : Lib) (h : HIx) (p : PIx) (i : ParserFL.Indices) (a : AIx)
  (y : IxI) (z : IxR)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
  (base den ctxIdx terminalIdx topIdx : ℕ)

/-- All callee bounds refer to actual signatures; the endpoint premise is
resource-only and never asserts a bound on its exponentially large value. -/
theorem initial_paper_bounds
    (hFp : ∀ x, Fp.den x = (Trans.Hash.params x.1 x.2.1 x.2.2).tuple)
    {Ks Cs Ki Ci Ke Ce : ℕ}
    (hs : ∀ q, FnBAt (G Ks Cs) (seedBF L a Fp base den) q)
    (hi : FnB (G Ki Ci) (initF y))
    (he : FnB (G Ke Ce) (cdmSig (endpointF z)))
    {n r : ℕ} (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (x b c d : ℕ) (coins : List Bool) (hx : 0<x) (hc : 0<c) :
    let Q := paperLength rows C x b c d+coins.length
    let B := initialBudget Q (G Ks Cs (2*Q)) (G Ki Ci (7*Q+5)) (G Ke Ce (10*(Q+2)^2))
    (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).cost
        (input rows C x b c d coins) ≤ B ∧
    (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).depth
        (input rows C x b c d coins) ≤ B ∧
    (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).msize
        (input rows C x b c d coins) ≤ B ∧
    ((Ty.list .bool).enc (input rows C x b c d coins)).size ≤ B := by
  let Q := paperLength rows C x b c d+coins.length
  let m := rationalRepetitionBudget (2*(r+1)) c d
  obtain ⟨hn,hr,hrows,hcirc,hprec⟩ := paperLength_components rows C x b c d
  have hv := satExtent_le_paperLength rows C x b c d
  have hdim : n+r+C.gates ≤ Q := by unfold satExtent circuitExtent at hv; dsimp [Q]; omega
  have hrowsQ : rows.length+rowIncidences rows ≤ Q := by dsimp [Q]; omega
  have hq : keySize n r ≤ 2*Q := by unfold keySize; omega
  obtain ⟨_,_,_,hm,_⟩ := budget_parameters rows C x b c d hx hc
  have hmQ : m ≤ 3*Q+2 := by dsimp [m,Q]; omega
  obtain ⟨hprog,hendmag⟩ := data_bounds rows C hdim hrowsQ
  have hrow := Final.Init.rows_sz_le rows (show n≤Q by omega) hrowsQ
  obtain ⟨s1,s2,s3,s4⟩ := hs (keySize n r)
  have sg := G_mono (k:=Ks) (c:=Cs) le_rfl le_rfl hq
  obtain ⟨c1,c2,c3⟩ := context_bounds L a Fp base den ctxIdx n r
    (encRows rows) (encProg C) x b c d coins Q (G Ks Cs (2*Q))
    (by omega) (by dsimp [Q]; omega) hrow hprog (by dsimp [Q]; omega)
    (s1.trans sg) (s2.trans sg) (s3.trans sg) (s4.trans sg)
  obtain ⟨p1,p2,p3⟩ := parse_paper_bounds L h p i rows C x b c d coins
  have hX := parseF_problemBits L h p i rows C x b c d coins
  have hC := context_den L a Fp base den ctxIdx hFp rows C x b c d coins
  obtain ⟨t1,t2,t3⟩ := initial_split L h p i a y z Fp base den ctxIdx terminalIdx topIdx
    _ _ hX _ hC
  dsimp only [encCtx] at t1 t2 t3
  have hiMag : mag (.prod .nat (.prod .nat .nat)) (keySize n r,r,m) ≤ 7*Q+5 := by
    change keySize n r+(r+m+1)+1 ≤ _
    omega
  obtain ⟨i1,i2,i3,_⟩ := hi (keySize n r,r,m)
  have ig := G_mono (k:=Ki) (c:=Ci) le_rfl le_rfl hiMag
  obtain ⟨e1,e2,e3,_⟩ := he ((n,r,encRows rows,encProg C),false)
  change (endpointF z).cost _ ≤ _ at e1
  change (endpointF z).depth _ ≤ _ at e2
  change (endpointF z).msize _ ≤ _ at e3
  have eg := G_mono (k:=Ke) (c:=Ce) le_rfl le_rfl hendmag
  have e1' := e1.trans eg
  have e2' := e2.trans eg
  have e3' := e3.trans eg
  have zi := sz_le (.prod .nat (.prod .nat .nat)) (keySize n r,r,m)
  have ze := sz_le TEArg ((n,r,encRows rows,encProg C),false)
  have zw := sz_bools (input rows C x b c d coins)
  have hw := input_length_le rows C x b c d coins
  have hQsq : Q ≤ (Q+2)^2 := by nlinarith only [Nat.zero_le Q]
  have hQsq0 : 4 ≤ (Q+2)^2 := by nlinarith only [Nat.zero_le Q]
  change (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).cost _ ≤
      initialBudget Q _ _ _ ∧ _
  unfold initialBudget
  dsimp only [Q,m,input,keySize] at *
  refine ⟨?_,?_,?_,?_⟩ <;> omega

end QecReliability.LatentMachine.InitializerFL
