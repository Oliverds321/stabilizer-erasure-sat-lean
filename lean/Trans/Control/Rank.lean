import Trans.Control.RankPlain
import Trans.Control.Base
import Trans.Hash.FLAffine

/-!
# Trans.Control.Rank: the exact endpoints in FL

`endpointF : ((n, r, rows, P), side) ↦ (1, 2^ambiguity)` on the encoded rows (`encRows`) and
circuit (`encProg`), with `endpointF_correct`:
`(endpointF y).den ((n, r, encRows rows, encProg C), side) = toR (concreteEndpoint rows C side).value`.

Only one new recursive function (`xorLF`, explicit bounds); everything else is a `bodySig`
body over the library (`foldlF`, `mapF`, `mapEnvF`, `filterF`, `getDF`, `replicateF`, …):
the circuit run and the GF(2) elimination are `foldl`s (the elimination over `range (2n)` with
state `(rows, rank)`), parities are `foldl`s with the coordinate in the state, `2^a` is a
`foldl` of doublings.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.Control
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.Trans.Hash (mapEnvF mapEnvBody mapEnv_validAll mapEnvF_den foldl_validAll)
open QecReliability.Trans.Control.RankP

abbrev TGateP : Ty := .prod .bool (.prod .bool (.prod .nat .nat))
abbrev TProgP : Ty := .prod (.list TGateP) (.list .nat)
abbrev TCoord : Ty := .prod .bool .nat
abbrev TRowsP : Ty := .list (.list TCoord)
abbrev TBits : Ty := .list .bool

/-! ## `xorL` (the only new recursion) -/

variable {P : Program}

@[simps] def xorLF (i : ℕ) : FnSig (.prod (.list .bool) (.list .bool)) (.list .bool) where
  idx := i
  den p := xorL p.1 p.2
  cost p := 40 * (p.1.length + 1)
  depth p := p.1.length + 1
  msize p := 2 * (Ty.enc (.prod (.list .bool) (.list .bool)) p).size

def xorLBody (i : ℕ) : Tm [.prod (.list .bool) (.list .bool)] (.list .bool) :=
  .lcase (.fst v0) .lnil
    (.lcase (.snd v2) .lnil (.lcons (.xor v2 v0) (.app (xorLF i) (.pair v3 v1))))

theorem xorL_sz (a b : List Bool) :
    (Ty.enc (.list .bool) (xorL a b)).size ≤ 2 * (Ty.enc (.list .bool) a).size := by
  induction a generalizing b with
  | nil => simp [xorL]
  | cons x xs ih =>
    cases b with
    | nil => have := Ty.sz_pos (Ty.list .bool) xs; simp only [xorL, Ty.enc_list_cons_bool, Ty.enc_list_nil_bool, Val.size_cons, Val.size_nil]; omega
    | cons y ys =>
      have := ih ys
      simp only [xorL, Ty.enc_list_cons_bool, Val.size_cons]
      have h1 := Enc.bool_size (Bool.xor x y); have h2 : 1 ≤ (Enc.bool x).size := Val.size_pos _
      cases x <;> cases y <;> simp [Enc.bool] at * <;> omega

theorem xorL_valid {i : ℕ} (hP : P[i]? = some (xorLBody i).compile) : ∀ p, (xorLF i).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.1.length) ?_
  rintro ⟨(_ | ⟨a, as⟩), (_ | ⟨b, bs⟩)⟩ ih
  · constructor <;> tm_auto [xorLBody, xorL]
  · constructor <;> tm_auto [xorLBody, xorL]
  · constructor <;> tm_auto [xorLBody, xorL]
  · have hih := ih (as, bs) (by simp)
    have hs := xorL_sz as bs
    have p1 := Ty.sz_pos (Ty.list .bool) as; have p2 := Ty.sz_pos (Ty.list .bool) bs
    constructor
    · tm_auto [xorLBody, hih]
    · simp [tm_simp, xorLBody, xorL, hih]; cases a <;> cases b <;> rfl
    · tm_auto [xorLBody, hih]
    · tm_auto [xorLBody, hih]
    · tm_lean [xorLBody, hih, xorLF_msize, xorLF_den, Ty.enc_list_cons_bool]

/-! ## Indices -/

structure IxR where
  succ : ℕ
  add : ℕ
  sub : ℕ
  eq : ℕ
  range : ℕ
  length : ℕ
  getD : ℕ
  replicate : ℕ
  append : ℕ
  xorL : ℕ
  gateVal : ℕ
  runStep : ℕ
  run : ℕ
  look : ℕ
  mapLook : ℕ
  maskOf : ℕ
  parStep : ℕ
  parFold : ℕ
  par : ℕ
  bit : ℕ
  mapBit : ℕ
  dense : ℕ
  mapDense : ℕ
  headT : ℕ
  tailB : ℕ
  filterHead : ℕ
  mapTail : ℕ
  clear : ℕ
  mapClear : ℕ
  rankStep : ℕ
  rankFold : ℕ
  rank : ℕ
  idB : ℕ
  filterId : ℕ
  notB : ℕ
  mapNot : ℕ
  dbl : ℕ
  dblFold : ℕ
  amb : ℕ
  endpoint : ℕ

variable (y : IxR)

/-! ## Circuit run on a constant input -/

def gateValBody : Tm [.prod TBits TGateP] .bool :=
  .letE (.app (getDF .bool y.getD) (.pair (.fst v0) (.pair (p2 (.snd v0)) .ff))) <|
  .letE (.app (getDF .bool y.getD) (.pair (.fst v1) (.pair (q3 (.snd v1)) .ff))) <|
  .ite (p0 (.snd v2))
    (.ite (p1 (.snd v2)) (.isPos (p2 (.snd v2))) (.not v1))
    (.ite (p1 (.snd v2)) (.xor v1 v0) (.and v1 v0))
def gateValF : FnSig (.prod TBits TGateP) .bool := bodySig y.gateVal (gateValBody y)

def runStepBody : Tm [.prod TBits TGateP] TBits :=
  .app (appendF .bool y.append) (.pair (.fst v0) (.lcons (.app (gateValF y) v0) .lnil))
def runStepF : FnSig (.prod TBits TGateP) TBits := bodySig y.runStep (runStepBody y)
def runF : FnSig (.prod TBits (.list TGateP)) TBits := foldlF (runStepF y) y.run

def lookBody : Tm [.prod TBits .nat] .bool :=
  .app (getDF .bool y.getD) (.pair (.fst v0) (.pair (.snd v0) .ff))
def lookF : FnSig (.prod TBits .nat) .bool := bodySig y.look (lookBody y)

/-- `(r, side, P) ↦ maskOf r side P`. -/
def maskOfBody : Tm [.prod .nat (.prod .bool TProgP)] TBits :=
  .letE (.app (runF y) (.pair (.app (replicateF .bool y.replicate) (.pair (.fst v0) (p1 v0)))
    (.fst (q2 v0)))) <|
    .app (mapEnvF (lookF y) y.mapLook) (.pair v0 (.snd (q2 v1)))
def maskOfF : FnSig (.prod .nat (.prod .bool TProgP)) TBits := bodySig y.maskOf (maskOfBody y)

/-! ## Parities and dense rows -/

/-- `(((z, i), acc), c) ↦ ((z, i), (c = (z, i)) xor acc)`. -/
def parStepBody : Tm [.prod (.prod TCoord .bool) TCoord] (.prod TCoord .bool) :=
  .pair (.fst (.fst v0))
    (.xor (.and (.ite (.fst (.snd v0)) (.fst (.fst (.fst v0))) (.not (.fst (.fst (.fst v0)))))
        (.app (eqF y.eq) (.pair (.snd (.snd v0)) (.snd (.fst (.fst v0))))))
      (.snd (.fst v0)))
def parStepF : FnSig (.prod (.prod TCoord .bool) TCoord) (.prod TCoord .bool) :=
  bodySig y.parStep (parStepBody y)

/-- `((z, i), row) ↦ par z i row`. -/
def parBody : Tm [.prod TCoord (.list TCoord)] .bool :=
  .snd (.app (foldlF (parStepF y) y.parFold) (.pair (.pair (.fst v0) .ff) (.snd v0)))
def parF : FnSig (.prod TCoord (.list TCoord)) .bool := bodySig y.par (parBody y)

/-- `((mask, (row, z)), i) ↦ mask[i] && par z i row`. -/
def bitBody : Tm [.prod (.prod TBits (.prod (.list TCoord) .bool)) .nat] .bool :=
  .and (.app (getDF .bool y.getD) (.pair (.fst (.fst v0)) (.pair (.snd v0) .ff)))
    (.app (parF y) (.pair (.pair (.snd (.snd (.fst v0))) (.snd v0)) (.fst (.snd (.fst v0)))))
def bitF : FnSig (.prod (.prod TBits (.prod (.list TCoord) .bool)) .nat) .bool :=
  bodySig y.bit (bitBody y)

/-- `((n, mask), row) ↦ denseRow n mask row`. -/
def denseBody : Tm [.prod (.prod .nat TBits) (.list TCoord)] TBits :=
  .letE (.app (rangeF y.range) (.fst (.fst v0))) <|
    .app (appendF .bool y.append)
      (.pair (.app (mapEnvF (bitF y) y.mapBit) (.pair (.pair (.snd (.fst v1)) (.pair (.snd v1) .ff)) v0))
        (.app (mapEnvF (bitF y) y.mapBit) (.pair (.pair (.snd (.fst v1)) (.pair (.snd v1) .tt)) v0)))
def denseF : FnSig (.prod (.prod .nat TBits) (.list TCoord)) TBits := bodySig y.dense (denseBody y)

/-! ## Elimination -/

def headTBody : Tm [TBits] .bool := .lcase v0 .ff v0
def headTF : FnSig TBits .bool := bodySig y.headT headTBody
def tailBBody : Tm [TBits] TBits := .lcase v0 .lnil v1
def tailBF : FnSig TBits TBits := bodySig y.tailB tailBBody

/-- `(p, x) ↦ clearL p x`. -/
def clearBody : Tm [.prod TBits TBits] TBits :=
  .ite (.app (headTF y) (.snd v0))
    (.app (xorLF y.xorL) (.pair (.app (tailBF y) (.snd v0)) (.app (tailBF y) (.fst v0))))
    (.app (tailBF y) (.snd v0))
def clearF : FnSig (.prod TBits TBits) TBits := bodySig y.clear (clearBody y)

/-- One elimination column: `((rows, c), _) ↦ (rows', c')`. -/
def rankStepBody : Tm [.prod (.prod (.list TBits) .nat) .nat] (.prod (.list TBits) .nat) :=
  .letE (.fst (.fst v0)) <|
  .lcase (.app (filterF (headTF y) y.filterHead) v0)
    (.pair (.app (mapF (tailBF y) y.mapTail) v0) (.snd (.fst v1)))
    (.pair (.app (mapEnvF (clearF y) y.mapClear) (.pair v0 v2)) (.app (succF y.succ) (.snd (.fst v3))))
def rankStepF : FnSig (.prod (.prod (.list TBits) .nat) .nat) (.prod (.list TBits) .nat) :=
  bodySig y.rankStep (rankStepBody y)

/-- `(k, rows) ↦ rankL k rows`. -/
def rankBody : Tm [.prod .nat (.list TBits)] .nat :=
  .snd (.app (foldlF (rankStepF y) y.rankFold)
    (.pair (.pair (.snd v0) .zero) (.app (rangeF y.range) (.fst v0))))
def rankF : FnSig (.prod .nat (.list TBits)) .nat := bodySig y.rank (rankBody y)

/-! ## Ambiguity and the endpoint -/

def idBBody : Tm [.bool] .bool := v0
def idBF : FnSig .bool .bool := bodySig y.idB idBBody
def notBBody : Tm [.bool] .bool := .not v0
def notBF : FnSig .bool .bool := bodySig y.notB notBBody

/-- `rr mask` inside `ambBody` (environment `[n+n, (n, rows, mask)]`). -/
abbrev rrT {Γ : List Ty} (nn : Tm Γ .nat) (n : Tm Γ .nat) (rows : Tm Γ TRowsP) (mask : Tm Γ TBits) :
    Tm Γ .nat :=
  .app (rankF y) (.pair nn (.app (mapEnvF (denseF y) y.mapDense) (.pair (.pair n mask) rows)))

/-- `(n, rows, mask) ↦ ambP n rows mask`. -/
def ambBody : Tm [.prod .nat (.prod TRowsP TBits)] .nat :=
  .letE (.app (addF y.add) (.pair (.fst v0) (.fst v0))) <|
  .app (subF y.sub) (.pair
    (.app (subF y.sub) (.pair
      (.bit .ff (.app (lengthF .bool y.length) (.app (filterF (idBF y) y.filterId) (.snd (.snd v1)))))
      (rrT y v0 (.fst v1) (.fst (.snd v1)) (.snd (.snd v1)))))
    (.app (subF y.sub) (.pair
      (rrT y v0 (.fst v1) (.fst (.snd v1))
        (.app (replicateF .bool y.replicate) (.pair (.fst v1) .tt)))
      (rrT y v0 (.fst v1) (.fst (.snd v1)) (.app (mapF (notBF y) y.mapNot) (.snd (.snd v1)))))))
def ambF : FnSig (.prod .nat (.prod TRowsP TBits)) .nat := bodySig y.amb (ambBody y)

def dblBody : Tm [.prod .nat .nat] .nat := .bit .ff (.fst v0)
def dblF : FnSig (.prod .nat .nat) .nat := bodySig y.dbl dblBody

/-- `((n, r, rows, P), side) ↦ (1, 2 ^ ambP n rows (maskOf r side P))`. -/
def endpointBody : Tm [.prod (.prod .nat (.prod .nat (.prod TRowsP TProgP))) .bool] TR :=
  .letE (.app (ambF y) (.pair (p0 (.fst v0)) (.pair (p2 (.fst v0))
    (.app (maskOfF y) (.pair (p1 (.fst v0)) (.pair (.snd v0) (q3 (.fst v0)))))))) <|
  .pair (.lit (1 : ℕ))
    (.app (foldlF (dblF y) y.dblFold) (.pair (.lit (1 : ℕ)) (.app (rangeF y.range) v0)))
def endpointF : FnSig (.prod (.prod .nat (.prod .nat (.prod TRowsP TProgP))) .bool) TR :=
  bodySig y.endpoint (endpointBody y)

/-! ## Meaning -/

theorem foldl_const_iter {α β : Type} (g : α → α) (l : List β) (z : α) :
    l.foldl (fun s _ => g s) z = g^[l.length] z := by
  induction l generalizing z with
  | nil => rfl
  | cons x xs ih => simp [ih, Function.iterate_succ_apply]

theorem gateVal_den (vals : List Bool) (g : Bool × Bool × ℕ × ℕ) :
    (gateValF y).den (vals, g) = gateVal vals g := by
  obtain ⟨u, s, a, b⟩ := g
  cases u <;> cases s <;> simp [gateValF, bodySig_den, gateValBody, tm_simp, gateVal]
  all_goals (generalize vals[a]?.getD false = u; generalize vals[b]?.getD false = v
             cases u <;> cases v <;> rfl)

theorem run_den (vals : List Bool) (gs : List (Bool × Bool × ℕ × ℕ)) :
    (runF y).den (vals, gs) = runGates vals gs := by
  induction gs generalizing vals with
  | nil => rfl
  | cons g gs ih =>
    simp only [runF, foldlF_den] at ih ⊢
    rw [foldlDen_cons]
    rw [show (runStepF y).den (vals, g) = vals ++ [gateVal vals g] by
      simp [runStepF, bodySig_den, runStepBody, tm_simp]; exact gateVal_den y vals g]
    exact ih _

theorem maskOf_den (r : ℕ) (b : Bool) (P : List (Bool × Bool × ℕ × ℕ) × List ℕ) :
    (maskOfF y).den (r, b, P) = maskOf r b P := by
  simp only [maskOfF, bodySig_den, maskOfBody, tm_simp]
  rw [run_den]
  simp [mapEnvF_den, lookF, bodySig_den, lookBody, tm_simp, maskOf]

theorem parFold_den (z : Bool) (i : ℕ) (row : List (Bool × ℕ)) (acc : Bool) :
    foldlDen (parStepF y) ((z, i), acc) row = ((z, i), Bool.xor acc (par z i row)) := by
  induction row generalizing acc with
  | nil => simp [par, foldlDen]
  | cons c cs ih =>
    rw [foldlDen_cons]
    have : (parStepF y).den (((z, i), acc), c) = ((z, i), Bool.xor (decide (c = (z, i))) acc) := by
      obtain ⟨c1, c2⟩ := c
      cases c1 <;> cases z <;> simp [parStepF, bodySig_den, parStepBody, tm_simp] <;>
        (try cases acc) <;> simp
    rw [this, ih]
    simp only [par, Prod.mk.injEq, true_and]
    cases decide (c = (z, i)) <;> cases acc <;> simp

theorem par_den (z : Bool) (i : ℕ) (row : List (Bool × ℕ)) :
    (parF y).den ((z, i), row) = par z i row := by
  simp only [parF, bodySig_den, parBody, tm_simp, foldlF_den]
  rw [parFold_den]; simp

theorem dense_den (n : ℕ) (mask : List Bool) (row : List (Bool × ℕ)) :
    (denseF y).den ((n, mask), row) = denseRow n mask row := by
  simp [denseF, bodySig_den, denseBody, tm_simp, mapEnvF_den, bitF, bitBody, denseRow]
  congr 1 <;> (apply List.map_congr_left; intro i _; rw [par_den])

theorem headT_den (x : List Bool) : (headTF y).den x = x.headD false := by cases x <;> rfl
theorem tailB_den (x : List Bool) : (tailBF y).den x = x.tail := by cases x <;> rfl

theorem clear_den (p x : List Bool) : (clearF y).den (p, x) = clearL p x := by
  show (if (headTF y).den x = true then xorL ((tailBF y).den x) ((tailBF y).den p)
    else (tailBF y).den x) = _
  rw [headT_den, tailB_den, tailB_den]; rfl

theorem find?_eq_head?_filter {α : Type} (p : α → Bool) (l : List α) :
    l.find? p = (l.filter p).head? := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp only [List.find?_cons, List.filter_cons, h, ih] <;> rfl

/-- One elimination column on plain data. -/
def colStep (s : List (List Bool) × ℕ) : List (List Bool) × ℕ :=
  match s.1.find? (fun x => x.headD false) with
  | none => (s.1.map List.tail, s.2)
  | some p => (s.1.map (clearL p), s.2 + 1)

theorem rankStep_den (s : List (List Bool) × ℕ) (k : ℕ) : (rankStepF y).den (s, k) = colStep s := by
  obtain ⟨rows, c⟩ := s
  have hh : (headTF y).den = fun x => x.headD false := funext (headT_den y)
  have ht : (tailBF y).den = List.tail := funext (tailB_den y)
  have hc : (fun x => (clearF y).den x) = fun q => clearL q.1 q.2 := funext fun q => clear_den y q.1 q.2
  simp only [rankStepF, bodySig_den, rankStepBody, tm_simp, filterF_den, hh, mapF_den, ht,
    mapEnvF_den, succF_den]
  unfold colStep
  rw [find?_eq_head?_filter]
  generalize List.filter (fun x => x.headD false) rows = fl
  cases fl with
  | nil => rfl
  | cons p ps => simp only [List.head?_cons]; congr 1; apply List.map_congr_left; intro x _; exact clear_den y p x

theorem colStep_iter : ∀ (k : ℕ) (rows : List (List Bool)) (c : ℕ),
    (colStep^[k] (rows, c)).2 = c + rankL k rows
  | 0, _, _ => rfl
  | k + 1, rows, c => by
    rw [Function.iterate_succ_apply]
    rcases h : rows.find? (fun x => x.headD false) with _ | p
    · simp only [colStep, rankL, h]; exact colStep_iter k _ _
    · simp only [colStep, rankL, h]; rw [colStep_iter k]; omega

theorem rank_den (k : ℕ) (rows : List (List Bool)) : (rankF y).den (k, rows) = rankL k rows := by
  simp only [rankF, bodySig_den, rankBody, tm_simp, foldlF_den, foldlDen, rangeF_den]
  have : (fun acc (x : ℕ) => (rankStepF y).den (acc, x)) = fun acc _ => colStep acc := by
    funext acc x; exact rankStep_den y acc x
  rw [this, foldl_const_iter, List.length_range, colStep_iter]; simp

theorem cardP_filter (mask : List Bool) : cardP mask = (mask.filter id).length := by
  induction mask with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all [cardP] <;> omega

theorem amb_den (n : ℕ) (rows : List (List (Bool × ℕ))) (mask : List Bool) :
    (ambF y).den (n, rows, mask) = ambP n rows mask := by
  have hid : (idBF y).den = id := by funext b; simp [idBF, bodySig_den, idBBody, tm_simp]
  have hnot : (notBF y).den = Bool.not := by funext b; simp [notBF, bodySig_den, notBBody, tm_simp]
  have hd : (denseF y).den = fun p => denseRow p.1.1 p.1.2 p.2 := by
    funext p; obtain ⟨⟨a, b⟩, c⟩ := p; exact dense_den y a b c
  simp only [ambF, bodySig_den, ambBody, tm_simp, subF_den, addF_den, lengthF_den, filterF_den,
    hid, mapEnvF_den, hd, replicateF_den, mapF_den, hnot, bitNat_false]
  rw [rank_den, rank_den, rank_den]
  simp [ambP, rrP, cardP_filter]

theorem dbl_iter (a : ℕ) : (fun x => 2 * x)^[a] 1 = 2 ^ a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring

theorem endpoint_den (n r : ℕ) (rows : List (List (Bool × ℕ))) (P : List (Bool × Bool × ℕ × ℕ) × List ℕ)
    (side : Bool) : (endpointF y).den ((n, r, rows, P), side) = endpointP n r rows P side := by
  simp only [endpointF, bodySig_den, endpointBody, tm_simp, foldlF_den, foldlDen, rangeF_den]
  rw [maskOf_den, amb_den]
  have : (fun acc (x : ℕ) => (dblF y).den (acc, x)) = fun acc _ => 2 * acc := by
    funext acc x; simp [dblF, bodySig_den, dblBody, tm_simp]
  rw [this, foldl_const_iter, List.length_range, dbl_iter]
  rfl

/-- **The FL endpoint is the controller's exact endpoint.** -/
theorem endpointF_correct {n r : ℕ} (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : SharedCircuit.Program r n) (side : Bool) :
    (endpointF y).den ((n, r, Query.encRows rows, Query.encProg C), side) =
      toR (Final.concreteEndpoint rows C side).value := by
  rw [endpoint_den, endpointP_eq]; rfl

/-! ## Validity -/

/-- Library validity and installation of every body used by `endpointF`. -/
structure LibR (P : Program) : Prop where
  succ : ∀ n, (succF y.succ).ValidAt P n
  add : ∀ p, (addF y.add).ValidAt P p
  sub : ∀ p, (subF y.sub).ValidAt P p
  eq : ∀ p, (eqF y.eq).ValidAt P p
  range : ∀ n, (rangeF y.range).ValidAt P n
  length : ∀ xs, (lengthF .bool y.length).ValidAt P xs
  getD : ∀ p, (getDF .bool y.getD).ValidAt P p
  replicate : ∀ p, (replicateF .bool y.replicate).ValidAt P p
  append : ∀ p, (appendF .bool y.append).ValidAt P p
  xorL : P[y.xorL]? = some (xorLBody y.xorL).compile
  gateVal : P[y.gateVal]? = some (gateValBody y).compile
  runStep : P[y.runStep]? = some (runStepBody y).compile
  run : P[y.run]? = some (foldlBody (runStepF y) y.run).compile
  look : P[y.look]? = some (lookBody y).compile
  mapLook : P[y.mapLook]? = some (mapEnvBody (lookF y) y.mapLook).compile
  maskOf : P[y.maskOf]? = some (maskOfBody y).compile
  parStep : P[y.parStep]? = some (parStepBody y).compile
  parFold : P[y.parFold]? = some (foldlBody (parStepF y) y.parFold).compile
  par : P[y.par]? = some (parBody y).compile
  bit : P[y.bit]? = some (bitBody y).compile
  mapBit : P[y.mapBit]? = some (mapEnvBody (bitF y) y.mapBit).compile
  dense : P[y.dense]? = some (denseBody y).compile
  mapDense : P[y.mapDense]? = some (mapEnvBody (denseF y) y.mapDense).compile
  headT : P[y.headT]? = some headTBody.compile
  tailB : P[y.tailB]? = some tailBBody.compile
  filterHead : P[y.filterHead]? = some (filterBody (headTF y) y.filterHead).compile
  mapTail : P[y.mapTail]? = some (mapBody (tailBF y) y.mapTail).compile
  clear : P[y.clear]? = some (clearBody y).compile
  mapClear : P[y.mapClear]? = some (mapEnvBody (clearF y) y.mapClear).compile
  rankStep : P[y.rankStep]? = some (rankStepBody y).compile
  rankFold : P[y.rankFold]? = some (foldlBody (rankStepF y) y.rankFold).compile
  rank : P[y.rank]? = some (rankBody y).compile
  idB : P[y.idB]? = some idBBody.compile
  filterId : P[y.filterId]? = some (filterBody (idBF y) y.filterId).compile
  notB : P[y.notB]? = some notBBody.compile
  mapNot : P[y.mapNot]? = some (mapBody (notBF y) y.mapNot).compile
  dbl : P[y.dbl]? = some dblBody.compile
  dblFold : P[y.dblFold]? = some (foldlBody (dblF y) y.dblFold).compile
  amb : P[y.amb]? = some (ambBody y).compile
  endpoint : P[y.endpoint]? = some (endpointBody y).compile

section Valid
variable {y} (h : LibR y P)
include h

theorem endpoint_valid : ∀ a, (endpointF y).ValidAt P a := by
  have hx := xorL_valid h.xorL
  have hg : ∀ a, (gateValF y).ValidAt P a := fun a => bodySig_valid h.gateVal (by
    simp [tm_simp, gateValBody, h.getD])
  have hrs : ∀ a, (runStepF y).ValidAt P a := fun a => bodySig_valid h.runStep (by
    simp [tm_simp, runStepBody, h.append, hg])
  have hrun := foldl_validAll hrs h.run
  have hl : ∀ a, (lookF y).ValidAt P a := fun a => bodySig_valid h.look (by
    simp [tm_simp, lookBody, h.getD])
  have hml := mapEnv_validAll hl h.mapLook
  have hm : ∀ a, (maskOfF y).ValidAt P a := fun a => bodySig_valid h.maskOf (by
    simp [tm_simp, maskOfBody, h.replicate]; exact ⟨hrun _, hml _⟩)
  have hps : ∀ a, (parStepF y).ValidAt P a := fun a => bodySig_valid h.parStep (by
    simp [tm_simp, parStepBody, h.eq])
  have hpf := foldl_validAll hps h.parFold
  have hp : ∀ a, (parF y).ValidAt P a := fun a => bodySig_valid h.par (by
    simp [tm_simp, parBody, hpf])
  have hb : ∀ a, (bitF y).ValidAt P a := fun a => bodySig_valid h.bit (by
    simp [tm_simp, bitBody, h.getD, hp])
  have hmb := mapEnv_validAll hb h.mapBit
  have hd : ∀ a, (denseF y).ValidAt P a := fun a => bodySig_valid h.dense (by
    simp [tm_simp, denseBody, h.range, h.append, hmb])
  have hmd := mapEnv_validAll hd h.mapDense
  have hh : ∀ a, (headTF y).ValidAt P a := fun a => bodySig_valid h.headT (by
    simp only [tm_simp, headTBody]; split <;> trivial)
  have ht : ∀ a, (tailBF y).ValidAt P a := fun a => bodySig_valid h.tailB (by
    simp only [tm_simp, tailBBody]; split <;> trivial)
  have hc : ∀ a, (clearF y).ValidAt P a := fun a => bodySig_valid h.clear (by
    simp [tm_simp, clearBody, hh, ht, hx])
  have hmc := mapEnv_validAll hc h.mapClear
  have hfh : ∀ xs, (filterF (headTF y) y.filterHead).ValidAt P xs :=
    fun xs => filter_valid h.filterHead xs (fun _ _ => hh _)
  have hmt : ∀ xs, (mapF (tailBF y) y.mapTail).ValidAt P xs :=
    fun xs => map_valid h.mapTail xs (fun _ _ => ht _)
  have hstep : ∀ a, (rankStepF y).ValidAt P a := fun a => bodySig_valid h.rankStep (by
    simp only [tm_simp, rankStepBody]
    split <;> simp_all [hfh, hmt, hmc, h.succ])
  have hrf := foldl_validAll hstep h.rankFold
  have hr : ∀ a, (rankF y).ValidAt P a := fun a => bodySig_valid h.rank (by
    simp [tm_simp, rankBody, hrf, h.range])
  have hid : ∀ a, (idBF y).ValidAt P a := fun a => bodySig_valid h.idB (by simp [tm_simp, idBBody])
  have hnot : ∀ a, (notBF y).ValidAt P a := fun a => bodySig_valid h.notB (by
    simp [tm_simp, notBBody])
  have hfi : ∀ xs, (filterF (idBF y) y.filterId).ValidAt P xs :=
    fun xs => filter_valid h.filterId xs (fun _ _ => hid _)
  have hmn : ∀ xs, (mapF (notBF y) y.mapNot).ValidAt P xs :=
    fun xs => map_valid h.mapNot xs (fun _ _ => hnot _)
  have ha : ∀ a, (ambF y).ValidAt P a := fun a => bodySig_valid h.amb (by
    simp [tm_simp, ambBody, h.add, h.sub, h.length, h.replicate, hfi, hmn, hr, hmd])
  have hdbl : ∀ a, (dblF y).ValidAt P a := fun a => bodySig_valid h.dbl (by simp [tm_simp, dblBody])
  have hdf := foldl_validAll hdbl h.dblFold
  intro a
  exact bodySig_valid h.endpoint (by simp [tm_simp, endpointBody, ha, hm, hdf, h.range])

end Valid

end QecReliability.Trans.Control
