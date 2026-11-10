import TensorRepairFLCanonical
import Trans.BoundsRest.Endpoint

/-! Exact physical dyadic anchors in FL. Canonical class bits are fed to the
original shared-wire circuit. Only its observed erasure mask is used by the
existing certified ambiguity-rank and power-of-two computations. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Tm FL.Lib.LinearRepairFL Trans.Wire
open Trans.Control
open Trans.Control.RankP
open SharedCircuit SharedCircuit.LatentEncoding Trans.Query

abbrev TAnchorCtx : Ty := .prod TKey (.prod .nat (.prod TRowsP TProgP))
abbrev AnchorCtx := TAnchorCtx.den

structure AnchorIndices where
  mask : ℕ
  dyadic : ℕ
  step : ℕ
  fold : ℕ
  anchors : ℕ

def maskFromBitsR (bits : List Bool) (prog : TProgP.den) : List Bool :=
  prog.2.map (fun o => (runGates bits prog.1).getD o false)

def dyadicR (ctx : AnchorCtx) (key : Key) : RawRatio :=
  (1,2 ^ ambP ctx.2.1 ctx.2.2.1
    (maskFromBitsR (canonicalBits ctx.1 key) ctx.2.2.2))

def anchorDataR (ctx : AnchorCtx) : List Key → RawTable
  | [] => []
  | key :: keys => if cornerR ctx.1 key then (key,dyadicR ctx key) :: anchorDataR ctx keys
      else anchorDataR ctx keys

variable (L : Lib) (ci : CanonicalIndices) (y : IxR) (i : AnchorIndices)

def maskFromBitsBody : Tm [.prod TBits TProgP] TBits :=
  .letE (.app (runF y) (.pair (.fst v0) (.fst (.snd v0)))) <|
    .app (Trans.Hash.mapEnvF (lookF y) y.mapLook) (.pair v0 (.snd (.snd v1)))

def maskFromBitsF := bodySig i.mask (maskFromBitsBody y)

def dyadicBody : Tm [.prod TAnchorCtx TKey] TRatio :=
  .letE (.app (bitsF L ci y.append) (.pair (.fst (.fst v0)) (.snd v0))) <|
  .letE (.app (maskFromBitsF y i) (.pair v0 (.snd (.snd (.snd (.fst v1)))))) <|
  .letE (.app (ambF y)
    (.pair (.fst (.snd (.fst v2))) (.pair (.fst (.snd (.snd (.fst v2)))) v0))) <|
  .pair (.lit (1 : ℕ))
    (.app (foldlF (dblF y) y.dblFold) (.pair (.lit (1 : ℕ)) (.app (rangeF y.range) v0)))

def dyadicF := bodySig i.dyadic (dyadicBody L ci y i)

def anchorDataStepBody : Tm [.prod TKey (.prod TAnchorCtx TTable)] (.prod TAnchorCtx TTable) :=
  .pair (.fst (.snd v0))
    (.ite (.app (cornerF L ci) (.pair (.fst (.fst (.snd v0))) (.fst v0)))
      (.lcons (.pair (.fst v0) (.app (dyadicF L ci y i) (.pair (.fst (.snd v0)) (.fst v0))))
        (.snd (.snd v0)))
      (.snd (.snd v0)))

def anchorDataStepF := bodySig i.step (anchorDataStepBody L ci y i)

def anchorDataBody : Tm [.prod TAnchorCtx (.list TKey)] TTable :=
  .snd (.app (foldrF (anchorDataStepF L ci y i) i.fold)
    (.pair (.snd v0) (.pair (.fst v0) .lnil)))

def anchorDataF := bodySig i.anchors (anchorDataBody L ci y i)

theorem maskFromBitsF_den (bits : List Bool) (prog : TProgP.den) :
    (maskFromBitsF y i).den (bits,prog) = maskFromBitsR bits prog := by
  simp only [maskFromBitsF,bodySig_den,maskFromBitsBody,tm_simp]
  rw [run_den]
  simp [Trans.Hash.mapEnvF_den,lookF,bodySig_den,lookBody,tm_simp,maskFromBitsR]

theorem dyadicF_den (ctx : AnchorCtx) (key : Key) :
    (dyadicF L ci y i).den (ctx,key) = dyadicR ctx key := by
  simp only [dyadicF,bodySig_den,dyadicBody,tm_simp,
    foldlF_den,rangeF_den,Trans.BoundsRest.dblFold_den,List.length_range,mul_one]
  rw [bitsF_den,maskFromBitsF_den,amb_den]
  rfl

theorem anchorDataStepF_den (key : Key) (ctx : AnchorCtx) (acc : RawTable) :
    (anchorDataStepF L ci y i).den (key,ctx,acc) =
      (ctx,if cornerR ctx.1 key then (key,dyadicR ctx key)::acc else acc) := by
  simp only [anchorDataStepF,bodySig_den,anchorDataStepBody,tm_simp]
  rw [cornerF_den,dyadicF_den]

theorem anchorDataFold_den (keys : List Key) (ctx : AnchorCtx) :
    foldrDen (anchorDataStepF L ci y i) keys (ctx,[]) = (ctx,anchorDataR ctx keys) := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    rw [foldrDen_cons,ih,anchorDataStepF_den,anchorDataR]

theorem anchorDataF_den (ctx : AnchorCtx) (keys : List Key) :
    (anchorDataF L ci y i).den (ctx,keys) = anchorDataR ctx keys := by
  simp only [anchorDataF,bodySig_den,anchorDataBody,tm_simp,foldrF_den]
  rw [anchorDataFold_den]

theorem maskFromBitsR_cause {n r : ℕ} (C : SharedCircuit.Program r n) (b : Causes r) :
    maskFromBitsR (List.ofFn (Binary.causeBits r b)) (encProg C) = maskL (circuitMap C b) := by
  simp only [maskFromBitsR,encProg,runGates_enc,List.map_ofFn,maskL]
  congr 1
  funext i
  simp only [Function.comp_apply,RankP.getD_ofFn]
  exact (congrFun ((Binary.causeBits n).apply_symm_apply
    (C.eval (Binary.causeBits r b))) i).symm

/-- The actual machine anchor computation is the exact bounded dyadic score
for the original physical code and the canonical latent cause tuple. -/
theorem dyadicR_correct {n : ℕ} (ds : List ℕ) (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (j : TensorBernstein.Grid ds) :
    dyadicR (ds,n,encRows rows,encProg C) (TensorMachine.indexList ds j) =
      LinearRepairFL.toR (RationalOutput.Ratio.dyadic rows
        (circuitMap C (TensorLatent.flattenCauses ds (TensorLatent.canonicalCauses ds j)))) := by
  rw [dyadicR,canonicalBits_flattenCauses,maskFromBitsR_cause,ambP_eq]
  rfl

structure AnchorIndices.OK (P : FL.Program) : Prop where
  mask : P[i.mask]? = some (maskFromBitsBody y).compile
  dyadic : P[i.dyadic]? = some (dyadicBody L ci y i).compile
  step : P[i.step]? = some (anchorDataStepBody L ci y i).compile
  fold : P[i.fold]? = some (foldrBody (anchorDataStepF L ci y i) i.fold).compile
  anchors : P[i.anchors]? = some (anchorDataBody L ci y i).compile

variable {L ci y i} {P : FL.Program}

/-- Reuse the existing installed endpoint library; none of these callees is an
assumed oracle. The same checked bodies evaluate arbitrary canonical masks. -/
theorem rankCallees_valid (h : LibR y P) :
    (∀ a, (runF y).ValidAt P a) ∧
    (∀ a, (Trans.Hash.mapEnvF (lookF y) y.mapLook).ValidAt P a) ∧
    (∀ a, (ambF y).ValidAt P a) ∧
    (∀ a, (foldlF (dblF y) y.dblFold).ValidAt P a) := by
  have hx := xorL_valid h.xorL
  have hg : ∀ a, (gateValF y).ValidAt P a := fun a => bodySig_valid h.gateVal (by
    simp [tm_simp, gateValBody, h.getD])
  have hrs : ∀ a, (runStepF y).ValidAt P a := fun a => bodySig_valid h.runStep (by
    simp [tm_simp, runStepBody, h.append, hg])
  have hrun := Trans.Hash.foldl_validAll hrs h.run
  have hl : ∀ a, (lookF y).ValidAt P a := fun a => bodySig_valid h.look (by
    simp [tm_simp, lookBody, h.getD])
  have hml := Trans.Hash.mapEnv_validAll hl h.mapLook
  have hps : ∀ a, (parStepF y).ValidAt P a := fun a => bodySig_valid h.parStep (by
    simp [tm_simp, parStepBody, h.eq])
  have hpf := Trans.Hash.foldl_validAll hps h.parFold
  have hp : ∀ a, (parF y).ValidAt P a := fun a => bodySig_valid h.par (by
    simp [tm_simp, parBody, hpf])
  have hb : ∀ a, (bitF y).ValidAt P a := fun a => bodySig_valid h.bit (by
    simp [tm_simp, bitBody, h.getD, hp])
  have hmb := Trans.Hash.mapEnv_validAll hb h.mapBit
  have hd : ∀ a, (denseF y).ValidAt P a := fun a => bodySig_valid h.dense (by
    simp [tm_simp, denseBody, h.range, h.append, hmb])
  have hmd := Trans.Hash.mapEnv_validAll hd h.mapDense
  have hh : ∀ a, (headTF y).ValidAt P a := fun a => bodySig_valid h.headT (by
    simp only [tm_simp, headTBody]; split <;> trivial)
  have ht : ∀ a, (tailBF y).ValidAt P a := fun a => bodySig_valid h.tailB (by
    simp only [tm_simp, tailBBody]; split <;> trivial)
  have hc : ∀ a, (clearF y).ValidAt P a := fun a => bodySig_valid h.clear (by
    simp [tm_simp, clearBody, hh, ht, hx])
  have hmc := Trans.Hash.mapEnv_validAll hc h.mapClear
  have hfh : ∀ xs, (filterF (headTF y) y.filterHead).ValidAt P xs :=
    fun xs => filter_valid h.filterHead xs (fun _ _ => hh _)
  have hmt : ∀ xs, (mapF (tailBF y) y.mapTail).ValidAt P xs :=
    fun xs => map_valid h.mapTail xs (fun _ _ => ht _)
  have hstep : ∀ a, (rankStepF y).ValidAt P a := fun a => bodySig_valid h.rankStep (by
    simp only [tm_simp, rankStepBody]
    split <;> simp_all [hfh, hmt, hmc, h.succ])
  have hrf := Trans.Hash.foldl_validAll hstep h.rankFold
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
  exact ⟨hrun,hml,ha,Trans.Hash.foldl_validAll hdbl h.dblFold⟩

theorem maskFromBits_valid (hr : LibR y P) (hi : AnchorIndices.OK L ci y i P) :
    ∀ x, (maskFromBitsF y i).ValidAt P x := by
  obtain ⟨hrun,hlook,_,_⟩ := rankCallees_valid hr
  intro x
  apply bodySig_valid hi.mask
  simp [maskFromBitsBody,tm_simp,hrun,hlook]

theorem dyadic_valid (hL : L.OK P) (hr : LibR y P)
    (hc : CanonicalIndices.OK L ci y.append P) (hi : AnchorIndices.OK L ci y i P) :
    ∀ x, (dyadicF L ci y i).ValidAt P x := by
  obtain ⟨_,_,hamb,hdbl⟩ := rankCallees_valid hr
  intro x
  apply bodySig_valid hi.dyadic
  simp [dyadicBody,tm_simp,bits_valid hL hc hr.append,maskFromBits_valid hr hi,hamb,hdbl,hr.range]

theorem anchorDataStep_valid (hL : L.OK P) (hr : LibR y P)
    (hc : CanonicalIndices.OK L ci y.append P) (hi : AnchorIndices.OK L ci y i P) :
    ∀ x, (anchorDataStepF L ci y i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.step
  simp [anchorDataStepBody,tm_simp,corner_valid hL hc,dyadic_valid hL hr hc hi]

theorem anchorData_valid (hL : L.OK P) (hr : LibR y P)
    (hc : CanonicalIndices.OK L ci y.append P) (hi : AnchorIndices.OK L ci y i P) :
    ∀ x, (anchorDataF L ci y i).ValidAt P x := by
  have hf := Trans.Hash.foldr_validAll (anchorDataStep_valid hL hr hc hi) hi.fold
  intro x
  apply bodySig_valid hi.anchors
  simp [anchorDataBody,tm_simp,hf]

end QecReliability.TensorMachine.RepairFL
