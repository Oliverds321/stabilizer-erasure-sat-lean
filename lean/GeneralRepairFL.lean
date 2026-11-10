import TensorRepairFLFullBounds
import TensorRepairFLSemantics
import TensorGeneralSemantics

/-! The general-circuit controller callback: pair cached good/bad counts with the
runtime grid keys, compute the exact physical corner anchors (both exactly as the
full repair callback does), substitute the anchors at the corners, and return the
substituted ratios. No shape repair. Typed FL bodies, denotation, validity,
execution and a polynomial resource envelope. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.GeneralRepairFL
open FL FL.Lib FL.Tm FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig bodySig_den bodySig_valid IxR LibR bodySig_cost bodySig_depth
  bodySig_msize)
open RepairFL

structure GeneralIndices where
  sndStep : ℕ
  sndFold : ℕ
  general : ℕ

variable (L : Lib) (ri : Indices) (ci : CanonicalIndices)
  (y : IxR) (ai : AnchorIndices) (wi : WrapperIndices) (gi : GeneralIndices)

def sndStepBody : Tm [.prod TEntry TOutput] TOutput :=
  .lcons (.snd (.fst v0)) (.snd v0)

def sndStepF := bodySig gi.sndStep sndStepBody

abbrev sndF := foldrF (sndStepF gi) gi.sndFold

def generalBody : Tm [TFullArg] TOutput :=
  .letE (.app (countDataF L wi)
    (.pair (.fst (.snd (.fst v0))) (.snd v0))) <|
  .letE (.app (anchorDataF L ci y ai)
    (.pair
      (.pair (.fst (.fst v1))
        (.pair (.fst (.snd (.snd (.fst v1))))
          (.pair (.fst (.snd (.snd (.snd (.fst v1)))))
            (.fst (.snd (.snd (.snd (.snd (.fst v1)))))))))
      (.fst (.snd (.fst v1))))) <|
    .app (sndF gi) (.pair (.app (substF L ri) (.pair v1 v0)) .lnil)

def generalF := bodySig gi.general (generalBody L ri ci y ai wi gi)

/-- Plain semantics of the general callback. -/
def generalR (x : TTensorX.den) (gs bs : List RawRatio) : List RawRatio :=
  (substituteR (countDataR x.2.1 gs bs) (anchorDataR (externalAnchorCtx x) x.2.1)).map Prod.snd

theorem sndStepF_den (x : RawEntry) (acc : List RawRatio) :
    (sndStepF gi).den (x,acc) = x.2 :: acc := rfl

theorem sndFold_den (xs : RawTable) :
    foldrDen (sndStepF gi) xs [] = xs.map Prod.snd := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [foldrDen_cons, ih, sndStepF_den]
    rfl

theorem generalF_den (x : TTensorX.den) (gs bs : List RawRatio) :
    (generalF L ri ci y ai wi gi).den (x,gs,bs) = generalR x gs bs := by
  change foldrDen (sndStepF gi)
    ((substF L ri).den ((countDataF L wi).den (x.2.1,gs,bs),
      (anchorDataF L ci y ai).den (externalAnchorCtx x,x.2.1))) [] = _
  rw [countDataF_den,anchorDataF_den,substF_den,sndFold_den]
  rfl

structure GeneralIndices.OK (P : FL.Program) : Prop where
  sndStep : P[gi.sndStep]? = some sndStepBody.compile
  sndFold : P[gi.sndFold]? = some (foldrBody (sndStepF gi) gi.sndFold).compile
  general : P[gi.general]? = some (generalBody L ri ci y ai wi gi).compile

variable {L ri ci y ai wi gi} {P : FL.Program}

theorem sndStep_valid (hi : GeneralIndices.OK L ri ci y ai wi gi P) :
    ∀ x, (sndStepF gi).ValidAt P x := by
  intro x
  apply bodySig_valid hi.sndStep
  simp [sndStepBody, tm_simp]

theorem general_valid (hL : L.OK P) (hr : LibR y P)
    (hrepair : Indices.OK L ri P) (hcanonical : CanonicalIndices.OK L ci y.append P)
    (hanchor : AnchorIndices.OK L ci y ai P) (hw : WrapperIndices.OK L ri ci y ai wi P)
    (hi : GeneralIndices.OK L ri ci y ai wi gi P) :
    ∀ x, (generalF L ri ci y ai wi gi).ValidAt P x := by
  have hf := Trans.Hash.foldr_validAll (sndStep_valid hi) hi.sndFold
  intro x
  apply bodySig_valid hi.general
  simp [generalBody,tm_simp,countData_valid hL hw,
    anchorData_valid hL hr hcanonical hanchor,subst_valid hL hrepair,hf]

theorem general_computes (hL : L.OK P) (hr : LibR y P)
    (hrepair : Indices.OK L ri P) (hcanonical : CanonicalIndices.OK L ci y.append P)
    (hanchor : AnchorIndices.OK L ci y ai P) (hw : WrapperIndices.OK L ri ci y ai wi P)
    (hi : GeneralIndices.OK L ri ci y ai wi gi P)
    (x : TTensorX.den) (gs bs : List RawRatio) :
    FL.Computes P gi.general (TFullArg.enc (x,gs,bs)) (TOutput.enc (generalR x gs bs))
      (max ((generalF L ri ci y ai wi gi).msize (x,gs,bs)) (TFullArg.enc (x,gs,bs)).size)
      ((generalF L ri ci y ai wi gi).cost (x,gs,bs))
      ((generalF L ri ci y ai wi gi).depth (x,gs,bs)) := by
  have h := (general_valid hL hr hrepair hcanonical hanchor hw hi (x,gs,bs)).computes
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [generalF_den] at h
  simpa only [generalF,Trans.Control.bodySig_idx] using h

end QecReliability.TensorMachine.GeneralRepairFL

/-! ## Semantics on the runtime grid: corner replacement of the count ratios -/
namespace QecReliability.TensorMachine.GeneralRepairFL
open FL FL.Lib FL.Lib.LinearRepairFL RationalOutput TensorBernstein TensorLatent
open SharedCircuit SharedCircuit.LatentEncoding Trans.Query RepairFL

theorem generalR_eq_cornerPrepare {n : ℕ} (ds : List ℕ)
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (q seed : ℕ) (coins : List Bool) (gs bs : Grid ds → RawRatio) :
    generalR (ds,grid ds,n,encRows rows,encProg C,q,seed,coins)
      ((RationalTensorRepair.enum ds).map gs) ((RationalTensorRepair.enum ds).map bs) =
      (TensorGeneral.cornerPrepare ds rows (circuitObservations ds C)
        (fun j => Ratio.counts (gs j).1 (bs j).1)).map toR := by
  unfold generalR
  change (substituteR
    (countDataR (grid ds) ((RationalTensorRepair.enum ds).map gs)
      ((RationalTensorRepair.enum ds).map bs))
    (anchorDataR (ds,n,encRows rows,encProg C) (grid ds))).map Prod.snd = _
  rw [← enum_indexList ds,countDataR_encode,anchorDataR_encode,substituteR_encode]
  simp only [encodeEntries,RationalPosetRepair.inputTable,TensorGeneral.cornerPrepare,
    List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply,RationalPosetRepair.anchored,TensorGeneral.cornerCoefficient,
    List.mem_filter]
  cases ht : RationalTensorRepair.cornerTest ds j with
  | true =>
    simp [hj]
    rfl
  | false => simp

end QecReliability.TensorMachine.GeneralRepairFL

/-! ## Resources -/
namespace QecReliability.TensorMachine.GeneralRepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize IxR)
open RepairFL

variable (L : Lib) (ri : Indices) (ci : CanonicalIndices)
  (y : IxR) (ai : AnchorIndices) (wi : WrapperIndices) (gi : GeneralIndices)

def sndBudget (D B N : ℕ) : ℕ := 100*((5*D+8*B+6)*(N+1)+1)

theorem sndStep_resources (D B N : ℕ) (x : RawEntry) (acc : List RawRatio)
    (hx : EntryBound D B x) (hc : ∀ z ∈ acc, RB B z) (hcn : acc.length ≤ N) :
    ResBound (sndStepF gi) (x,acc) (sndBudget D B N) := by
  have sx := entry_encoded_size hx
  have sc := output_encoded_size hc
  have scN : (TOutput.enc acc).size ≤ (8*B+4)*N+1 :=
    sc.trans (by nlinarith [Nat.mul_le_mul_left (8*B+4) hcn])
  change ((Ty.list (.prod .nat .nat)).enc acc).size ≤ (8*B+4)*N+1 at scN
  have hscale : (8*B+4)*N ≤ (5*D+8*B+6)*N := Nat.mul_le_mul_right N (by omega)
  simp only [TEntry,TRatio,Ty.enc_prod,Ty.enc_nat,Val.size_cons] at sx
  simp only [ResBound,sndStepF,bodySig_cost,bodySig_depth,bodySig_msize,sndStepBody,tm_simp]
  simp only [Ty.enc_list_cons,Ty.enc_list_cons_nat2,Val.size_cons,max_le_iff,
    sndBudget]
  simp only [Nat.mul_add,Nat.mul_one] at *
  omega

private theorem tableBound_suffix' {D B : ℕ} {xs pre ys : RawTable}
    (h : TableBound D B xs) (he : xs = pre ++ ys) : TableBound D B ys := by
  intro x hx
  apply h x
  rw [he]
  exact List.mem_append.mpr (Or.inr hx)

private theorem suffix_length' {α : Type} {xs pre ys : List α}
    (h : xs = pre ++ ys) : ys.length ≤ xs.length := by
  rw [h,List.length_append]
  omega

def sndFoldBudget (D B N : ℕ) : ℕ := 10*(sndBudget D B N+12)*(N+1)

theorem sndFold_resources (D B N : ℕ) (xs : RawTable)
    (hx : TableBound D B xs) (hxn : xs.length ≤ N) :
    ResBound (sndF gi) (xs,[]) (sndFoldBudget D B N) := by
  let M := sndBudget D B N
  have bits (ys : RawTable) (hy : TableBound D B ys) : ∀ z ∈ ys.map Prod.snd, RB B z := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact (hy x hx).2
  have hr : ∀ pre ys, xs = pre ++ ys →
      (TOutput.enc (foldrDen (sndStepF gi) ys [])).size ≤ M := by
    intro pre ys he
    rw [sndFold_den]
    have ss := output_encoded_size (bits ys (tableBound_suffix' hx he))
    have hn : (ys.map Prod.snd).length ≤ N := by
      simpa only [List.length_map] using (suffix_length' he).trans hxn
    have ssN : (TOutput.enc (ys.map Prod.snd)).size ≤ (8*B+4)*N+1 :=
      ss.trans (by nlinarith [Nat.mul_le_mul_left (8*B+4) hn])
    dsimp [M,sndBudget]
    nlinarith
  have hz : (TOutput.enc ([] : List RawRatio)).size ≤ M := by
    have he := hr xs [] (List.append_nil xs).symm
    rw [foldrDen_nil] at he
    exact he
  have hc : ∀ pre x ys, xs = pre ++ x::ys →
      ResBound (sndStepF gi) (x,foldrDen (sndStepF gi) ys []) M := by
    intro pre x ys he
    have hy := tableBound_suffix' hx he
    have hx' := hy x (by simp)
    have hys : TableBound D B ys := fun z hz => hy z (by simp [hz])
    have hsn : (ys.map Prod.snd).length ≤ N := by
      simp only [List.length_map]
      have := suffix_length' he
      simp only [List.length_cons] at this
      omega
    rw [sndFold_den]
    exact sndStep_resources gi D B N x (ys.map Prod.snd) hx' (bits ys hys) hsn
  obtain ⟨fc,fd,fm⟩ := foldr_suffix_resources (sndStepF gi) xs [] M M M hz hr hc
  have sx := table_encoded_size hx
  have sxN : (TTable.enc xs).size ≤ (5*D+8*B+6)*N+1 :=
    sx.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hxn])
  have sxM : (TTable.enc xs).size ≤ M := by
    dsimp [M,sndBudget]
    nlinarith
  have hcost : (M+12)*xs.length ≤ (M+12)*N := Nat.mul_le_mul_left _ hxn
  have sxM' : ((Ty.list TEntry).enc xs).size ≤ M := sxM
  simp only [ResBound,foldrF_cost,foldrF_depth,foldrF_msize]
  change _ ≤ 10*(M+12)*(N+1) ∧ _ ≤ 10*(M+12)*(N+1) ∧ _ ≤ 10*(M+12)*(N+1)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

def generalCombinedBudget (D B N S C A R F : ℕ) : ℕ :=
  C+A+R+F+100*S+100*(5*D+8*B+6)*(N+1)+1000

set_option maxHeartbeats 1000000 in
theorem general_resources_of_callees (D B N S C A R F : ℕ)
    (x : TTensorX.den) (gs bs : List RawRatio)
    (hinput : (TFullArg.enc (x,gs,bs)).size ≤ S)
    (hdata : TableBound D B (countDataR x.2.1 gs bs))
    (hanchors : TableBound D B (anchorDataR (externalAnchorCtx x) x.2.1))
    (hdn : (countDataR x.2.1 gs bs).length ≤ N)
    (han : (anchorDataR (externalAnchorCtx x) x.2.1).length ≤ N)
    (hC : ResBound (countDataF L wi) (x.2.1,gs,bs) C)
    (hA : ResBound (anchorDataF L ci y ai) (externalAnchorCtx x,x.2.1) A)
    (hR : ResBound (substF L ri)
      (countDataR x.2.1 gs bs,anchorDataR (externalAnchorCtx x) x.2.1) R)
    (hF : ResBound (sndF gi)
      (substituteR (countDataR x.2.1 gs bs) (anchorDataR (externalAnchorCtx x) x.2.1),[]) F)
    (hsub : (TTable.enc (substituteR (countDataR x.2.1 gs bs)
      (anchorDataR (externalAnchorCtx x) x.2.1))).size ≤ (5*D+8*B+6)*N+1) :
    ResBound (generalF L ri ci y ai wi gi) (x,gs,bs) (generalCombinedBudget D B N S C A R F) := by
  have sd := table_encoded_size hdata
  have sa := table_encoded_size hanchors
  have sdN : (TTable.enc (countDataR x.2.1 gs bs)).size ≤ (5*D+8*B+6)*N+1 :=
    sd.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hdn])
  have saN : (TTable.enc (anchorDataR (externalAnchorCtx x) x.2.1)).size ≤ (5*D+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) han])
  have sdN' : ((Ty.list TEntry).enc (countDataR x.2.1 gs bs)).size ≤ (5*D+8*B+6)*N+1 := sdN
  have saN' : ((Ty.list TEntry).enc (anchorDataR (externalAnchorCtx x) x.2.1)).size ≤
    (5*D+8*B+6)*N+1 := saN
  have ssN' : ((Ty.list TEntry).enc (substituteR (countDataR x.2.1 gs bs)
      (anchorDataR (externalAnchorCtx x) x.2.1))).size ≤ (5*D+8*B+6)*N+1 := hsub
  have sempty : (TOutput.enc ([] : List RawRatio)).size = 1 := rfl
  rcases hC with ⟨cc,cd,cm⟩
  rcases hA with ⟨ac,ad,am⟩
  rcases hR with ⟨rc,rd,rm⟩
  rcases hF with ⟨fc,fd,fm⟩
  simp only [ResBound,generalF,bodySig_cost,bodySig_depth,bodySig_msize,generalBody,tm_simp]
  repeat first | rw [countDataF_den] | rw [anchorDataF_den] | rw [substF_den]
  simp only [TFullArg,TTensorX,Trans.Wire.TX,TAnchorCtx,externalAnchorCtx,
    Ty.enc_prod,Ty.enc_list_nil,Val.size_cons,Val.size_nil,max_le_iff] at *
  have hbudget : generalCombinedBudget D B N S C A R F =
      C+A+R+F+100*S+100*((5*D+8*B+6)*N)+100*(5*D+8*B+6)+1000 := by
    unfold generalCombinedBudget
    ring
  simp only [hbudget,Trans.Wire.TRowsW,Trans.Wire.TCoordW,
    Trans.Control.TRowsP,Trans.Control.TCoord,Trans.Control.TGateP] at *
  simp only [Nat.mul_add,Nat.mul_one] at *
  omega

def generalUniformBudget (kd cd kc cc kr cr M B N S Q : ℕ) : ℕ :=
  generalCombinedBudget M (fullRatioBits kd cd M B) N S
    (countDataBudget M B N) (fullAnchorCost kd cd kc cc M Q)
    (2*tableFoldBudget M (fullRatioBits kd cd M B) (G kr cr (2*M+1)) N+100)
    (sndFoldBudget M (fullRatioBits kd cd M B) N)

/-- A fixed polynomial envelope for the complete compiled general callback, with
the same structural parameters as `RepairFL.full_resources`. -/
theorem general_resources : ∃ kd cd kc cc kr cr, ∀ (M B N S : ℕ)
    (x : TTensorX.den) (gs bs : List RawRatio),
    mag TAnchorCtx (externalAnchorCtx x) ≤ M →
    (∀ key ∈ x.2.1, mag TKey key ≤ M) →
    CountListBound B gs → CountListBound B bs →
    x.2.1.length ≤ N → gs.length ≤ N → bs.length ≤ N →
    (TFullArg.enc (x,gs,bs)).size ≤ S →
    ResBound (generalF L ri ci y ai wi gi) (x,gs,bs)
      (generalUniformBudget kd cd kc cc kr cr M B N S x.2.1.length) := by
  obtain ⟨kd,cd,kc,cc,ha⟩ := anchorData_uniform L ci y ai
  obtain ⟨kr,cr,hkeys⟩ := key_resources L ri
  refine ⟨kd,cd,kc,cc,kr,cr,?_⟩
  intro M B N S x gs bs hctx hk hg hb hkn hgn hbn hsize
  obtain ⟨hanc,hancBits⟩ := ha M (externalAnchorCtx x) x.2.1 hctx hk
  have hdata := countDataR_bound M B x.2.1 gs bs hk hg hb
  have hdata' := tableBound_mono hdata le_rfl (Nat.le_max_left _ (G kd cd (2*M+1)+1))
  have hanc' := tableBound_mono hancBits le_rfl (Nat.le_max_right (2*B+1) _)
  have hdn : (countDataR x.2.1 gs bs).length ≤ N := by
    rw [countDataR_length]
    exact hkn
  have han := (anchorDataR_length (externalAnchorCtx x) x.2.1).trans hkn
  have hcmp : KeyResources L ri M (G kr cr (2*M+1)) := hkeys M
  have hsubst := subst_resources L ri M (fullRatioBits kd cd M B) (G kr cr (2*M+1)) N
    hcmp (countDataR x.2.1 gs bs) (anchorDataR (externalAnchorCtx x) x.2.1)
    hdata' hanc' hdn han
  have hsb := substituteR_bound hdata' hanc'
  have hsn : (substituteR (countDataR x.2.1 gs bs)
      (anchorDataR (externalAnchorCtx x) x.2.1)).length ≤ N := by
    simpa only [substituteR,List.length_map] using hdn
  have hss := table_encoded_size hsb
  have hssN : (TTable.enc (substituteR (countDataR x.2.1 gs bs)
      (anchorDataR (externalAnchorCtx x) x.2.1))).size ≤
        (5*M+8*fullRatioBits kd cd M B+6)*N+1 := by
    have h2 := Nat.mul_le_mul_left (5*M+8*fullRatioBits kd cd M B+6) hsn
    unfold fullRatioBits at h2 ⊢
    linarith
  have hsnd := sndFold_resources gi M (fullRatioBits kd cd M B) N _ hsb hsn
  exact general_resources_of_callees L ri ci y ai wi gi M (fullRatioBits kd cd M B) N S _ _ _ _
    x gs bs hsize hdata' hanc' hdn han
    (countData_resources L wi M B N x.2.1 gs bs hk hg hb hkn hgn hbn) hanc hsubst hsnd hssN

end QecReliability.TensorMachine.GeneralRepairFL

#print axioms QecReliability.TensorMachine.GeneralRepairFL.general_computes
#print axioms QecReliability.TensorMachine.GeneralRepairFL.generalR_eq_cornerPrepare
#print axioms QecReliability.TensorMachine.GeneralRepairFL.general_resources
