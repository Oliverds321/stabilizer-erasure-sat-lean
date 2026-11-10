import TensorRepairFLAnchors

/-! Full controller callback: pair cached good/bad counts with runtime grid keys,
compute exact physical corner anchors, and execute the installed anchored repair.
All external data are finite lists; no target coefficient or exact anchor oracle
is supplied to this callback. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Tm FL.Lib.LinearRepairFL Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid IxR LibR)

abbrev TCountState : Ty := .prod (.list TRatio) (.prod (.list TRatio) TTable)
abbrev TTensorX : Ty := .prod TKey (.prod (.list TKey) Trans.Wire.TX)
abbrev TFullArg : Ty := .prod TTensorX (.prod (.list TRatio) (.list TRatio))

structure WrapperIndices where
  countsRatio : ℕ
  countsStep : ℕ
  countsFold : ℕ
  counts : ℕ
  full : ℕ

def countDataR : List Key → List RawRatio → List RawRatio → RawTable
  | [], _, _ => []
  | key :: keys, gs, bs =>
    (key,countsR (gs.headD (0,0)).1 (bs.headD (0,0)).1) ::
      countDataR keys gs.tail bs.tail

def countsStepR (s : List RawRatio × List RawRatio × RawTable) (key : Key) :
    List RawRatio × List RawRatio × RawTable :=
  (s.1.tail,s.2.1.tail,
    (key,countsR (s.1.headD (0,0)).1 (s.2.1.headD (0,0)).1) :: s.2.2)

theorem countsFoldR (keys : List Key) (gs bs : List RawRatio) (acc : RawTable) :
    keys.foldl countsStepR (gs,bs,acc) =
      (gs.drop keys.length,bs.drop keys.length,(countDataR keys gs bs).reverse ++ acc) := by
  induction keys generalizing gs bs acc with
  | nil => simp [countDataR]
  | cons key keys ih =>
    cases gs <;> cases bs <;>
      simp [List.foldl_cons,countsStepR,countDataR,ih,List.reverse_cons,List.append_assoc]

def externalAnchorCtx (x : TTensorX.den) : AnchorCtx :=
  (x.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1)

def fullR (x : TTensorX.den) (gs bs : List RawRatio) : List RawRatio :=
  repairR (countDataR x.2.1 gs bs) (anchorDataR (externalAnchorCtx x) x.2.1)

variable (L : Lib) (ri : Indices) (ci : CanonicalIndices)
  (y : IxR) (ai : AnchorIndices) (i : WrapperIndices)

private def countHead {Γ : List Ty} (xs : Tm Γ (.list TRatio)) : Tm Γ .nat :=
  .lcase xs .zero (.fst v0)

private def countTail {Γ : List Ty} (xs : Tm Γ (.list TRatio)) : Tm Γ (.list TRatio) :=
  .lcase xs .lnil v1

def countsStepBody : Tm [.prod TCountState TKey] TCountState :=
  .pair (countTail (.fst (.fst v0)))
    (.pair (countTail (.fst (.snd (.fst v0))))
      (.lcons (.pair (.snd v0) (.app (countsF i.countsRatio)
        (.pair (countHead (.fst (.fst v0))) (countHead (.fst (.snd (.fst v0)))))))
        (.snd (.snd (.fst v0)))))

def countsStepF := bodySig i.countsStep (countsStepBody i)

def countDataBody : Tm [.prod (.list TKey) (.prod (.list TRatio) (.list TRatio))] TTable :=
  .app (reverseF TEntry L.rev)
    (.snd (.snd (.app (foldlF (countsStepF i) i.countsFold)
      (.pair (.pair (.fst (.snd v0)) (.pair (.snd (.snd v0)) .lnil)) (.fst v0)))))

def countDataF := bodySig i.counts (countDataBody L i)

private def anchorCtxTerm {Γ : List Ty} (x : Tm Γ TTensorX) : Tm Γ TAnchorCtx :=
  .pair (.fst x) (.pair (.fst (.snd (.snd x)))
    (.pair (.fst (.snd (.snd (.snd x)))) (.fst (.snd (.snd (.snd (.snd x)))))))

def fullBody : Tm [TFullArg] TOutput :=
  .letE (.app (countDataF L i) (.pair (.fst (.snd (.fst v0))) (.snd v0))) <|
  .letE (.app (anchorDataF L ci y ai)
    (.pair (anchorCtxTerm (.fst v1)) (.fst (.snd (.fst v1))))) <|
    .app (repairF L ri) (.pair v1 v0)

def fullF := bodySig i.full (fullBody L ri ci y ai i)

theorem countsStepF_den (gs bs : List RawRatio) (acc : RawTable) (key : Key) :
    (countsStepF i).den ((gs,bs,acc),key) = countsStepR (gs,bs,acc) key := by
  cases gs <;> cases bs <;>
    simp [countsStepF,bodySig_den,countsStepBody,countHead,countTail,tm_simp,countsF_den,
      countsStepR]

theorem countsFold_den (keys : List Key) (s : List RawRatio × List RawRatio × RawTable) :
    foldlDen (countsStepF i) s keys = keys.foldl countsStepR s := by
  induction keys generalizing s with
  | nil => rfl
  | cons key keys ih =>
    rcases s with ⟨gs,bs,acc⟩
    rw [foldlDen_cons,countsStepF_den,ih,List.foldl_cons]

theorem countDataF_den (keys : List Key) (gs bs : List RawRatio) :
    (countDataF L i).den (keys,gs,bs) = countDataR keys gs bs := by
  change (foldlDen (countsStepF i) (gs,bs,[]) keys).2.2.reverse = _
  rw [countsFold_den,countsFoldR]
  simp only [List.append_nil,List.reverse_reverse]

theorem fullF_den (x : TTensorX.den) (gs bs : List RawRatio) :
    (fullF L ri ci y ai i).den (x,gs,bs) = fullR x gs bs := by
  change (repairF L ri).den
    ((countDataF L i).den (x.2.1,gs,bs),
      (anchorDataF L ci y ai).den (externalAnchorCtx x,x.2.1)) = _
  rw [countDataF_den,anchorDataF_den,repairF_den]
  rfl

theorem countDataR_length (keys : List Key) (gs bs : List RawRatio) :
    (countDataR keys gs bs).length = keys.length := by
  induction keys generalizing gs bs with
  | nil => rfl
  | cons key keys ih => simp only [countDataR,List.length_cons,ih]

structure WrapperIndices.OK (P : FL.Program) : Prop where
  countsRatio : P[i.countsRatio]? = some (countsBody L.add).compile
  countsStep : P[i.countsStep]? = some (countsStepBody i).compile
  countsFold : P[i.countsFold]? = some (foldlBody (countsStepF i) i.countsFold).compile
  counts : P[i.counts]? = some (countDataBody L i).compile
  full : P[i.full]? = some (fullBody L ri ci y ai i).compile

variable {L ri ci y ai i} {P : FL.Program}

theorem countsStep_valid (hL : L.OK P) (hi : WrapperIndices.OK L ri ci y ai i P) :
    ∀ x, (countsStepF i).ValidAt P x := by
  have hc := counts_valid hL.add hi.countsRatio
  rintro ⟨⟨gs,bs,acc⟩,key⟩
  apply bodySig_valid hi.countsStep
  cases gs <;> cases bs <;> simp [countsStepBody,countHead,countTail,tm_simp,hc]

theorem countData_valid (hL : L.OK P) (hi : WrapperIndices.OK L ri ci y ai i P) :
    ∀ x, (countDataF L i).ValidAt P x := by
  have hf := Trans.Hash.foldl_validAll (countsStep_valid hL hi) hi.countsFold
  intro x
  apply bodySig_valid hi.counts
  simp [countDataBody,tm_simp,hf,hL.rev]

theorem full_valid (hL : L.OK P) (hr : LibR y P)
    (hrepair : Indices.OK L ri P) (hcanonical : CanonicalIndices.OK L ci y.append P)
    (hanchor : AnchorIndices.OK L ci y ai P) (hi : WrapperIndices.OK L ri ci y ai i P) :
    ∀ x, (fullF L ri ci y ai i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.full
  simp [fullBody,anchorCtxTerm,tm_simp,countData_valid hL hi,
    anchorData_valid hL hr hcanonical hanchor,repair_valid hL hrepair]

/-- Full installed callback execution: counts, exact physical anchors, and
rational tensor repair. Resources are the genuine compiled FL measures. -/
theorem full_computes (hL : L.OK P) (hr : LibR y P)
    (hrepair : Indices.OK L ri P) (hcanonical : CanonicalIndices.OK L ci y.append P)
    (hanchor : AnchorIndices.OK L ci y ai P) (hi : WrapperIndices.OK L ri ci y ai i P)
    (x : TTensorX.den) (gs bs : List RawRatio) :
    FL.Computes P i.full (TFullArg.enc (x,gs,bs)) (TOutput.enc (fullR x gs bs))
      (max ((fullF L ri ci y ai i).msize (x,gs,bs)) (TFullArg.enc (x,gs,bs)).size)
      ((fullF L ri ci y ai i).cost (x,gs,bs)) ((fullF L ri ci y ai i).depth (x,gs,bs)) := by
  have h := (full_valid hL hr hrepair hcanonical hanchor hi (x,gs,bs)).computes
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [fullF_den] at h
  simpa only [fullF,Trans.Control.bodySig_idx] using h

end QecReliability.TensorMachine.RepairFL
