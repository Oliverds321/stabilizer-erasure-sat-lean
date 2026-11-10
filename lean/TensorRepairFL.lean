import TensorRepairFLPlain
import Trans.Wire.Header

/-! Actual typed FL bodies for multivariate anchored rational repair. Every loop
uses an existing certified list fold, and every ratio comparison uses the
certified cross-multiplication implementation. The installed execution theorem
below refers to compiled FL evaluation with compositional measured resources. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Tm FL.Lib.LinearRepairFL Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid)

abbrev TKey : Ty := .list .nat
abbrev TRatio : Ty := .prod .nat .nat
abbrev TEntry : Ty := .prod TKey TRatio
abbrev TTable : Ty := .list TEntry
abbrev TOutput : Ty := .list TRatio
abbrev TScanState : Ty := .prod TKey TRatio
abbrev TOutState : Ty := .prod (.prod TTable TTable) TOutput

structure Indices where
  lesser : ℕ
  greater : ℕ
  keyStep : ℕ
  keyFold : ℕ
  keyLe : ℕ
  keyEq : ℕ
  lowerStep : ℕ
  lowerFold : ℕ
  lower : ℕ
  upperStep : ℕ
  upperFold : ℕ
  upper : ℕ
  anchorStep : ℕ
  anchorFold : ℕ
  anchor : ℕ
  substStep : ℕ
  substFold : ℕ
  subst : ℕ
  point : ℕ
  outStep : ℕ
  outFold : ℕ
  repair : ℕ

variable (L : Lib) (i : Indices)

def keyStepBody : Tm [.prod (.prod TKey .bool) .nat] (.prod TKey .bool) :=
  .lcase (.fst (.fst v0)) (.pair .lnil .ff)
    (.pair v1 (.and (.snd (.fst v2)) (.app (leF L.le) (.pair (.snd v2) v0))))

def keyStepF := bodySig i.keyStep (keyStepBody L)

def keyLeBody : Tm [.prod TKey TKey] .bool :=
  .letE (.app (foldlF (keyStepF L i) i.keyFold)
    (.pair (.pair (.snd v0) .tt) (.fst v0))) <|
    .lcase (.fst v0) (.snd v0) .ff

def keyLeF := bodySig i.keyLe (keyLeBody L i)

def keyEqBody : Tm [.prod TKey TKey] .bool :=
  .and (.app (keyLeF L i) v0) (.app (keyLeF L i) (.pair (.snd v0) (.fst v0)))

def keyEqF := bodySig i.keyEq (keyEqBody L i)

def lowerStepBody : Tm [.prod TEntry TScanState] TScanState :=
  .pair (.fst (.snd v0))
    (.ite (.app (keyLeF L i) (.pair (.fst (.fst v0)) (.fst (.snd v0))))
      (.app (lesserF i.lesser) (.pair (.snd (.fst v0)) (.snd (.snd v0))))
      (.snd (.snd v0)))

def lowerStepF := bodySig i.lowerStep (lowerStepBody L i)

def lowerBody : Tm [.prod TTable TKey] TRatio :=
  .snd (.app (foldrF (lowerStepF L i) i.lowerFold)
    (.pair (.fst v0) (.pair (.snd v0) (.pair (.lit (1 : ℕ)) (.lit (1 : ℕ))))))

def lowerF := bodySig i.lower (lowerBody L i)

def upperStepBody : Tm [.prod TEntry TScanState] TScanState :=
  .pair (.fst (.snd v0))
    (.ite (.app (keyLeF L i) (.pair (.fst (.snd v0)) (.fst (.fst v0))))
      (.app (greaterF i.greater) (.pair (.snd (.fst v0)) (.snd (.snd v0))))
      (.snd (.snd v0)))

def upperStepF := bodySig i.upperStep (upperStepBody L i)

def upperBody : Tm [.prod TTable TKey] TRatio :=
  .snd (.app (foldrF (upperStepF L i) i.upperFold)
    (.pair (.fst v0) (.pair (.snd v0) (.pair .zero (.lit (1 : ℕ))))))

def upperF := bodySig i.upper (upperBody L i)

def anchorStepBody : Tm [.prod TEntry TScanState] TScanState :=
  .pair (.fst (.snd v0))
    (.ite (.app (keyEqF L i) (.pair (.fst (.fst v0)) (.fst (.snd v0))))
      (.snd (.fst v0)) (.snd (.snd v0)))

def anchorStepF := bodySig i.anchorStep (anchorStepBody L i)

def anchorBody : Tm [.prod TTable TScanState] TRatio :=
  .snd (.app (foldrF (anchorStepF L i) i.anchorFold) v0)

def anchorF := bodySig i.anchor (anchorBody L i)

def substStepBody : Tm [.prod TEntry (.prod TTable TTable)] (.prod TTable TTable) :=
  .pair (.fst (.snd v0))
    (.lcons (.pair (.fst (.fst v0))
      (.app (anchorF L i) (.pair (.fst (.snd v0)) (.fst v0)))) (.snd (.snd v0)))

def substStepF := bodySig i.substStep (substStepBody L i)

def substBody : Tm [.prod TTable TTable] TTable :=
  .snd (.app (foldrF (substStepF L i) i.substFold)
    (.pair (.fst v0) (.pair (.snd v0) .lnil)))

def substF := bodySig i.subst (substBody L i)

def pointBody : Tm [.prod TTable (.prod TTable TKey)] TRatio :=
  .app (greaterF i.greater)
    (.pair (.app (upperF L i) (.snd v0))
      (.app (lowerF L i) (.pair (.fst v0) (.snd (.snd v0)))))

def pointF := bodySig i.point (pointBody L i)

def outStepBody : Tm [.prod TEntry TOutState] TOutState :=
  .pair (.fst (.snd v0))
    (.lcons (.app (pointF L i)
      (.pair (.fst (.fst (.snd v0)))
        (.pair (.snd (.fst (.snd v0))) (.fst (.fst v0))))) (.snd (.snd v0)))

def outStepF := bodySig i.outStep (outStepBody L i)

def repairBody : Tm [.prod TTable TTable] TOutput :=
  .letE (.app (substF L i) v0) <|
    .snd (.app (foldrF (outStepF L i) i.outFold)
      (.pair (.fst v1) (.pair (.pair v0 (.snd v1)) .lnil)))

def repairF := bodySig i.repair (repairBody L i)

theorem keyStepF_den (ys : Key) (b : Bool) (x : ℕ) :
    (keyStepF L i).den ((ys,b),x) = keyStepR (ys,b) x := by
  cases ys <;> simp [keyStepF, bodySig_den, keyStepBody, keyStepR, tm_simp]

theorem keyFold_den (xs : Key) (s : Key × Bool) :
    foldlDen (keyStepF L i) s xs = xs.foldl keyStepR s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rcases s with ⟨ys,b⟩
    rw [foldlDen_cons, keyStepF_den, ih, List.foldl_cons]

theorem keyLeF_den (xs ys : Key) : (keyLeF L i).den (xs,ys) = keyLe xs ys := by
  simp only [keyLeF,bodySig_den,keyLeBody,tm_simp,foldlF_den]
  rw [keyFold_den]
  have h := keyFold_finish xs ys true
  generalize he : xs.foldl keyStepR (ys,true) = s at h ⊢
  rcases s with ⟨zs,b⟩
  cases zs <;> simpa only [keyFinish,Bool.true_and] using h

theorem keyEqF_den (xs ys : Key) : (keyEqF L i).den (xs,ys) = keyEq xs ys := by
  change (if (keyLeF L i).den (xs,ys) then (keyLeF L i).den (ys,xs) else false) = _
  rw [keyLeF_den, keyLeF_den]
  unfold keyEq
  cases keyLe xs ys <;> rfl

theorem lowerStepF_den (k j : Key) (x z : RawRatio) :
    (lowerStepF L i).den ((k,x),(j,z)) =
      (j, if keyLe k j then lesserR x z else z) := by
  change (j, if (keyLeF L i).den (k,j) then lesserR x z else z) = _
  rw [keyLeF_den]

theorem lowerFold_den (data : RawTable) (j : Key) :
    foldrDen (lowerStepF L i) data (j,(1,1)) = (j,lowerR data j) := by
  induction data with
  | nil => rfl
  | cons ix xs ih =>
    rcases ix with ⟨k,x⟩
    rw [foldrDen_cons, ih, lowerStepF_den, lowerR]

theorem lowerF_den (data : RawTable) (j : Key) :
    (lowerF L i).den (data,j) = lowerR data j := by
  change (foldrDen (lowerStepF L i) data (j,(1,1))).2 = _
  rw [lowerFold_den]

theorem upperStepF_den (k j : Key) (x z : RawRatio) :
    (upperStepF L i).den ((k,x),(j,z)) =
      (j, if keyLe j k then greaterR x z else z) := by
  change (j, if (keyLeF L i).den (j,k) then greaterR x z else z) = _
  rw [keyLeF_den]

theorem upperFold_den (data : RawTable) (j : Key) :
    foldrDen (upperStepF L i) data (j,(0,1)) = (j,upperR data j) := by
  induction data with
  | nil => rfl
  | cons ix xs ih =>
    rcases ix with ⟨k,x⟩
    rw [foldrDen_cons, ih, upperStepF_den, upperR]

theorem upperF_den (data : RawTable) (j : Key) :
    (upperF L i).den (data,j) = upperR data j := by
  change (foldrDen (upperStepF L i) data (j,(0,1))).2 = _
  rw [upperFold_den]

theorem anchorStepF_den (k j : Key) (x z : RawRatio) :
    (anchorStepF L i).den ((k,x),(j,z)) = (j, if keyEq k j then x else z) := by
  change (j, if (keyEqF L i).den (k,j) then x else z) = _
  rw [keyEqF_den]

theorem anchorFold_den (data : RawTable) (j : Key) (z : RawRatio) :
    foldrDen (anchorStepF L i) data (j,z) = (j,anchorR data j z) := by
  induction data with
  | nil => rfl
  | cons ix xs ih =>
    rcases ix with ⟨k,x⟩
    rw [foldrDen_cons, ih, anchorStepF_den, anchorR]

theorem anchorF_den (data : RawTable) (j : Key) (z : RawRatio) :
    (anchorF L i).den (data,j,z) = anchorR data j z := by
  change (foldrDen (anchorStepF L i) data (j,z)).2 = _
  rw [anchorFold_den]

theorem substStepF_den (k : Key) (x : RawRatio) (anchors acc : RawTable) :
    (substStepF L i).den ((k,x),anchors,acc) =
      (anchors,(k,anchorR anchors k x)::acc) := by
  change (anchors,(k,(anchorF L i).den (anchors,k,x))::acc) = _
  rw [anchorF_den]

theorem substFold_den (data anchors : RawTable) :
    foldrDen (substStepF L i) data (anchors,[]) = (anchors,substituteR data anchors) := by
  induction data with
  | nil => rfl
  | cons ix xs ih =>
    rcases ix with ⟨k,x⟩
    rw [foldrDen_cons, ih, substStepF_den]
    rfl

theorem substF_den (data anchors : RawTable) :
    (substF L i).den (data,anchors) = substituteR data anchors := by
  change (foldrDen (substStepF L i) data (anchors,[])).2 = _
  rw [substFold_den]

theorem pointF_den (data anchors : RawTable) (j : Key) :
    (pointF L i).den (data,anchors,j) = pointR data anchors j := by
  change greaterR ((upperF L i).den (anchors,j)) ((lowerF L i).den (data,j)) = _
  rw [upperF_den,lowerF_den]
  rfl

theorem outStepF_den (k : Key) (x : RawRatio) (data anchors : RawTable) (acc : List RawRatio) :
    (outStepF L i).den ((k,x),(data,anchors),acc) =
      ((data,anchors),pointR data anchors k :: acc) := by
  change ((data,anchors),(pointF L i).den (data,anchors,k)::acc) = _
  rw [pointF_den]

theorem outFold_den (xs data anchors : RawTable) :
    foldrDen (outStepF L i) xs ((data,anchors),[]) =
      ((data,anchors),xs.map (fun ix => pointR data anchors ix.1)) := by
  induction xs with
  | nil => rfl
  | cons ix xs ih =>
    rcases ix with ⟨k,x⟩
    rw [foldrDen_cons, ih, outStepF_den]
    rfl

theorem repairF_den (data anchors : RawTable) :
    (repairF L i).den (data,anchors) = repairR data anchors := by
  change (foldrDen (outStepF L i) data (((substF L i).den (data,anchors),anchors),[])).2 = _
  rw [substF_den,outFold_den]
  rfl

structure Indices.OK (P : FL.Program) : Prop where
  lesser : P[i.lesser]? = some (lesserBody L.mul L.le).compile
  greater : P[i.greater]? = some (greaterBody L.mul L.le).compile
  keyStep : P[i.keyStep]? = some (keyStepBody L).compile
  keyFold : P[i.keyFold]? = some (foldlBody (keyStepF L i) i.keyFold).compile
  keyLe : P[i.keyLe]? = some (keyLeBody L i).compile
  keyEq : P[i.keyEq]? = some (keyEqBody L i).compile
  lowerStep : P[i.lowerStep]? = some (lowerStepBody L i).compile
  lowerFold : P[i.lowerFold]? = some (foldrBody (lowerStepF L i) i.lowerFold).compile
  lower : P[i.lower]? = some (lowerBody L i).compile
  upperStep : P[i.upperStep]? = some (upperStepBody L i).compile
  upperFold : P[i.upperFold]? = some (foldrBody (upperStepF L i) i.upperFold).compile
  upper : P[i.upper]? = some (upperBody L i).compile
  anchorStep : P[i.anchorStep]? = some (anchorStepBody L i).compile
  anchorFold : P[i.anchorFold]? = some (foldrBody (anchorStepF L i) i.anchorFold).compile
  anchor : P[i.anchor]? = some (anchorBody L i).compile
  substStep : P[i.substStep]? = some (substStepBody L i).compile
  substFold : P[i.substFold]? = some (foldrBody (substStepF L i) i.substFold).compile
  subst : P[i.subst]? = some (substBody L i).compile
  point : P[i.point]? = some (pointBody L i).compile
  outStep : P[i.outStep]? = some (outStepBody L i).compile
  outFold : P[i.outFold]? = some (foldrBody (outStepF L i) i.outFold).compile
  repair : P[i.repair]? = some (repairBody L i).compile

variable {L i} {P : FL.Program}

theorem keyStep_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (keyStepF L i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.keyStep
  simp [keyStepBody, tm_simp, hL.le] <;> split <;> trivial

theorem keyLe_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (keyLeF L i).ValidAt P x := by
  have hf := Trans.Hash.foldl_validAll (keyStep_valid hL hi) hi.keyFold
  intro x
  apply bodySig_valid hi.keyLe
  simp [keyLeBody, tm_simp, hf] <;> split <;> trivial

theorem keyEq_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (keyEqF L i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.keyEq
  simp [keyEqBody, tm_simp, keyLe_valid hL hi]

theorem lowerStep_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (lowerStepF L i).ValidAt P x := by
  have hl := lesser_valid hL.mul hL.le hi.lesser
  intro x
  apply bodySig_valid hi.lowerStep
  simp [lowerStepBody, tm_simp, keyLe_valid hL hi, hl]

theorem lower_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (lowerF L i).ValidAt P x := by
  have hf := Trans.Hash.foldr_validAll (lowerStep_valid hL hi) hi.lowerFold
  intro x
  apply bodySig_valid hi.lower
  simp [lowerBody, tm_simp, hf]

theorem upperStep_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (upperStepF L i).ValidAt P x := by
  have hg := greater_valid hL.mul hL.le hi.greater
  intro x
  apply bodySig_valid hi.upperStep
  simp [upperStepBody, tm_simp, keyLe_valid hL hi, hg]

theorem upper_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (upperF L i).ValidAt P x := by
  have hf := Trans.Hash.foldr_validAll (upperStep_valid hL hi) hi.upperFold
  intro x
  apply bodySig_valid hi.upper
  simp [upperBody, tm_simp, hf]

theorem anchorStep_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (anchorStepF L i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.anchorStep
  simp [anchorStepBody, tm_simp, keyEq_valid hL hi]

theorem anchor_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (anchorF L i).ValidAt P x := by
  have hf := Trans.Hash.foldr_validAll (anchorStep_valid hL hi) hi.anchorFold
  intro x
  apply bodySig_valid hi.anchor
  simp [anchorBody, tm_simp, hf]

theorem substStep_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (substStepF L i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.substStep
  simp [substStepBody, tm_simp, anchor_valid hL hi]

theorem subst_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (substF L i).ValidAt P x := by
  have hf := Trans.Hash.foldr_validAll (substStep_valid hL hi) hi.substFold
  intro x
  apply bodySig_valid hi.subst
  simp [substBody, tm_simp, hf]

theorem point_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (pointF L i).ValidAt P x := by
  have hg := greater_valid hL.mul hL.le hi.greater
  intro x
  apply bodySig_valid hi.point
  simp [pointBody, tm_simp, lower_valid hL hi, upper_valid hL hi, hg]

theorem outStep_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (outStepF L i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.outStep
  simp [outStepBody, tm_simp, point_valid hL hi]

theorem repair_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (repairF L i).ValidAt P x := by
  have hf := Trans.Hash.foldr_validAll (outStep_valid hL hi) hi.outFold
  intro x
  apply bodySig_valid hi.repair
  simp [repairBody, tm_simp, subst_valid hL hi, hf]

/-- Compiled repair execution with its actual compositional cost/depth/space.
Closed polynomial envelopes are proved separately; no comparison counter is
substituted for this machine execution bound. -/
theorem repair_computes (hL : L.OK P) (hi : Indices.OK L i P) (data anchors : RawTable) :
    FL.Computes P i.repair ((Ty.prod TTable TTable).enc (data,anchors))
      (TOutput.enc (repairR data anchors))
      (max ((repairF L i).msize (data,anchors)) ((Ty.prod TTable TTable).enc (data,anchors)).size)
      ((repairF L i).cost (data,anchors)) ((repairF L i).depth (data,anchors)) := by
  have h := (repair_valid hL hi (data,anchors)).computes
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [repairF_den] at h
  simpa only [repairF, Trans.Control.bodySig_idx] using h

end QecReliability.TensorMachine.RepairFL
