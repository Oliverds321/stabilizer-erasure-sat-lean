import Trans.Control.Base

/-!
# Trans.Control.StepA: index table, library contract, the list-shuffling phases

* `Ix TX`: global indices of every function of the controller transcription, and the two
  external FnSigs taken as parameters: `compile : (X, key) ↦ query bits` (supplied later by the
  CNF/hash packages) and `endpoint : (X, side) ↦ ratio` (supplied by `Trans/Control/Rank.lean`).
* `LibOK P x`: the library functions and both parameters are valid at every argument.
* One FL function per controller phase (argument `(ctx, cfg)`, result the next `cfg`):
  `reverseCells selectScan trialCommit sortNext insertScan insertRestore medianLookup
  reverseGood reverseBad reverseOutput`, each with `*_valid`. Their agreement with
  `WholeWrapperCandidate.step` is proved in `StepMain.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace QecReliability.Trans.Control
open QecReliability.FL QecReliability.FL.Lib QecReliability.FL.Lib.LinearRepairFL Tm

/-- Indices (and the two external signatures). -/
structure Ix (TX : Ty) where
  compile : FnSig (.prod TX TKey) (.list .bool)
  endpoint : FnSig (.prod TX .bool) TR
  succ : ℕ
  pred : ℕ
  add : ℕ
  le : ℕ
  eq : ℕ
  max : ℕ
  mul : ℕ
  sub : ℕ
  append : ℕ
  fstE : ℕ
  mapFst : ℕ
  entry : ℕ
  ctr : ℕ
  md : ℕ
  reverseCells : ℕ
  selectScan : ℕ
  trialCommit : ℕ
  sortNext : ℕ
  insertScan : ℕ
  insertRestore : ℕ
  medianLookup : ℕ
  reverseGood : ℕ
  reverseBad : ℕ
  reverseOutput : ℕ
  fop0 : ℕ
  fop1 : ℕ
  fop2 : ℕ
  fop3 : ℕ
  fop4 : ℕ
  fop5 : ℕ
  fop6 : ℕ
  fetch : ℕ
  compileP : ℕ
  endpointZero : ℕ
  endpointOne : ℕ
  repairAcc : ℕ
  repair : ℕ
  pstep : ℕ
  prefixP : ℕ
  resume : ℕ
  dispatch : ℕ
  step : ℕ
  isDone : ℕ
  isInvoke : ℕ
  queryOf : ℕ
  answer : ℕ
  answerST : ℕ

variable {TX : Ty}

/-- `fst` of an entry. -/
def fstEBody : Tm [TEnt] .nat := .fst v0
def fstEF (i : ℕ) : FnSig TEnt .nat := bodySig i fstEBody

/-- The library and the parameters are valid everywhere. -/
structure LibOK (P : Program) (x : Ix TX) : Prop where
  compile : ∀ y, x.compile.ValidAt P y
  endpoint : ∀ y, x.endpoint.ValidAt P y
  succ : ∀ y, (succF x.succ).ValidAt P y
  pred : ∀ y, (predF x.pred).ValidAt P y
  add : ∀ y, (addF x.add).ValidAt P y
  le : ∀ y, (leF x.le).ValidAt P y
  eq : ∀ y, (eqF x.eq).ValidAt P y
  max : ∀ y, (maxF x.max).ValidAt P y
  mul : ∀ y, (mulF x.mul).ValidAt P y
  sub : ∀ y, (subF x.sub).ValidAt P y
  append : ∀ y, (appendF .bool x.append).ValidAt P y
  mapFst : ∀ y, (mapF (fstEF x.fstE) x.mapFst).ValidAt P y
  entry : ∀ y, (entryF x.entry).ValidAt P y
  ctr : ∀ y, (ctrF x.ctr).ValidAt P y
  md : ∀ y, (mdF x.md).ValidAt P y

theorem mapFst_valid {P : Program} {i j : ℕ} (hf : P[i]? = some fstEBody.compile)
    (hm : P[j]? = some (mapBody (fstEF i) j).compile) : ∀ y, (mapF (fstEF i) j).ValidAt P y :=
  fun y => map_valid hm y (fun _ _ => bodySig_valid hf (by simp [tm_simp, fstEBody]))

@[simp] theorem fstEF_den (i : ℕ) (e : ℕ × ℕ) : (fstEF i).den e = e.1 := rfl

/-- The literal `4 B` and `4 B + 1` on a natural term. -/
abbrev Tm.four {Γ : List Ty} (b : Tm Γ .nat) : Tm Γ .nat := .bit .ff (.bit .ff b)
abbrev Tm.fourOne {Γ : List Ty} (b : Tm Γ .nat) : Tm Γ .nat := .bit .tt (.bit .ff b)

@[simp] theorem bitNat_four (b : ℕ) : bitNat false (bitNat false b) = 4 * b := by
  simp [bitNat]; omega
@[simp] theorem bitNat_fourOne (b : ℕ) : bitNat true (bitNat false b) = 4 * b + 1 := by
  simp [bitNat]; omega

/-- `pc := k`. -/
abbrev setPc {Γ : List Ty} (c : Tm Γ TCfg) (k : ℕ) : Tm Γ TG0 := F.g0With c (pc := .lit k)

/-! ## The phases (argument `v0 = (ctx, cfg)`; after `letE`, `cfg` is `v0`) -/

/-- Shared cons step of the three reversals: move the head of `pairSrc` onto `pairDst`
(environment: `v0` head, `v1` tail, `v2` cfg). -/
abbrev pairMove {Γ : List Ty} : Tm (TEnt :: .list TEnt :: TCfg :: Γ) TCfg :=
  F.cfgWith v2 (g2 := F.g2With v2 (pairSrc := v1) (pairDst := .lcons v0 (F.pairDst v2)))

def reverseCellsBody : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.pairSrc v0)
    (F.cfgWith v0 (g0 := setPc v0 6)
      (g2 := F.g2With v0 (pairSrc := F.pairDst v0) (pairDst := .lnil) (selectIndex := .zero)
        (scaleFactor := .lit (1 : ℕ))))
    pairMove

def selectScanBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.pairSrc v0)
    (F.cfgWith v0 (g0 := setPc v0 7) (g2 := F.g2With v0 (selected := .lit (1 : ℕ))))
    (.ite (.app (leF x.le) (.pair (.fst v0) (Tm.four (A.B v3))))
      (F.cfgWith v2 (g0 := setPc v2 7)
        (g2 := F.g2With v2 (pairSrc := .lnil)
          (selected := .app (maxF x.max) (.pair (.lit (1 : ℕ))
            (.app (mulF x.mul) (.pair (F.scaleFactor v2) (.fst v0)))))))
      (F.cfgWith v2 (g2 := F.g2With v2 (pairSrc := v1)
        (selectIndex := .app (succF x.succ) (F.selectIndex v2))
        (scaleFactor := .bit .ff (F.scaleFactor v2)))))

def trialCommitBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <|
    F.cfgWith v0 (g0 := setPc v0 0)
      (g1 := F.g1With v0 (coefCalls := .app (addF x.add) (.pair (F.coefCalls v0) (F.trialCalls v0))))
      (g2 := F.g2With v0 (trialsRev := .lcons (.pair (F.selected v0) (F.trialCalls v0))
        (F.trialsRev v0)))

def sortNextBody : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.sortTodo v0)
    (F.cfgWith v0 (g0 := setPc v0 11)
      (g3 := F.g3With v0 (insertRight := F.sorted v0) (lookupRemaining := A.m v1)))
    (F.cfgWith v2 (g0 := setPc v2 9)
      (g3 := F.g3With v2 (sortTodo := v1) (insertValue := v0) (insertLeftRev := .lnil)
        (insertRight := F.sorted v2)))

def insertScanBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.insertRight v0)
    (F.cfgWith v0 (g0 := setPc v0 10)
      (g3 := F.g3With v0 (insertResult := .lcons (F.insertValue v0) .lnil)))
    (.ite (.app (leF x.le) (.pair (F.insertValue v2) v0))
      (F.cfgWith v2 (g0 := setPc v2 10)
        (g3 := F.g3With v2 (insertResult := .lcons (F.insertValue v2) (F.insertRight v2))))
      (F.cfgWith v2 (g3 := F.g3With v2 (insertRight := v1)
        (insertLeftRev := .lcons v0 (F.insertLeftRev v2)))))

def insertRestoreBody : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.insertLeftRev v0)
    (F.cfgWith v0 (g0 := setPc v0 8)
      (g3 := F.g3With v0 (sorted := F.insertResult v0) (insertRight := .lnil)
        (insertResult := .lnil)))
    (F.cfgWith v2 (g3 := F.g3With v2 (insertLeftRev := v1)
      (insertResult := .lcons v0 (F.insertResult v2))))

def medianLookupBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.insertRight v0)
    (F.cfgWith v0 (g0 := setPc v0 19))
    (.ite (.isZero (F.lookupRemaining v2))
      (F.cfgWith v2 (g0 := setPc v2 0) (g2 := F.g2With v2 (trialsRev := .lnil) (selected := v0))
        (g3 := F.g3With v2 (insertRight := .lnil) (sortTodo := .lnil) (sorted := .lnil)))
      (F.cfgWith v2 (g3 := F.g3With v2 (insertRight := v1)
        (lookupRemaining := .app (predF x.pred) (F.lookupRemaining v2)))))

def reverseGoodBody : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.pairSrc v0)
    (F.cfgWith v0 (g0 := setPc v0 13)
      (g2 := F.g2With v0 (pairSrc := F.badRev v0) (pairDst := .lnil))
      (g4 := F.g4With v0 (goodTable := F.pairDst v0) (badRev := .lnil)))
    pairMove

def reverseBadBody : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.pairSrc v0)
    (F.cfgWith v0 (g0 := setPc v0 14) (g2 := F.g2With v0 (pairDst := .lnil))
      (g4 := F.g4With v0 (badTable := F.pairDst v0)))
    pairMove

def reverseOutputBody : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.outputRev v0)
    (F.cfgWith v0 (g0 := setPc v0 18))
    (F.cfgWith v2 (g5 := F.g5With v2 (outputRev := v1) (output := .lcons v0 (F.output v2))))

def reverseCellsF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.reverseCells reverseCellsBody
def selectScanF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.selectScan (selectScanBody x)
def trialCommitF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.trialCommit (trialCommitBody x)
def sortNextF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.sortNext sortNextBody
def insertScanF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.insertScan (insertScanBody x)
def insertRestoreF (x : Ix TX) : FnSig (TArg TX) TCfg :=
  bodySig x.insertRestore insertRestoreBody
def medianLookupF (x : Ix TX) : FnSig (TArg TX) TCfg :=
  bodySig x.medianLookup (medianLookupBody x)
def reverseGoodF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.reverseGood reverseGoodBody
def reverseBadF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.reverseBad reverseBadBody
def reverseOutputF (x : Ix TX) : FnSig (TArg TX) TCfg :=
  bodySig x.reverseOutput reverseOutputBody

/-! ## Validity -/

section Valid
variable {P : Program} {x : Ix TX} (h : LibOK P x)
include h

theorem reverseCells_valid (hP : P[x.reverseCells]? = some (reverseCellsBody (TX := TX)).compile) :
    ∀ a, (reverseCellsF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, reverseCellsBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)
theorem selectScan_valid (hP : P[x.selectScan]? = some (selectScanBody x).compile) :
    ∀ a, (selectScanF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, selectScanBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)
theorem trialCommit_valid (hP : P[x.trialCommit]? = some (trialCommitBody x).compile) :
    ∀ a, (trialCommitF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, trialCommitBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)
theorem sortNext_valid (hP : P[x.sortNext]? = some (sortNextBody (TX := TX)).compile) :
    ∀ a, (sortNextF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, sortNextBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)
theorem insertScan_valid (hP : P[x.insertScan]? = some (insertScanBody x).compile) :
    ∀ a, (insertScanF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, insertScanBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)
theorem insertRestore_valid
    (hP : P[x.insertRestore]? = some (insertRestoreBody (TX := TX)).compile) :
    ∀ a, (insertRestoreF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, insertRestoreBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)
theorem medianLookup_valid (hP : P[x.medianLookup]? = some (medianLookupBody x).compile) :
    ∀ a, (medianLookupF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, medianLookupBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)
theorem reverseGood_valid (hP : P[x.reverseGood]? = some (reverseGoodBody (TX := TX)).compile) :
    ∀ a, (reverseGoodF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, reverseGoodBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)
theorem reverseBad_valid (hP : P[x.reverseBad]? = some (reverseBadBody (TX := TX)).compile) :
    ∀ a, (reverseBadF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, reverseBadBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)
theorem reverseOutput_valid
    (hP : P[x.reverseOutput]? = some (reverseOutputBody (TX := TX)).compile) :
    ∀ a, (reverseOutputF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp [tm_simp, reverseOutputBody, h.succ, h.pred, h.add, h.le, h.eq, h.max, h.mul, h.sub, h.append, h.mapFst, h.entry, h.ctr, h.md, h.compile, h.endpoint]
  try (split <;> simp_all)

end Valid

end QecReliability.Trans.Control
