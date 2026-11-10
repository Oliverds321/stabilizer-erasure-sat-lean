import Trans.Control.StepB

/-!
# Trans.Control.StepP: the prefix traversal, resume, the SAT answer, dispatch

* `pstepF : (reply, pre) ↦ (ok, pre')`: one step of `PrefixTransitions.step` with the oracle
  answering `reply` (`ok = false` iff the step is `none`, then `pre' = pre`).
* `prefixPF` (`.prefix`), `resumeF` (`.resume`), `answerF` (the `.invoke` edge's successor with
  a given SAT answer: `pc := .resume, reply := b`).
* `dispatchF : (ctx, cfg) ↦ cfg'`: case distinction on the program counter; invoke/done/fault
  leave the configuration unchanged.
* Register-level interface on `ST = (ctx, cfg)`: `stepF : ST ↦ (ctx, dispatch ST)`,
  `isDoneF`, `isInvokeF`, `queryOfF : ST ↦ cfg.query`, `answerSTF : (ST, b) ↦ (ctx, answer)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.Control
open QecReliability.FL QecReliability.FL.Lib Tm

variable {TX : Ty}

/-- `ret c` as a control. -/
abbrev retC {Γ : List Ty} (c : Tm Γ .nat) : Tm Γ TCtl :=
  .pair (.lit (2 : ℕ)) (.pair c (.pair .lnil .zero))

abbrev mk4c {Γ : List Ty} {a b c d : Ty} (x₀ : Tm Γ a) (x₁ : Tm Γ b) (x₂ : Tm Γ c)
    (x₃ : Tm Γ d) : Tm Γ (.prod a (.prod b (.prod c d))) := .pair x₀ (.pair x₁ (.pair x₂ x₃))

/-- One prefix step. Environments: `[stack, ctl, arg]`; after `ncase` on the tag
`[bit, half, stack, ctl, arg]`; in the `ret`/cons case `[frame, rest, bit, half, stack, ctl, arg]`. -/
def pstepBody (x : Ix TX) : Tm [.prod .bool TPre] (.prod .bool TPre) :=
  .letE (.fst (.snd v0)) <|
  .letE (.snd (.snd v1)) <|
  .ncase (p0 v1)
    (.pair .tt (.pair (.ite (.isZero (q3 v1)) (retC .zero) (.pair (.lit (1 : ℕ)) (q1 v1))) v0))
    (.ite v0
      (.ite (.fst v4)
        (.ite (.isZero (p1 v3))
          (.pair .tt (.pair (retC (.lit (1 : ℕ))) v2))
          (.letE (.app (predF x.pred) (p1 v3))
            (.pair .tt (.pair
              (mk4c .zero v0 (.app (appendF .bool x.append) (.pair (p2 v4) (.lcons .ff .lnil)))
                (q3 v4))
              (.lcons (mk4c .ff v0 (p2 v4) (q3 v4)) v3)))))
        (.pair .tt (.pair (retC .zero) v2)))
      (.lcase v2 (.pair .ff (.pair v3 v2))
        (.ite (.fst v0)
          (.pair .tt (.pair (retC (.app (addF x.add) (.pair (p1 v0) (p1 v5)))) v1))
          (.pair .tt (.pair
            (mk4c .zero (p1 v0) (.app (appendF .bool x.append) (.pair (p2 v0) (.lcons .tt .lnil)))
              (.app (subF x.sub) (.pair (q3 v0) (p1 v5))))
            (.lcons (mk4c .tt (p1 v5) .lnil .zero) v1))))))

def pstepF (x : Ix TX) : FnSig (.prod .bool TPre) (.prod .bool TPre) :=
  bodySig x.pstep (pstepBody x)

/-- `.prefix`. -/
def prefixPBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <|
  .ite (Tm.eqLit x (p0 (p0 (F.pre v0))) 1)
    (F.cfgWith v0 (g0 := F.g0With v0 (pc := .lit (2 : ℕ)) (tag := .tt))
      (g1 := F.g1With v0 (request := mk6 .tt (F.good v0) (F.coef v0) (F.rep v0) (F.scale v0)
        (p2 (p0 (F.pre v0))))))
    (.letE (.app (pstepF x) (.pair .ff (F.pre v0))) <|
      .ite (.fst v0)
        (F.cfgWith v1 (g1 := F.g1With v1 (pre := .snd v0)))
        (F.cfgWith v1 (g0 := setPc v1 0)
          (g1 := F.g1With v1
            (trialCalls := .app (addF x.add) (.pair (F.trialCalls v1) (F.cellCalls v1))))
          (g2 := F.g2With v1 (cellsRev := .lcons (.pair (p1 (p0 (F.pre v1))) (F.cellCalls v1))
            (F.cellsRev v1)))))

def prefixPF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.prefixP (prefixPBody x)

/-- `.resume`. -/
def resumeBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <|
  .ite (F.tag v0)
    (.letE (.app (pstepF x) (.pair (F.reply v0) (F.pre v0))) <|
      .ite (.fst v0)
        (F.cfgWith v1 (g0 := setPc v1 1)
          (g1 := F.g1With v1 (query := .lnil) (pre := .snd v0)
            (cellCalls := .app (succF x.succ) (F.cellCalls v1))))
        (F.cfgWith v1 (g0 := setPc v1 19)))
    (F.cfgWith v0 (g0 := F.g0With v0 (pc := .lit (0 : ℕ)) (nonempty := F.reply v0))
      (g1 := F.g1With v0 (query := .lnil) (trialCalls := .lit (1 : ℕ))))

def resumeF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.resume (resumeBody x)

/-- The successor of the `.invoke` edge with SAT answer `b`. -/
def answerBody : Tm [.prod (TArg TX) .bool] TCfg :=
  .letE (A.cfg (.fst v0)) <|
    F.cfgWith v0 (g0 := setPc v0 4) (g1 := F.g1With v0 (reply := .snd v1))

def answerF (x : Ix TX) : FnSig (.prod (TArg TX) .bool) TCfg := bodySig x.answer answerBody

/-- Dispatch on the program counter (`v0 = pc`, `v1 = (ctx, cfg)`). -/
def dispatchBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (F.pc (A.cfg v0)) <|
  .ite (.isZero v0) (.app (fetchF x) v1) <|
  .ite (Tm.eqLit x v0 1) (.app (prefixPF x) v1) <|
  .ite (Tm.eqLit x v0 2) (.app (compilePF x) v1) <|
  .ite (Tm.eqLit x v0 4) (.app (resumeF x) v1) <|
  .ite (Tm.eqLit x v0 5) (.app (reverseCellsF x) v1) <|
  .ite (Tm.eqLit x v0 6) (.app (selectScanF x) v1) <|
  .ite (Tm.eqLit x v0 7) (.app (trialCommitF x) v1) <|
  .ite (Tm.eqLit x v0 8) (.app (sortNextF x) v1) <|
  .ite (Tm.eqLit x v0 9) (.app (insertScanF x) v1) <|
  .ite (Tm.eqLit x v0 10) (.app (insertRestoreF x) v1) <|
  .ite (Tm.eqLit x v0 11) (.app (medianLookupF x) v1) <|
  .ite (Tm.eqLit x v0 12) (.app (reverseGoodF x) v1) <|
  .ite (Tm.eqLit x v0 13) (.app (reverseBadF x) v1) <|
  .ite (Tm.eqLit x v0 14) (.app (endpointZeroF x) v1) <|
  .ite (Tm.eqLit x v0 15) (.app (endpointOneF x) v1) <|
  .ite (Tm.eqLit x v0 16) (.app (repairF x) v1) <|
  .ite (Tm.eqLit x v0 17) (.app (reverseOutputF x) v1) (A.cfg v1)

def dispatchF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.dispatch (dispatchBody x)

/-! ## Register-level interface on `ST = (ctx, cfg)` -/

def stepBody (x : Ix TX) : Tm [TArg TX] (TArg TX) := .pair (.fst v0) (.app (dispatchF x) v0)
def isDoneBody (x : Ix TX) : Tm [TArg TX] .bool :=
  .letE (F.pc (A.cfg v0)) (.or (Tm.eqLit x v0 18) (Tm.eqLit x v0 19))
def isInvokeBody (x : Ix TX) : Tm [TArg TX] .bool := Tm.eqLit x (F.pc (A.cfg v0)) 3
def queryOfBody : Tm [TArg TX] (.list .bool) := F.query (A.cfg v0)
def answerSTBody (x : Ix TX) : Tm [.prod (TArg TX) .bool] (TArg TX) :=
  .pair (.fst (.fst v0)) (.app (answerF x) v0)

def stepF (x : Ix TX) : FnSig (TArg TX) (TArg TX) := bodySig x.step (stepBody x)
def isDoneF (x : Ix TX) : FnSig (TArg TX) .bool := bodySig x.isDone (isDoneBody x)
def isInvokeF (x : Ix TX) : FnSig (TArg TX) .bool := bodySig x.isInvoke (isInvokeBody x)
def queryOfF (x : Ix TX) : FnSig (TArg TX) (.list .bool) := bodySig x.queryOf queryOfBody
def answerSTF (x : Ix TX) : FnSig (.prod (TArg TX) .bool) (TArg TX) :=
  bodySig x.answerST (answerSTBody x)

/-! ## Validity -/

section Valid
variable {P : Program} {x : Ix TX} (h : LibOK P x)
include h

theorem pstep_valid (hP : P[x.pstep]? = some (pstepBody x).compile) :
    ∀ a, (pstepF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp only [tm_simp, pstepBody]
  split
  · simp
  · split <;> simp [h.pred, h.append, h.add, h.sub] <;> split <;> simp_all [h.add, h.sub, h.append]

theorem prefixP_valid (hs : ∀ a, (pstepF x).ValidAt P a)
    (hP : P[x.prefixP]? = some (prefixPBody x).compile) : ∀ a, (prefixPF x).ValidAt P a := by
  intro a; apply bodySig_valid hP; simp [tm_simp, prefixPBody, hs, h.eq, h.add]

theorem resume_valid (hs : ∀ a, (pstepF x).ValidAt P a)
    (hP : P[x.resume]? = some (resumeBody x).compile) : ∀ a, (resumeF x).ValidAt P a := by
  intro a; apply bodySig_valid hP; simp [tm_simp, resumeBody, hs, h.succ]

theorem answer_valid (hP : P[x.answer]? = some (answerBody (TX := TX)).compile) :
    ∀ a, (answerF x).ValidAt P a := by
  intro a; apply bodySig_valid hP; simp [tm_simp, answerBody]

end Valid

/-- Validity of every phase function (the hypotheses of `dispatch_valid`). -/
structure PhasesOK (P : Program) (x : Ix TX) : Prop where
  fetch : ∀ a, (fetchF x).ValidAt P a
  prefixP : ∀ a, (prefixPF x).ValidAt P a
  compileP : ∀ a, (compilePF x).ValidAt P a
  resume : ∀ a, (resumeF x).ValidAt P a
  reverseCells : ∀ a, (reverseCellsF x).ValidAt P a
  selectScan : ∀ a, (selectScanF x).ValidAt P a
  trialCommit : ∀ a, (trialCommitF x).ValidAt P a
  sortNext : ∀ a, (sortNextF x).ValidAt P a
  insertScan : ∀ a, (insertScanF x).ValidAt P a
  insertRestore : ∀ a, (insertRestoreF x).ValidAt P a
  medianLookup : ∀ a, (medianLookupF x).ValidAt P a
  reverseGood : ∀ a, (reverseGoodF x).ValidAt P a
  reverseBad : ∀ a, (reverseBadF x).ValidAt P a
  endpointZero : ∀ a, (endpointZeroF x).ValidAt P a
  endpointOne : ∀ a, (endpointOneF x).ValidAt P a
  repair : ∀ a, (repairF x).ValidAt P a
  reverseOutput : ∀ a, (reverseOutputF x).ValidAt P a

section Valid2
variable {P : Program} {x : Ix TX} (h : LibOK P x) (hp : PhasesOK P x)
include h hp

theorem dispatch_valid (hP : P[x.dispatch]? = some (dispatchBody x).compile) :
    ∀ a, (dispatchF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp only [tm_simp, dispatchBody]
  simp [h.eq, hp.fetch, hp.prefixP, hp.compileP, hp.resume, hp.reverseCells, hp.selectScan,
    hp.trialCommit, hp.sortNext, hp.insertScan, hp.insertRestore, hp.medianLookup, hp.reverseGood,
    hp.reverseBad, hp.endpointZero, hp.endpointOne, hp.repair, hp.reverseOutput]

end Valid2

end QecReliability.Trans.Control
