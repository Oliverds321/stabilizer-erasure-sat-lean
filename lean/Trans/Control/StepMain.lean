import Trans.Control.StepP

/-!
# Trans.Control.StepMain: the transcription computes `WholeWrapperCandidate.step`

For every phase `X` (all program counters except `.invoke`, `.done`, `.fault`):
`X_correct : (step q r B m true ext s).map (encCfg ∘ next) = some ((XF x).den (ctx, encCfg s))`
with `ctx = encCtx q r B m X`, assuming (only for `.compile` / the endpoints) that the external
parameters agree with `ext` at the needed arguments (`hQ`, `hE`).

Assembled (`dispatch_correct`, `step_correct`): one FL call of `stepF` is one controller edge.
The register-loop helpers: `isDone_correct` (`= decide (step … = none)`), `isInvoke_correct`,
`queryOf_correct`, and `answer_correct` (the `.invoke` edge's successor with the SAT answer).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.Control
open QecReliability.FL QecReliability.FL.Lib QecReliability.FL.Lib.LinearRepairFL Tm
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.RationalOutput

variable {TX : Ty}

attribute [ctl_simp] WholeWrapperCandidate.step localEdge bodySig_den encCfg encCtx pcCode encTag
  encPre encCtl encFrame encOp reverseCellsF selectScanF trialCommitF sortNextF insertScanF
  insertRestoreF medianLookupF reverseGoodF reverseBadF reverseOutputF reverseCellsBody
  selectScanBody trialCommitBody sortNextBody insertScanBody insertRestoreBody medianLookupBody
  reverseGoodBody reverseBadBody reverseOutputBody fop0F fop1F fop2F fop3F fop4F fop5F fop6F fop0Body
  fop1Body fop2Body fop3Body fop4Body fop5Body fop6Body fetchF fetchBody compilePF compilePBody
  endpointZeroF endpointZeroBody endpointOneF endpointOneBody repairAccF repairAccBody repairF
  repairBody pstepF pstepBody prefixPF prefixPBody resumeF resumeBody answerF answerBody
  PrefixTransitions.step emptyReply

section Phases
variable (x : Ix TX) (q r B m : ℕ) (X : TX.den) (ext : External) (s : Config)

/-- The common statement. -/
def Agrees (G : FnSig (TArg TX) TCfg) : Prop :=
  (WholeWrapperCandidate.step q r B m true ext s).map (fun e => encCfg e.next) =
    some (G.den (encCtx q r B m X, encCfg s))

theorem reverseCells_correct (hpc : s.pc = .reverseCells) : Agrees q r B m X ext s (reverseCellsF x) := by
  unfold Agrees; rcases hs : s.pairSrc with _ | ⟨e, es⟩ <;> simp [ctl_simp, tm_simp, hpc, hs]

theorem selectScan_correct (hpc : s.pc = .selectScan) : Agrees q r B m X ext s (selectScanF x) := by
  unfold Agrees; rcases hs : s.pairSrc with _ | ⟨e, es⟩
  · simp [ctl_simp, tm_simp, hpc, hs]
  · by_cases hb : e.1 ≤ 4 * B <;>
      simp [ctl_simp, tm_simp, hpc, hs, hb, -bitNat_false, -bitNat_true, bitNat_four] <;>
      simp [bitNat]

theorem trialCommit_correct (hpc : s.pc = .trialCommit) : Agrees q r B m X ext s (trialCommitF x) := by
  unfold Agrees; simp [ctl_simp, tm_simp, hpc]

theorem sortNext_correct (hpc : s.pc = .sortNext) : Agrees q r B m X ext s (sortNextF x) := by
  unfold Agrees; rcases hs : s.sortTodo with _ | ⟨e, es⟩ <;> simp [ctl_simp, tm_simp, hpc, hs]

theorem insertScan_correct (hpc : s.pc = .insertScan) : Agrees q r B m X ext s (insertScanF x) := by
  unfold Agrees; rcases hs : s.insertRight with _ | ⟨e, es⟩
  · simp [ctl_simp, tm_simp, hpc, hs]
  · by_cases hb : s.insertValue ≤ e <;> simp [ctl_simp, tm_simp, hpc, hs, hb]

theorem insertRestore_correct (hpc : s.pc = .insertRestore) :
    Agrees q r B m X ext s (insertRestoreF x) := by
  unfold Agrees; rcases hs : s.insertLeftRev with _ | ⟨e, es⟩ <;> simp [ctl_simp, tm_simp, hpc, hs]

theorem medianLookup_correct (hpc : s.pc = .medianLookup) :
    Agrees q r B m X ext s (medianLookupF x) := by
  unfold Agrees; rcases hs : s.insertRight with _ | ⟨e, es⟩
  · simp [ctl_simp, tm_simp, hpc, hs]
  · by_cases hb : s.lookupRemaining = 0 <;> simp [ctl_simp, tm_simp, hpc, hs, hb]

theorem reverseGood_correct (hpc : s.pc = .reverseGood) : Agrees q r B m X ext s (reverseGoodF x) := by
  unfold Agrees; rcases hs : s.pairSrc with _ | ⟨e, es⟩ <;> simp [ctl_simp, tm_simp, hpc, hs]

theorem reverseBad_correct (hpc : s.pc = .reverseBad) : Agrees q r B m X ext s (reverseBadF x) := by
  unfold Agrees; rcases hs : s.pairSrc with _ | ⟨e, es⟩ <;> simp [ctl_simp, tm_simp, hpc, hs]

theorem reverseOutput_correct (hpc : s.pc = .reverseOutput) :
    Agrees q r B m X ext s (reverseOutputF x) := by
  unfold Agrees; rcases hs : s.outputRev with _ | ⟨e, es⟩ <;> simp [ctl_simp, tm_simp, hpc, hs]

theorem fetch_correct (hpc : s.pc = .fetch) : Agrees q r B m X ext s (fetchF x) := by
  unfold Agrees; rcases hs : s.code with _ | ⟨op, rest⟩
  · simp [ctl_simp, tm_simp, hpc, hs]
  · cases op <;>
      simp [ctl_simp, tm_simp, encKey, hpc, hs, -bitNat_false, -bitNat_true, bitNat_fourOne] <;>
      split <;> simp_all

theorem compile_correct (hpc : s.pc = .compile)
    (hQ : x.compile.den (X, encKey s.request) = (ext.compileQuery s.request).bits) :
    Agrees q r B m X ext s (compilePF x) := by
  unfold Agrees; simp [ctl_simp, tm_simp, hpc, hQ]

theorem endpointZero_correct (hpc : s.pc = .endpointZero)
    (hE : x.endpoint.den (X, false) = toR (ext.endpoint false).value) :
    Agrees q r B m X ext s (endpointZeroF x) := by
  unfold Agrees; simp [ctl_simp, tm_simp, hpc, hE]

theorem endpointOne_correct (hpc : s.pc = .endpointOne)
    (hE : x.endpoint.den (X, true) = toR (ext.endpoint true).value) :
    Agrees q r B m X ext s (endpointOneF x) := by
  unfold Agrees; simp [ctl_simp, tm_simp, hpc, hE, toR_eq]

/-- One step of the repair scan on the ratio representation. -/
theorem entryR_toR (r j : ℕ) (a ell prev : Ratio) (g b : ℕ × ℕ) :
    entryR (true, r, (a.num, a.den), (ell.num, ell.den)) j (prev.num, prev.den) g b =
      let e := LinearRepair.sourceEntry r a ell j g b
      let cur := if j = 0 then e else Ratio.lesser prev e
      ((e.num, e.den), (cur.num, cur.den),
        ((Ratio.greater ell cur).num, (Ratio.greater ell cur).den)) := by
  have h1 := toR_lesser; have h2 := toR_greater; have h3 := toR_counts
  simp only [LinearRepairFL.toR] at h1 h2 h3
  simp only [entryR, LinearRepair.sourceEntry]
  split_ifs <;> simp_all

theorem repair_correct (hpc : s.pc = .repair) : Agrees q r B m X ext s (repairF x) := by
  unfold Agrees
  rcases hg : s.repairGood with _ | ⟨g, gs⟩ <;> rcases hb : s.repairBad with _ | ⟨b, bs⟩
  · simp [ctl_simp, tm_simp, hpc, hg, hb]
  · simp [ctl_simp, tm_simp, hpc, hg, hb]
  · simp [ctl_simp, tm_simp, hpc, hg, hb]
  · simp only [ctl_simp, tm_simp, hpc, hg, hb, Option.map_some, entryF_den, ctrF_den, mdF_den,
      succF_den, toR_eq, LinearRepairFL.toR]
    rw [entryR_toR]
    simp [ctrR, toR_eq, LinearRepairFL.toR]

theorem prefix_correct (hpc : s.pc = .prefix) : Agrees q r B m X ext s (prefixPF x) := by
  unfold Agrees
  rcases hp : s.prefixState with ⟨ctl, stack⟩
  cases ctl with
  | enter d pre cap => by_cases hc : cap = 0 <;> simp [ctl_simp, tm_simp, hpc, hp, hc]
  | await d pre cap => simp [ctl_simp, tm_simp, encKey, hpc, hp]
  | ret count =>
    rcases stack with _ | ⟨fr, rest⟩
    · simp [ctl_simp, tm_simp, hpc, hp]
    · cases fr <;> simp [ctl_simp, tm_simp, hpc, hp]

theorem resume_correct (hpc : s.pc = .resume) : Agrees q r B m X ext s (resumeF x) := by
  unfold Agrees
  rcases ht : s.returnTag with _ | _
  · simp [ctl_simp, tm_simp, hpc, ht]
  · rcases hp : s.prefixState with ⟨ctl, stack⟩
    cases ctl with
    | enter d pre cap => by_cases hc : cap = 0 <;> simp [ctl_simp, tm_simp, hpc, ht, hp, hc]
    | await d pre cap =>
      cases hr : s.reply <;> cases d <;> simp [ctl_simp, tm_simp, hpc, ht, hp, hr]
    | ret count =>
      rcases stack with _ | ⟨fr, rest⟩
      · simp [ctl_simp, tm_simp, hpc, ht, hp]
      · cases fr <;> simp [ctl_simp, tm_simp, hpc, ht, hp]

end Phases

section Main
variable (x : Ix TX) (q r B m : ℕ) (X : TX.den) (ext : External) (s : Config)

/-- The external parameters agree with `ext` at the arguments a phase of `s` may use. -/
structure ExtAgrees : Prop where
  query : x.compile.den (X, encKey s.request) = (ext.compileQuery s.request).bits
  endpoint : ∀ b, x.endpoint.den (X, b) = toR (ext.endpoint b).value

theorem dispatch_correct (hpc : s.pc ≠ .invoke) (hd : s.pc ≠ .done) (hf : s.pc ≠ .fault)
    (he : ExtAgrees x X ext s) : Agrees q r B m X ext s (dispatchF x) := by
  have hd' : ∀ G : FnSig (TArg TX) TCfg, (dispatchF x).den (encCtx q r B m X, encCfg s) =
      G.den (encCtx q r B m X, encCfg s) → Agrees q r B m X ext s G →
      Agrees q r B m X ext s (dispatchF x) := fun G e h => by unfold Agrees at *; rw [e]; exact h
  cases hp : s.pc
  all_goals try (exfalso; simp_all; done)
  case fetch => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (fetch_correct x q r B m X ext s hp)
  case «prefix» => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (prefix_correct x q r B m X ext s hp)
  case compile => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (compile_correct x q r B m X ext s hp he.query)
  case resume => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (resume_correct x q r B m X ext s hp)
  case reverseCells => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (reverseCells_correct x q r B m X ext s hp)
  case selectScan => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (selectScan_correct x q r B m X ext s hp)
  case trialCommit => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (trialCommit_correct x q r B m X ext s hp)
  case sortNext => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (sortNext_correct x q r B m X ext s hp)
  case insertScan => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (insertScan_correct x q r B m X ext s hp)
  case insertRestore => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (insertRestore_correct x q r B m X ext s hp)
  case medianLookup => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (medianLookup_correct x q r B m X ext s hp)
  case reverseGood => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (reverseGood_correct x q r B m X ext s hp)
  case reverseBad => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (reverseBad_correct x q r B m X ext s hp)
  case endpointZero => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (endpointZero_correct x q r B m X ext s hp (he.endpoint false))
  case endpointOne => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (endpointOne_correct x q r B m X ext s hp (he.endpoint true))
  case repair => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (repair_correct x q r B m X ext s hp)
  case reverseOutput => exact hd' _ (by simp [dispatchF, bodySig_den, dispatchBody, tm_simp, encCfg, encCtx, hp, pcCode]) (reverseOutput_correct x q r B m X ext s hp)

theorem step_none_iff (shape : Bool) :
    WholeWrapperCandidate.step q r B m shape ext s = none ↔ s.pc = .done ∨ s.pc = .fault := by
  cases hp : s.pc <;> simp [WholeWrapperCandidate.step, hp, localEdge]
  all_goals (try (repeat' split) <;> simp)

/-- **One FL call of `stepF` is one controller edge** (every program counter except `.invoke`;
`.done`/`.fault` have no edge). -/
theorem step_correct (hpc : s.pc ≠ .invoke) (he : ExtAgrees x X ext s) (e : Edge)
    (hs : WholeWrapperCandidate.step q r B m true ext s = some e) :
    (stepF x).den (encCtx q r B m X, encCfg s) = (encCtx q r B m X, encCfg e.next) := by
  have hn : ¬ (s.pc = .done ∨ s.pc = .fault) := fun h' => by
    rw [← step_none_iff] at h'; rw [h'] at hs; cases hs
  have hD := dispatch_correct x q r B m X ext s hpc (fun h' => hn (.inl h')) (fun h' => hn (.inr h')) he
  unfold Agrees at hD
  rw [hs, Option.map_some, Option.some.injEq] at hD
  simp only [stepF, bodySig_den, stepBody, tm_simp]
  rw [← hD]

theorem isDone_correct :
    (isDoneF x).den (encCtx q r B m X, encCfg s) = true ↔
      WholeWrapperCandidate.step q r B m true ext s = none := by
  rw [step_none_iff q r B m ext s true]
  cases hp : s.pc <;> simp [isDoneF, bodySig_den, isDoneBody, tm_simp, encCfg, hp, pcCode]

theorem isInvoke_correct :
    (isInvokeF x).den (encCtx q r B m X, encCfg s) = decide (s.pc = .invoke) := by
  cases hp : s.pc <;> simp [isInvokeF, bodySig_den, isInvokeBody, tm_simp, encCfg, hp, pcCode]

theorem queryOf_correct : (queryOfF x).den (encCtx q r B m X, encCfg s) = s.query := rfl

/-- The `.invoke` edge: its successor is `{s with pc := .resume, reply := answer}`, and
`answerSTF` computes that successor from the SAT answer bit. -/
theorem invoke_next (hpc : s.pc = .invoke) :
    (WholeWrapperCandidate.step q r B m true ext s).map Edge.next =
      some { s with pc := .resume, reply := (ext.sat s.query).value } := by
  simp [WholeWrapperCandidate.step, hpc]

theorem answer_correct (b : Bool) :
    (answerSTF x).den ((encCtx q r B m X, encCfg s), b) =
      (encCtx q r B m X, encCfg { s with pc := .resume, reply := b }) := rfl

end Main

end QecReliability.Trans.Control
