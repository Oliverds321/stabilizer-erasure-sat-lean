import LatentEndpointRepairFL

/-! Fixed endpoint-mode dispatch and step bodies. Every non-repair phase is
reused; the repair branch calls the false-mode signature, never the pinned
true-mode repairF. The agreement theorem targets step ... false explicitly. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.EndpointControllerFL
open FL FL.Lib FL.Tm Trans.Control Trans.Control.Tm
open OracleCost OracleCost.WholeWrapperCandidate
variable {TX : Ty}

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

section Valid
variable {P : FL.Program} {x : Ix TX} (h : LibOK P x) (hp : PhasesOK P x)
include h hp
theorem dispatch_valid (hP : P[x.dispatch]? = some (dispatchBody x).compile) :
    ∀ a, (dispatchF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp only [tm_simp, dispatchBody]
  simp [h.eq, hp.fetch, hp.prefixP, hp.compileP, hp.resume, hp.reverseCells, hp.selectScan,
    hp.trialCommit, hp.sortNext, hp.insertScan, hp.insertRestore, hp.medianLookup, hp.reverseGood,
    hp.reverseBad, hp.endpointZero, hp.endpointOne, hp.repair, hp.reverseOutput]

end Valid

def stepBody (x : Ix TX) : Tm [TArg TX] (TArg TX) :=
  .pair (.fst v0) (.app (dispatchF x) v0)
def stepF (x : Ix TX) : FnSig (TArg TX) (TArg TX) := bodySig x.step (stepBody x)

theorem step_valid {P : FL.Program} {x : Ix TX}
    (hd : ∀ a, (dispatchF x).ValidAt P a)
    (hi : P[x.step]? = some (stepBody x).compile) :
    ∀ a, (stepF x).ValidAt P a := fun a =>
  bodySig_valid hi (by simp [stepBody,tm_simp,hd])

theorem dispatch_den_nonrepair (x : Ix TX) (q r B m : ℕ) (X : TX.den) (s : Config)
    (h : s.pc ≠ .repair) :
    (dispatchF x).den (encCtx q r B m X,encCfg s) =
      (Trans.Control.dispatchF x).den (encCtx q r B m X,encCfg s) := by
  cases hp : s.pc <;> try { exact False.elim (h hp) }
  all_goals simp [dispatchF,dispatchBody,Trans.Control.dispatchF,Trans.Control.dispatchBody,
    bodySig_den,tm_simp,encCfg,encCtx,hp,pcCode]

theorem dispatch_correct (x : Ix TX) (q r B m : ℕ) (X : TX.den) (ext : External) (s : Config)
    (hn : s.pc ≠ .invoke) (hd : s.pc ≠ .done) (hf : s.pc ≠ .fault)
    (he : ExtAgrees x X ext s) :
    (WholeWrapperCandidate.step q r B m false ext s).map (fun e => encCfg e.next) =
      some ((dispatchF x).den (encCtx q r B m X,encCfg s)) := by
  by_cases hr : s.pc = .repair
  · have h := repair_correct x q r B m X ext s hr
    simpa [dispatchF,bodySig_den,dispatchBody,tm_simp,encCfg,encCtx,hr,pcCode] using h
  · rw [step_mode_eq_of_not_repair q r B m ext s hr,dispatch_den_nonrepair x q r B m X s hr]
    exact Trans.Control.dispatch_correct x q r B m X ext s hn hd hf he

theorem step_correct (x : Ix TX) (q r B m : ℕ) (X : TX.den) (ext : External) (s : Config)
    (hn : s.pc ≠ .invoke) (he : ExtAgrees x X ext s) (e : Edge)
    (hs : WholeWrapperCandidate.step q r B m false ext s = some e) :
    (stepF x).den (encCtx q r B m X,encCfg s) = (encCtx q r B m X,encCfg e.next) := by
  have hnterm : ¬ (s.pc = .done ∨ s.pc = .fault) := fun h => by
    have hz := (Trans.Control.step_none_iff q r B m ext s false).mpr h
    rw [hz] at hs
    cases hs
  have h := dispatch_correct x q r B m X ext s hn
    (fun h => hnterm (.inl h)) (fun h => hnterm (.inr h)) he
  rw [hs,Option.map_some,Option.some.injEq] at h
  simp only [stepF,bodySig_den,stepBody,tm_simp]
  rw [← h]

theorem isDone_correct (x : Ix TX) (q r B m : ℕ) (X : TX.den) (ext : External) (s : Config) :
    (Trans.Control.isDoneF x).den (encCtx q r B m X,encCfg s) = true ↔
      WholeWrapperCandidate.step q r B m false ext s = none := by
  rw [Trans.Control.step_none_iff q r B m ext s false]
  rw [Trans.Control.isDone_correct x q r B m X ext s,
    Trans.Control.step_none_iff q r B m ext s true]

end QecReliability.LatentMachine.EndpointControllerFL

