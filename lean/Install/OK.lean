import Install.OKHash

/-!
# Install.OK: every installation record of the program `prog …`

Given the hash program's validity (`Install.OKHash.hash_ok`, which needs the oracle meanings),
this file discharges the installation records of every package for the concrete index table:

* `Trans.Control`: `LibI yI`, `LibR yR`, `LibOK _ cX`, `PhasesOK _ cX`, and validity of
  `stepF`, `isDoneF`, `isInvokeF`, `queryOfF`, `answerSTF` at every argument;
* `Trans.Wire`: `WIx.OK` (`wL wH wP wA wC`), `initTopF` and the compile/endpoint wrappers;
* `Trans.Bounds`: `OIx.OK oX`, `outputF`, `resumeTopF`.
-/

set_option autoImplicit false

namespace QecReliability.Install
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Query.Plain (ProgP)

section
variable {base den density : ℕ} {E : ℕ × ℕ × ℕ} {pg : ℕ → ProgP} {nb : ℕ → ℕ → ℕ → ℕ}

local notation "PP" => prog base den density E pg nb
local notation "CX" => cX base den density E pg nb

/-! ## Control: initial configuration and endpoints -/

theorem yI_ok : Trans.Control.LibI yI PP := by
  have S := std_ok base den density E pg nb
  exact ⟨S.succ, S.range, S.append _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

theorem yR_ok : Trans.Control.LibR yR PP := by
  have S := std_ok base den density E pg nb
  exact ⟨S.succ, S.add, S.sub, S.eq, S.range, S.length _, S.getD _, S.replicate _, S.append _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Wire -/

theorem wH_ok : wH.OK wL PP := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem wP_ok : wP.OK wL wH PP := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem wA_ok : wA.OK wL wH wP yI paramsFn base den PP := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem wC_ok : wC.OK wL queryFn (hashFn E pg nb) base den density yR PP :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem wW_ok : wW.OK PP yI paramsFn queryFn (hashFn E pg nb) base den density yR :=
  ⟨wL_ok base den density E pg nb, wH_ok, wP_ok, wA_ok, wC_ok⟩

/-- **The init function** is valid at every argument. -/
theorem init_ok : ∀ x, (Trans.Wire.initTopF wL wH wP wA yI paramsFn base den).ValidAt PP x :=
  wW_ok.initTop_valid params_ok yI_ok

theorem endpoint_ok : ∀ x, endpointFn.ValidAt PP x :=
  wW_ok.endpointW_valid yR_ok

theorem compile_ok (hH : ∀ x, (hashFn E pg nb).ValidAt PP x) : ∀ x, (compileFn base den density E pg nb).ValidAt PP x :=
  wW_ok.compile_valid (query_valid base den density E pg nb) hH

/-! ## Control: the controller step -/

theorem cX_lib (hH : ∀ x, (hashFn E pg nb).ValidAt PP x) : Trans.Control.LibOK PP CX := by
  have S := std_ok base den density E pg nb
  have hcounts := LinearRepairFL.counts_valid (P := PP) (i := iCounts) S.add rfl
  have hles := LinearRepairFL.lesser_valid (P := PP) (i := iLesser) S.mul S.le rfl
  have hgrt := LinearRepairFL.greater_valid (P := PP) (i := iGreater) S.mul S.le rfl
  exact
    { compile := compile_ok hH
      endpoint := endpoint_ok
      succ := S.succ, pred := S.pred, add := S.add, le := S.le, eq := S.eq, max := S.max,
      mul := S.mul, sub := S.sub, append := S.append _
      mapFst := Trans.Control.mapFst_valid rfl rfl
      entry := LinearRepairFL.entry_valid S.eq hcounts hles hgrt rfl
      ctr := LinearRepairFL.ctr_valid S.succ S.eq rfl
      md := LinearRepairFL.md_valid S.max rfl }

theorem cX_phases (hH : ∀ x, (hashFn E pg nb).ValidAt PP x) :
    Trans.Control.PhasesOK PP CX := by
  have h := cX_lib hH
  have hps := Trans.Control.pstep_valid h rfl
  exact
    { fetch := Trans.Control.fetch_valid h (Trans.Control.fop_valid h rfl rfl rfl rfl rfl rfl rfl)
        rfl
      prefixP := Trans.Control.prefixP_valid h hps rfl
      compileP := Trans.Control.compileP_valid h rfl
      resume := Trans.Control.resume_valid h hps rfl
      reverseCells := Trans.Control.reverseCells_valid h rfl
      selectScan := Trans.Control.selectScan_valid h rfl
      trialCommit := Trans.Control.trialCommit_valid h rfl
      sortNext := Trans.Control.sortNext_valid h rfl
      insertScan := Trans.Control.insertScan_valid h rfl
      insertRestore := Trans.Control.insertRestore_valid h rfl
      medianLookup := Trans.Control.medianLookup_valid h rfl
      reverseGood := Trans.Control.reverseGood_valid h rfl
      reverseBad := Trans.Control.reverseBad_valid h rfl
      endpointZero := Trans.Control.endpointZero_valid h rfl
      endpointOne := Trans.Control.endpointOne_valid h rfl
      repair := Trans.Control.repair_valid h (Trans.Control.repairAcc_valid h rfl) rfl
      reverseOutput := Trans.Control.reverseOutput_valid h rfl }

/-- **The step function** is valid at every argument. -/
theorem step_ok (hH : ∀ x, (hashFn E pg nb).ValidAt PP x) : ∀ a, (Trans.Control.stepF CX).ValidAt PP a := by
  have hd := Trans.Control.dispatch_valid (cX_lib hH) (cX_phases hH) rfl
  intro a
  apply Trans.Control.bodySig_valid rfl
  simp [tm_simp, Trans.Control.stepBody, hd]

theorem answerST_ok (hH : ∀ x, (hashFn E pg nb).ValidAt PP x) : ∀ a, (Trans.Control.answerSTF CX).ValidAt PP a :=
  Trans.Bounds.answerST_valid (Trans.Control.answer_valid (cX_lib hH) rfl) rfl

theorem isDone_ok : ∀ a, (Trans.Control.isDoneF CX).ValidAt PP a := by
  have heq : ∀ y, (eqF (CX).eq).ValidAt PP y := (std_ok base den density E pg nb).eq
  intro a
  apply Trans.Control.bodySig_valid rfl
  simp [tm_simp, Trans.Control.isDoneBody, Trans.Control.Tm.eqLit, heq]

theorem isInvoke_ok : ∀ a, (Trans.Control.isInvokeF CX).ValidAt PP a := by
  have heq : ∀ y, (eqF (CX).eq).ValidAt PP y := (std_ok base den density E pg nb).eq
  intro a
  apply Trans.Control.bodySig_valid rfl
  simp [tm_simp, Trans.Control.isInvokeBody, Trans.Control.Tm.eqLit, heq]

theorem queryOf_ok : ∀ a, (Trans.Control.queryOfF CX).ValidAt PP a := by
  intro a
  apply Trans.Control.bodySig_valid rfl
  simp [tm_simp, Trans.Control.queryOfBody]

/-! ## Output and resume -/

theorem oX_ok : oX.OK PP Trans.Wire.TX CX := by
  have S := std_ok base den density E pg nb
  exact ⟨S.pred, S.bitLen, S.replicate _, S.append _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The output function** is valid at every argument. -/
theorem output_ok : ∀ a, (Trans.Bounds.outputF oX Trans.Wire.TX).ValidAt PP a :=
  oX_ok.output_valid

/-- **The resume function** is valid at every argument. -/
theorem resumeTop_ok (hH : ∀ x, (hashFn E pg nb).ValidAt PP x) :
    ∀ a, (Trans.Bounds.resumeTopF oX CX).ValidAt PP a :=
  oX_ok.resumeTop_valid (answerST_ok hH)

end

end QecReliability.Install
