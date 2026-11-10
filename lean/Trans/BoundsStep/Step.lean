import Trans.BoundsStep.Dispatch

/-!
# Trans.BoundsStep.Step: closed form of one controller step (`stepF`)

With `S = (Ty.enc (TArg TX') a).size` and the callee terms at `X = a.1.2`,
`request = a.2.2.1.1` (`CC`/`CD`/`CM`: `x.compile` at `(X, request)` plus `x.endpoint` at
`(X, false)` and `(X, true)`), **`StepB x a`** says

* `stepF.cost a ≤ 5000000 (S+1)² + CC x a`,
* `stepF.depth a ≤ 2000 (S+1) + CD x a`,
* `stepF.msize a ≤ 2·size(stepF.den a) + 20000 (S+1) + CM x a`.

`step_at_K`: `StepB x a` whenever the encoded program counter is `K` (17 small lemmas);
**`step_bounds`**: `StepB x (c, encCfg s)` for every configuration with
`s.pc ∉ {invoke, done, fault}` (the only program counters with a `step` edge).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (TArg TCtx TCfg encCfg pcCode bodySig bodySig_cost bodySig_depth
  bodySig_msize bodySig_den)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate

private theorem step_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem step_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable {TX' : Ty} (x : Control.Ix TX')

/-- Callee cost at the arguments a step may use. -/
def CC (a : (TArg TX').den) : ℕ :=
  x.compile.cost (a.1.2, a.2.2.1.1) + x.endpoint.cost (a.1.2, false) + x.endpoint.cost (a.1.2, true)
/-- Callee depth. -/
def CD (a : (TArg TX').den) : ℕ :=
  x.compile.depth (a.1.2, a.2.2.1.1) + x.endpoint.depth (a.1.2, false) +
    x.endpoint.depth (a.1.2, true)
/-- Callee size budget. -/
def CM (a : (TArg TX').den) : ℕ :=
  x.compile.msize (a.1.2, a.2.2.1.1) + x.endpoint.msize (a.1.2, false) +
    x.endpoint.msize (a.1.2, true)

/-- The closed-form bound of one step at `a`. -/
def StepB (a : (TArg TX').den) : Prop :=
  (Control.stepF x).cost a ≤ 5000000 * ((Ty.enc (TArg TX') a).size + 1) ^ 2 + CC x a ∧
    (Control.stepF x).depth a ≤ 2000 * ((Ty.enc (TArg TX') a).size + 1) + CD x a ∧
    (Control.stepF x).msize a ≤ 2 * (Ty.enc (TArg TX') ((Control.stepF x).den a)).size +
      20000 * ((Ty.enc (TArg TX') a).size + 1) + CM x a

theorem stepF_den (a : (TArg TX').den) :
    (Control.stepF x).den a = (a.1, (Control.dispatchF x).den a) := rfl

/-- Combining the dispatch overhead with a phase bound. -/
theorem step_of (a : (TArg TX').den) (F : FnSig (TArg TX') TCfg)
    (hden : (Control.dispatchF x).den a = F.den a)
    (hcost : (Control.dispatchF x).cost a ≤ 30000 + F.cost a)
    (hdep : (Control.dispatchF x).depth a ≤ 40 + F.depth a)
    (hms : (Control.dispatchF x).msize a ≤ 200 + F.msize a)
    (fc : F.cost a ≤ 4000000 * ((Ty.enc (TArg TX') a).size + 1) ^ 2 + CC x a)
    (fd : F.depth a ≤ 1000 * ((Ty.enc (TArg TX') a).size + 1) + CD x a)
    (fm : F.msize a ≤ (Ty.enc TCfg (F.den a)).size + 11000 * ((Ty.enc (TArg TX') a).size + 1) +
      CM x a) : StepB x a := by
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hsz : (Ty.enc (TArg TX') ((Control.stepF x).den a)).size =
      (Ty.enc (TCtx TX') a.1).size + (Ty.enc TCfg ((Control.dispatchF x).den a)).size + 1 := by
    rw [stepF_den, Trans.Bounds.shape2]
  rw [hden] at hsz
  refine ⟨?_, ?_, ?_⟩
  · show (Control.stepBody x).cost (Env.one a) + 2 ≤ _
    dsimp only [Control.stepBody, Tm.cost, Tm.den, Env.one, step_get_zero, step_get_succ]
    omega
  · show (Control.stepBody x).depth (Env.one a) + 1 ≤ _
    dsimp only [Control.stepBody, Tm.depth, Tm.den, Env.one, step_get_zero, step_get_succ]
    simp only [max_self, Nat.zero_max, Nat.max_zero]
    omega
  · show (Control.stepBody x).msize (Env.one a) ≤ _
    dsimp only [Control.stepBody, Tm.msize, Tm.den, Env.one, step_get_zero, step_get_succ]
    simp only [max_self, Nat.zero_max, Nat.max_zero, max_le_iff]
    constructor
    · omega
    · show (Ty.enc (TArg TX') (a.1, (Control.dispatchF x).den a)).size ≤ _
      rw [← stepF_den]
      omega

theorem step_at_0 (a : (TArg TX').den) (hpc : a.2.1.1 = 0) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_0 x a hpc
  have c1 := fetch_cost x a
  have d1 := fetch_depth x a
  have e1 := fetch_ex x a
  have m1 : (Control.fetchF x).msize a ≤ (Ty.enc TCfg ((Control.fetchF x).den a)).size +
      Control.Tm'.ex (Control.fetchBody x) (Env.one a) :=
    Control.bodySig_msize_le x.fetch (Control.fetchBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.fetchF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_1 (a : (TArg TX').den) (hpc : a.2.1.1 = 1) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_1 x a hpc
  have c1 := prefixP_cost x a
  have d1 := prefixP_depth x a
  have e1 := prefixP_ex x a
  have m1 : (Control.prefixPF x).msize a ≤ (Ty.enc TCfg ((Control.prefixPF x).den a)).size +
      Control.Tm'.ex (Control.prefixPBody x) (Env.one a) :=
    Control.bodySig_msize_le x.prefixP (Control.prefixPBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.prefixPF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_2 (a : (TArg TX').den) (hpc : a.2.1.1 = 2) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_2 x a hpc
  have c1 := compileP_cost x a
  have d1 := compileP_depth x a
  have e1 := compileP_ex x a
  have m1 : (Control.compilePF x).msize a ≤ (Ty.enc TCfg ((Control.compilePF x).den a)).size +
      Control.Tm'.ex (Control.compilePBody x) (Env.one a) :=
    Control.bodySig_msize_le x.compileP (Control.compilePBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hC : CC x a = x.compile.cost (a.1.2, a.2.2.1.1) + x.endpoint.cost (a.1.2, false) +
      x.endpoint.cost (a.1.2, true) := rfl
  have hD : CD x a = x.compile.depth (a.1.2, a.2.2.1.1) + x.endpoint.depth (a.1.2, false) +
      x.endpoint.depth (a.1.2, true) := rfl
  have hM : CM x a = x.compile.msize (a.1.2, a.2.2.1.1) + x.endpoint.msize (a.1.2, false) +
      x.endpoint.msize (a.1.2, true) := rfl
  refine step_of x a (Control.compilePF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_4 (a : (TArg TX').den) (hpc : a.2.1.1 = 4) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_4 x a hpc
  have c1 := resume_cost x a
  have d1 := resume_depth x a
  have e1 := resume_ex x a
  have m1 : (Control.resumeF x).msize a ≤ (Ty.enc TCfg ((Control.resumeF x).den a)).size +
      Control.Tm'.ex (Control.resumeBody x) (Env.one a) :=
    Control.bodySig_msize_le x.resume (Control.resumeBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.resumeF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_5 (a : (TArg TX').den) (hpc : a.2.1.1 = 5) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_5 x a hpc
  have c1 := reverseCells_cost x a
  have d1 := reverseCells_depth x a
  have e1 := reverseCells_ex (TX' := TX') a
  have m1 : (Control.reverseCellsF x).msize a ≤ (Ty.enc TCfg ((Control.reverseCellsF x).den a)).size +
      Control.Tm'.ex (Control.reverseCellsBody (TX := TX')) (Env.one a) :=
    Control.bodySig_msize_le x.reverseCells (Control.reverseCellsBody (TX := TX')) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.reverseCellsF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_6 (a : (TArg TX').den) (hpc : a.2.1.1 = 6) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_6 x a hpc
  have c1 := selectScan_cost x a
  have d1 := selectScan_depth x a
  have e1 := selectScan_ex x a
  have m1 : (Control.selectScanF x).msize a ≤ (Ty.enc TCfg ((Control.selectScanF x).den a)).size +
      Control.Tm'.ex (Control.selectScanBody x) (Env.one a) :=
    Control.bodySig_msize_le x.selectScan (Control.selectScanBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.selectScanF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_7 (a : (TArg TX').den) (hpc : a.2.1.1 = 7) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_7 x a hpc
  have c1 := trialCommit_cost x a
  have d1 := trialCommit_depth x a
  have e1 := trialCommit_ex x a
  have m1 : (Control.trialCommitF x).msize a ≤ (Ty.enc TCfg ((Control.trialCommitF x).den a)).size +
      Control.Tm'.ex (Control.trialCommitBody x) (Env.one a) :=
    Control.bodySig_msize_le x.trialCommit (Control.trialCommitBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.trialCommitF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_8 (a : (TArg TX').den) (hpc : a.2.1.1 = 8) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_8 x a hpc
  have c1 := sortNext_cost x a
  have d1 := sortNext_depth x a
  have e1 := sortNext_ex (TX' := TX') a
  have m1 : (Control.sortNextF x).msize a ≤ (Ty.enc TCfg ((Control.sortNextF x).den a)).size +
      Control.Tm'.ex (Control.sortNextBody (TX := TX')) (Env.one a) :=
    Control.bodySig_msize_le x.sortNext (Control.sortNextBody (TX := TX')) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.sortNextF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_9 (a : (TArg TX').den) (hpc : a.2.1.1 = 9) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_9 x a hpc
  have c1 := insertScan_cost x a
  have d1 := insertScan_depth x a
  have e1 := insertScan_ex x a
  have m1 : (Control.insertScanF x).msize a ≤ (Ty.enc TCfg ((Control.insertScanF x).den a)).size +
      Control.Tm'.ex (Control.insertScanBody x) (Env.one a) :=
    Control.bodySig_msize_le x.insertScan (Control.insertScanBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.insertScanF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_10 (a : (TArg TX').den) (hpc : a.2.1.1 = 10) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_10 x a hpc
  have c1 := insertRestore_cost x a
  have d1 := insertRestore_depth x a
  have e1 := insertRestore_ex (TX' := TX') a
  have m1 : (Control.insertRestoreF x).msize a ≤ (Ty.enc TCfg ((Control.insertRestoreF x).den a)).size +
      Control.Tm'.ex (Control.insertRestoreBody (TX := TX')) (Env.one a) :=
    Control.bodySig_msize_le x.insertRestore (Control.insertRestoreBody (TX := TX')) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.insertRestoreF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_11 (a : (TArg TX').den) (hpc : a.2.1.1 = 11) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_11 x a hpc
  have c1 := medianLookup_cost x a
  have d1 := medianLookup_depth x a
  have e1 := medianLookup_ex x a
  have m1 : (Control.medianLookupF x).msize a ≤ (Ty.enc TCfg ((Control.medianLookupF x).den a)).size +
      Control.Tm'.ex (Control.medianLookupBody x) (Env.one a) :=
    Control.bodySig_msize_le x.medianLookup (Control.medianLookupBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.medianLookupF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_12 (a : (TArg TX').den) (hpc : a.2.1.1 = 12) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_12 x a hpc
  have c1 := reverseGood_cost x a
  have d1 := reverseGood_depth x a
  have e1 := reverseGood_ex (TX' := TX') a
  have m1 : (Control.reverseGoodF x).msize a ≤ (Ty.enc TCfg ((Control.reverseGoodF x).den a)).size +
      Control.Tm'.ex (Control.reverseGoodBody (TX := TX')) (Env.one a) :=
    Control.bodySig_msize_le x.reverseGood (Control.reverseGoodBody (TX := TX')) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.reverseGoodF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_13 (a : (TArg TX').den) (hpc : a.2.1.1 = 13) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_13 x a hpc
  have c1 := reverseBad_cost x a
  have d1 := reverseBad_depth x a
  have e1 := reverseBad_ex (TX' := TX') a
  have m1 : (Control.reverseBadF x).msize a ≤ (Ty.enc TCfg ((Control.reverseBadF x).den a)).size +
      Control.Tm'.ex (Control.reverseBadBody (TX := TX')) (Env.one a) :=
    Control.bodySig_msize_le x.reverseBad (Control.reverseBadBody (TX := TX')) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.reverseBadF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_14 (a : (TArg TX').den) (hpc : a.2.1.1 = 14) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_14 x a hpc
  have c1 := endpointZero_cost x a
  have d1 := endpointZero_depth x a
  have e1 := endpointZero_ex x a
  have m1 : (Control.endpointZeroF x).msize a ≤ (Ty.enc TCfg ((Control.endpointZeroF x).den a)).size +
      Control.Tm'.ex (Control.endpointZeroBody x) (Env.one a) :=
    Control.bodySig_msize_le x.endpointZero (Control.endpointZeroBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hC : CC x a = x.compile.cost (a.1.2, a.2.2.1.1) + x.endpoint.cost (a.1.2, false) +
      x.endpoint.cost (a.1.2, true) := rfl
  have hD : CD x a = x.compile.depth (a.1.2, a.2.2.1.1) + x.endpoint.depth (a.1.2, false) +
      x.endpoint.depth (a.1.2, true) := rfl
  have hM : CM x a = x.compile.msize (a.1.2, a.2.2.1.1) + x.endpoint.msize (a.1.2, false) +
      x.endpoint.msize (a.1.2, true) := rfl
  refine step_of x a (Control.endpointZeroF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_15 (a : (TArg TX').den) (hpc : a.2.1.1 = 15) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_15 x a hpc
  have c1 := endpointOne_cost x a
  have d1 := endpointOne_depth x a
  have e1 := endpointOne_ex x a
  have m1 : (Control.endpointOneF x).msize a ≤ (Ty.enc TCfg ((Control.endpointOneF x).den a)).size +
      Control.Tm'.ex (Control.endpointOneBody x) (Env.one a) :=
    Control.bodySig_msize_le x.endpointOne (Control.endpointOneBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hC : CC x a = x.compile.cost (a.1.2, a.2.2.1.1) + x.endpoint.cost (a.1.2, false) +
      x.endpoint.cost (a.1.2, true) := rfl
  have hD : CD x a = x.compile.depth (a.1.2, a.2.2.1.1) + x.endpoint.depth (a.1.2, false) +
      x.endpoint.depth (a.1.2, true) := rfl
  have hM : CM x a = x.compile.msize (a.1.2, a.2.2.1.1) + x.endpoint.msize (a.1.2, false) +
      x.endpoint.msize (a.1.2, true) := rfl
  refine step_of x a (Control.endpointOneF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_16 (a : (TArg TX').den) (hpc : a.2.1.1 = 16) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_16 x a hpc
  have c1 := repair_cost x a
  have d1 := repair_depth x a
  have e1 := repair_ex x a
  have m1 : (Control.repairF x).msize a ≤ (Ty.enc TCfg ((Control.repairF x).den a)).size +
      Control.Tm'.ex (Control.repairBody x) (Env.one a) :=
    Control.bodySig_msize_le x.repair (Control.repairBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.repairF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

theorem step_at_17 (a : (TArg TX').den) (hpc : a.2.1.1 = 17) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_17 x a hpc
  have c1 := reverseOutput_cost x a
  have d1 := reverseOutput_depth x a
  have e1 := reverseOutput_ex (TX' := TX') a
  have m1 : (Control.reverseOutputF x).msize a ≤ (Ty.enc TCfg ((Control.reverseOutputF x).den a)).size +
      Control.Tm'.ex (Control.reverseOutputBody (TX := TX')) (Env.one a) :=
    Control.bodySig_msize_le x.reverseOutput (Control.reverseOutputBody (TX := TX')) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (Control.reverseOutputF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega

/-- **One controller step, closed form**: at every configuration with a `step` edge. -/
theorem step_bounds (c : (TCtx TX').den) (s : Config) (h1 : s.pc ≠ .invoke) (h2 : s.pc ≠ .done)
    (h3 : s.pc ≠ .fault) : StepB x (c, encCfg s) := by
  have hp : (c, encCfg s).2.1.1 = pcCode s.pc := rfl
  cases hs : s.pc with
  | fetch => exact step_at_0 x _ (by rw [hp, hs]; rfl)
  | «prefix» => exact step_at_1 x _ (by rw [hp, hs]; rfl)
  | compile => exact step_at_2 x _ (by rw [hp, hs]; rfl)
  | resume => exact step_at_4 x _ (by rw [hp, hs]; rfl)
  | reverseCells => exact step_at_5 x _ (by rw [hp, hs]; rfl)
  | selectScan => exact step_at_6 x _ (by rw [hp, hs]; rfl)
  | trialCommit => exact step_at_7 x _ (by rw [hp, hs]; rfl)
  | sortNext => exact step_at_8 x _ (by rw [hp, hs]; rfl)
  | insertScan => exact step_at_9 x _ (by rw [hp, hs]; rfl)
  | insertRestore => exact step_at_10 x _ (by rw [hp, hs]; rfl)
  | medianLookup => exact step_at_11 x _ (by rw [hp, hs]; rfl)
  | reverseGood => exact step_at_12 x _ (by rw [hp, hs]; rfl)
  | reverseBad => exact step_at_13 x _ (by rw [hp, hs]; rfl)
  | endpointZero => exact step_at_14 x _ (by rw [hp, hs]; rfl)
  | endpointOne => exact step_at_15 x _ (by rw [hp, hs]; rfl)
  | repair => exact step_at_16 x _ (by rw [hp, hs]; rfl)
  | reverseOutput => exact step_at_17 x _ (by rw [hp, hs]; rfl)
  | invoke => exact absurd hs h1
  | done => exact absurd hs h2
  | fault => exact absurd hs h3

end QecReliability.Trans.BoundsStep
