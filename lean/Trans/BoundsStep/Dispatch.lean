import Trans.BoundsStep.PhaseFetch
import Trans.BoundsStep.PhaseCall
import Trans.BoundsStep.PhasePrefix
import Trans.BoundsStep.PhaseRepair

/-!
# Trans.BoundsStep.Dispatch: `dispatchF` at a fixed program counter

`dispatch_K` (one small lemma per program counter `K`, never one 17-case theorem): at every
argument `a` with `a.2.1.1 = K` (the encoded program counter), `dispatchF` returns the phase's
result, and its cost/depth/msize exceed the phase's by at most `30000`/`40`/`200` (the `eqF`
tests of the dispatch chain on 5-bit numbers).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (TArg TCfg bodySig bodySig_cost bodySig_depth bodySig_msize
  bodySig_den)

private theorem dispatch_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem dispatch_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable {TX' : Ty} (x : Control.Ix TX')

theorem lits20 : ∀ k : ℕ, k < 20 → k.size ≤ 5 ∧ (Enc.nat k).size ≤ 21 :=
  fun k hk => lit_sz k (by omega)

/-- Simp set evaluating the dispatch chain at a literal program counter. -/
macro "disp_simp" : tactic => `(tactic| simp only [eqF_den, decide_eq_true_eq, decide_false,
  decide_true, Bool.false_eq_true, ↓reduceIte, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, ite_true,
  ite_false, if_true, if_false, Nat.succ_ne_zero, one_ne_zero, zero_ne_one])

set_option maxHeartbeats 1000000 in
theorem dispatch_0 (a : (TArg TX').den) (hpc : a.2.1.1 = 0) :
    (Control.dispatchF x).den a = (Control.fetchF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.fetchF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.fetchF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.fetchF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.fetchF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_1 (a : (TArg TX').den) (hpc : a.2.1.1 = 1) :
    (Control.dispatchF x).den a = (Control.prefixPF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.prefixPF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.prefixPF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.prefixPF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.prefixPF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_2 (a : (TArg TX').den) (hpc : a.2.1.1 = 2) :
    (Control.dispatchF x).den a = (Control.compilePF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.compilePF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.compilePF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.compilePF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.compilePF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_4 (a : (TArg TX').den) (hpc : a.2.1.1 = 4) :
    (Control.dispatchF x).den a = (Control.resumeF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.resumeF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.resumeF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.resumeF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.resumeF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_5 (a : (TArg TX').den) (hpc : a.2.1.1 = 5) :
    (Control.dispatchF x).den a = (Control.reverseCellsF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.reverseCellsF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.reverseCellsF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.reverseCellsF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.reverseCellsF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_6 (a : (TArg TX').den) (hpc : a.2.1.1 = 6) :
    (Control.dispatchF x).den a = (Control.selectScanF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.selectScanF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.selectScanF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.selectScanF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.selectScanF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_7 (a : (TArg TX').den) (hpc : a.2.1.1 = 7) :
    (Control.dispatchF x).den a = (Control.trialCommitF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.trialCommitF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.trialCommitF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.trialCommitF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.trialCommitF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_8 (a : (TArg TX').den) (hpc : a.2.1.1 = 8) :
    (Control.dispatchF x).den a = (Control.sortNextF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.sortNextF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.sortNextF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.sortNextF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.sortNextF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_9 (a : (TArg TX').den) (hpc : a.2.1.1 = 9) :
    (Control.dispatchF x).den a = (Control.insertScanF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.insertScanF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.insertScanF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.insertScanF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.insertScanF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_10 (a : (TArg TX').den) (hpc : a.2.1.1 = 10) :
    (Control.dispatchF x).den a = (Control.insertRestoreF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.insertRestoreF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.insertRestoreF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.insertRestoreF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega); have l10 := lits20 10 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.insertRestoreF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_11 (a : (TArg TX').den) (hpc : a.2.1.1 = 11) :
    (Control.dispatchF x).den a = (Control.medianLookupF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.medianLookupF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.medianLookupF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.medianLookupF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega); have l10 := lits20 10 (by omega); have l11 := lits20 11 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.medianLookupF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_12 (a : (TArg TX').den) (hpc : a.2.1.1 = 12) :
    (Control.dispatchF x).den a = (Control.reverseGoodF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.reverseGoodF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.reverseGoodF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.reverseGoodF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega); have l10 := lits20 10 (by omega); have l11 := lits20 11 (by omega); have l12 := lits20 12 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.reverseGoodF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_13 (a : (TArg TX').den) (hpc : a.2.1.1 = 13) :
    (Control.dispatchF x).den a = (Control.reverseBadF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.reverseBadF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.reverseBadF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.reverseBadF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega); have l10 := lits20 10 (by omega); have l11 := lits20 11 (by omega); have l12 := lits20 12 (by omega); have l13 := lits20 13 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.reverseBadF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_14 (a : (TArg TX').den) (hpc : a.2.1.1 = 14) :
    (Control.dispatchF x).den a = (Control.endpointZeroF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.endpointZeroF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.endpointZeroF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.endpointZeroF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega); have l10 := lits20 10 (by omega); have l11 := lits20 11 (by omega); have l12 := lits20 12 (by omega); have l13 := lits20 13 (by omega); have l14 := lits20 14 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.endpointZeroF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_15 (a : (TArg TX').den) (hpc : a.2.1.1 = 15) :
    (Control.dispatchF x).den a = (Control.endpointOneF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.endpointOneF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.endpointOneF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.endpointOneF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega); have l10 := lits20 10 (by omega); have l11 := lits20 11 (by omega); have l12 := lits20 12 (by omega); have l13 := lits20 13 (by omega); have l14 := lits20 14 (by omega); have l15 := lits20 15 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.endpointOneF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_16 (a : (TArg TX').den) (hpc : a.2.1.1 = 16) :
    (Control.dispatchF x).den a = (Control.repairF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.repairF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.repairF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.repairF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega); have l10 := lits20 10 (by omega); have l11 := lits20 11 (by omega); have l12 := lits20 12 (by omega); have l13 := lits20 13 (by omega); have l14 := lits20 14 (by omega); have l15 := lits20 15 (by omega); have l16 := lits20 16 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.repairF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

set_option maxHeartbeats 1000000 in
theorem dispatch_17 (a : (TArg TX').den) (hpc : a.2.1.1 = 17) :
    (Control.dispatchF x).den a = (Control.reverseOutputF x).den a ∧
      (Control.dispatchF x).cost a ≤ 30000 + (Control.reverseOutputF x).cost a ∧
      (Control.dispatchF x).depth a ≤ 40 + (Control.reverseOutputF x).depth a ∧
      (Control.dispatchF x).msize a ≤ 200 + (Control.reverseOutputF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega); have l10 := lits20 10 (by omega); have l11 := lits20 11 (by omega); have l12 := lits20 12 (by omega); have l13 := lits20 13 (by omega); have l14 := lits20 14 (by omega); have l15 := lits20 15 (by omega); have l16 := lits20 16 (by omega); have l17 := lits20 17 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [Control.dispatchF, bodySig_den, Control.dispatchBody, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [Control.dispatchF, bodySig_cost, Control.dispatchBody, Tm.cost, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (Control.dispatchBody x).depth (Env.one a) ≤ 39 + (Control.reverseOutputF x).depth a by
      simp only [Control.dispatchF, bodySig_depth]; omega
    dsimp only [Control.dispatchBody, Tm.depth, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [Control.dispatchF, bodySig_msize, Control.dispatchBody, Tm.msize, Tm.den, Env.one, dispatch_get_zero, dispatch_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega

end QecReliability.Trans.BoundsStep
