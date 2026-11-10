import LatentEndpointRepairBounds
import LatentEndpointDispatchFL
import Trans.BoundsStep.Step

/-! Resource bounds for the actually installed endpoint-only controller.
Outside repair the old and new executions agree exactly, including every FL
resource measure. Only repair uses the separately proved false-mode bounds. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.EndpointControllerBounds
open FL FL.Lib FL.Tm Trans Trans.BoundsStep
open Trans.Control (TArg TCtx TCfg encCfg pcCode bodySig bodySig_cost bodySig_depth
  bodySig_msize bodySig_den)
open OracleCost OracleCost.WholeWrapperCandidate
private theorem endpointStep_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem endpointStep_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable {TX' : Ty} (x : Control.Ix TX')

theorem dispatch_nonrepair (a : (TArg TX').den) (h : a.2.1.1 ≠ 16) :
    (EndpointControllerFL.dispatchF x).den a = (Control.dispatchF x).den a ∧
    (EndpointControllerFL.dispatchF x).cost a = (Control.dispatchF x).cost a ∧
    (EndpointControllerFL.dispatchF x).depth a = (Control.dispatchF x).depth a ∧
    (EndpointControllerFL.dispatchF x).msize a = (Control.dispatchF x).msize a := by
  dsimp only [EndpointControllerFL.dispatchF,Control.dispatchF,bodySig_den,
    bodySig_cost,bodySig_depth,bodySig_msize,EndpointControllerFL.dispatchBody,
    Control.dispatchBody,Tm.den,Tm.cost,Tm.depth,Tm.msize,Env.one, endpointStep_get_zero, endpointStep_get_succ]
  simp only [eqF_den,h,decide_false,Bool.false_eq_true,if_false,and_self]

theorem step_nonrepair (a : (TArg TX').den) (h : a.2.1.1 ≠ 16) :
    (EndpointControllerFL.stepF x).den a = (Control.stepF x).den a ∧
    (EndpointControllerFL.stepF x).cost a = (Control.stepF x).cost a ∧
    (EndpointControllerFL.stepF x).depth a = (Control.stepF x).depth a ∧
    (EndpointControllerFL.stepF x).msize a = (Control.stepF x).msize a := by
  obtain ⟨hd,hc,hdep,hm⟩ := dispatch_nonrepair x a h
  dsimp only [EndpointControllerFL.stepF,Control.stepF,bodySig_den,
    bodySig_cost,bodySig_depth,bodySig_msize,EndpointControllerFL.stepBody,
    Control.stepBody,Tm.den,Tm.cost,Tm.depth,Tm.msize,Env.one, endpointStep_get_zero, endpointStep_get_succ]
  simp only [hd,hc,hdep,hm,and_self]

theorem dispatch_16 (a : (TArg TX').den) (hpc : a.2.1.1 = 16) :
    (EndpointControllerFL.dispatchF x).den a = (EndpointControllerFL.repairF x).den a ∧
      (EndpointControllerFL.dispatchF x).cost a ≤ 30000 + (EndpointControllerFL.repairF x).cost a ∧
      (EndpointControllerFL.dispatchF x).depth a ≤ 40 + (EndpointControllerFL.repairF x).depth a ∧
      (EndpointControllerFL.dispatchF x).msize a ≤ 200 + (EndpointControllerFL.repairF x).msize a := by
  have l0 := lits20 0 (by omega); have l1 := lits20 1 (by omega); have l2 := lits20 2 (by omega); have l3 := lits20 3 (by omega); have l4 := lits20 4 (by omega); have l5 := lits20 5 (by omega); have l6 := lits20 6 (by omega); have l7 := lits20 7 (by omega); have l8 := lits20 8 (by omega); have l9 := lits20 9 (by omega); have l10 := lits20 10 (by omega); have l11 := lits20 11 (by omega); have l12 := lits20 12 (by omega); have l13 := lits20 13 (by omega); have l14 := lits20 14 (by omega); have l15 := lits20 15 (by omega); have l16 := lits20 16 (by omega);
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [EndpointControllerFL.dispatchF, bodySig_den, EndpointControllerFL.dispatchBody, Tm.den, Env.one, endpointStep_get_zero, endpointStep_get_succ]
    simp only [hpc] <;> disp_simp
  · dsimp only [EndpointControllerFL.dispatchF, bodySig_cost, EndpointControllerFL.dispatchBody, Tm.cost, Tm.den, Env.one, endpointStep_get_zero, endpointStep_get_succ,
      eqF_cost, Ty.enc_nat]
    rw [hpc]
    disp_simp
    strip_mdata
    omega
  · suffices h : (EndpointControllerFL.dispatchBody x).depth (Env.one a) ≤ 39 + (EndpointControllerFL.repairF x).depth a by
      simp only [EndpointControllerFL.dispatchF, bodySig_depth]; omega
    dsimp only [EndpointControllerFL.dispatchBody, Tm.depth, Tm.den, Env.one, endpointStep_get_zero, endpointStep_get_succ, eqF_depth]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega
  · dsimp only [EndpointControllerFL.dispatchF, bodySig_msize, EndpointControllerFL.dispatchBody, Tm.msize, Tm.den, Env.one, endpointStep_get_zero, endpointStep_get_succ,
      eqF_msize, Ty.enc_prod, Ty.enc_nat, Val.size_cons]
    rw [hpc]
    disp_simp
    simp only [max_le_iff]
    strip_mdata
    (repeat' apply And.intro) <;> omega


def StepB (a : (TArg TX').den) : Prop :=
  (EndpointControllerFL.stepF x).cost a ≤ 5000000 * ((Ty.enc (TArg TX') a).size + 1) ^ 2 + CC x a ∧
    (EndpointControllerFL.stepF x).depth a ≤ 2000 * ((Ty.enc (TArg TX') a).size + 1) + CD x a ∧
    (EndpointControllerFL.stepF x).msize a ≤ 2 * (Ty.enc (TArg TX') ((EndpointControllerFL.stepF x).den a)).size +
      20000 * ((Ty.enc (TArg TX') a).size + 1) + CM x a

theorem stepF_den (a : (TArg TX').den) :
    (EndpointControllerFL.stepF x).den a = (a.1, (EndpointControllerFL.dispatchF x).den a) := rfl

/-- Combining the dispatch overhead with a phase bound. -/
theorem step_of (a : (TArg TX').den) (F : FnSig (TArg TX') TCfg)
    (hden : (EndpointControllerFL.dispatchF x).den a = F.den a)
    (hcost : (EndpointControllerFL.dispatchF x).cost a ≤ 30000 + F.cost a)
    (hdep : (EndpointControllerFL.dispatchF x).depth a ≤ 40 + F.depth a)
    (hms : (EndpointControllerFL.dispatchF x).msize a ≤ 200 + F.msize a)
    (fc : F.cost a ≤ 4000000 * ((Ty.enc (TArg TX') a).size + 1) ^ 2 + CC x a)
    (fd : F.depth a ≤ 1000 * ((Ty.enc (TArg TX') a).size + 1) + CD x a)
    (fm : F.msize a ≤ (Ty.enc TCfg (F.den a)).size + 11000 * ((Ty.enc (TArg TX') a).size + 1) +
      CM x a) : StepB x a := by
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hsz : (Ty.enc (TArg TX') ((EndpointControllerFL.stepF x).den a)).size =
      (Ty.enc (TCtx TX') a.1).size + (Ty.enc TCfg ((EndpointControllerFL.dispatchF x).den a)).size + 1 := by
    rw [stepF_den, Trans.Bounds.shape2]
  rw [hden] at hsz
  refine ⟨?_, ?_, ?_⟩
  · show (EndpointControllerFL.stepBody x).cost (Env.one a) + 2 ≤ _
    dsimp only [EndpointControllerFL.stepBody, Tm.cost, Tm.den, Env.one, endpointStep_get_zero, endpointStep_get_succ]
    omega
  · show (EndpointControllerFL.stepBody x).depth (Env.one a) + 1 ≤ _
    dsimp only [EndpointControllerFL.stepBody, Tm.depth, Tm.den, Env.one, endpointStep_get_zero, endpointStep_get_succ]
    simp only [max_self, Nat.zero_max, Nat.max_zero]
    omega
  · show (EndpointControllerFL.stepBody x).msize (Env.one a) ≤ _
    dsimp only [EndpointControllerFL.stepBody, Tm.msize, Tm.den, Env.one, endpointStep_get_zero, endpointStep_get_succ]
    simp only [max_self, Nat.zero_max, Nat.max_zero, max_le_iff]
    constructor
    · omega
    · show (Ty.enc (TArg TX') (a.1, (EndpointControllerFL.dispatchF x).den a)).size ≤ _
      rw [← stepF_den]
      omega


theorem step_at_16 (a : (TArg TX').den) (hpc : a.2.1.1 = 16) : StepB x a := by
  obtain ⟨hden, hcost, hdep, hms⟩ := dispatch_16 x a hpc
  have c1 := repair_cost x a
  have d1 := repair_depth x a
  have e1 := repair_ex x a
  have m1 : (EndpointControllerFL.repairF x).msize a ≤ (Ty.enc TCfg ((EndpointControllerFL.repairF x).den a)).size +
      Control.Tm'.ex (EndpointControllerFL.repairBody x) (Env.one a) :=
    Control.bodySig_msize_le x.repair (EndpointControllerFL.repairBody x) a
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  refine step_of x a (EndpointControllerFL.repairF x) hden hcost hdep hms ?_ ?_ ?_
  · omega
  · omega
  · omega


theorem step_bounds (c : (TCtx TX').den) (s : Config) (h1 : s.pc ≠ .invoke)
    (h2 : s.pc ≠ .done) (h3 : s.pc ≠ .fault) : StepB x (c,encCfg s) := by
  by_cases hr : s.pc = .repair
  · apply step_at_16 x
    change pcCode s.pc = 16
    rw [hr]
    rfl
  · have hn : (c,encCfg s).2.1.1 ≠ 16 := by
      change pcCode s.pc ≠ 16
      cases hs : s.pc <;> simp_all [pcCode]
    obtain ⟨hd,hc,hdep,hm⟩ := step_nonrepair x (c,encCfg s) hn
    have hb := Trans.BoundsStep.step_bounds x c s h1 h2 h3
    simpa only [StepB,Trans.BoundsStep.StepB,hd,hc,hdep,hm] using hb

end QecReliability.LatentMachine.EndpointControllerBounds

