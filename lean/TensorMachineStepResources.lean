import TensorMachineControllerSpace

/-! Measured overhead of the tensor dispatch on actual counting states. The
inherited step retains its existing bit-resource analysis. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.ControllerFL
open FL FL.Lib FL.Tm Trans.Control Trans.BoundsStep

private theorem lookup_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl
private theorem lookup_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

set_option maxHeartbeats 3000000 in
theorem nonfinish_resources (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (fi di si : ℕ) (a : (TArg TX).den) (hp : a.2.1.1 ≠ 14) :
    (stepF x repair fi di si).cost a ≤
      (LatentMachine.EndpointControllerFL.stepF x).cost a + (eqF x.eq).cost (a.2.1.1,14)+1000 ∧
    (stepF x repair fi di si).depth a ≤
      (LatentMachine.EndpointControllerFL.stepF x).depth a + (eqF x.eq).depth (a.2.1.1,14)+100 ∧
    (stepF x repair fi di si).msize a ≤
      (LatentMachine.EndpointControllerFL.stepF x).msize a + (eqF x.eq).msize (a.2.1.1,14)+
        ((TArg TX).enc a).size+100 := by
  have h14 : (Enc.nat 14).size ≤ 21 := (lit_sz 14 (by omega)).2
  dsimp only [stepF,dispatchF,bodySig_cost,bodySig_depth,bodySig_msize,bodySig_den,
    stepBody,dispatchBody,Trans.Control.Tm.eqLit,
    LatentMachine.EndpointControllerFL.stepF,LatentMachine.EndpointControllerFL.stepBody,
    Tm.cost,Tm.depth,Tm.msize,Tm.den,Env.one,lookup_zero,lookup_succ]
  simp only [eqF_den,hp,decide_false,if_false,Bool.false_eq_true,Ty.enc_nat,
    Ty.sz_prod,Enc.bool_false_size,max_le_iff]
  (repeat' apply And.intro) <;> omega

theorem pc_test_bounds (idx : ℕ) (pc : OracleCost.WholeWrapperCandidate.PC) :
    (eqF idx).cost (pcCode pc,14) ≤ 2000 ∧
    (eqF idx).depth (pcCode pc,14) ≤ 20 ∧
    (eqF idx).msize (pcCode pc,14) ≤ 100 := by
  have hp := (lit_sz (pcCode pc) ((pcCode_lt pc).trans_le (by decide))).1
  have hl := (lit_sz 14 (by omega)).1
  simp only [eqF_cost,eqF_depth,eqF_msize]
  omega

theorem nonfinish_den (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (fi di si : ℕ) (a : (TArg TX).den) (hp : a.2.1.1 ≠ 14) :
    (stepF x repair fi di si).den a = (LatentMachine.EndpointControllerFL.stepF x).den a := by
  simp only [stepF,dispatchF,bodySig_den,stepBody,dispatchBody,Trans.Control.Tm.eqLit,
    LatentMachine.EndpointControllerFL.stepF,LatentMachine.EndpointControllerFL.stepBody,
    tm_simp,eqF_den,hp,decide_false,if_false,Bool.false_eq_true]

def localStepBudget (S K : ℕ) : ℕ := 6000000*(S+1)^2+30000*(S+1)+3*K+4000

open OracleCost OracleCost.WholeWrapperCandidate in
theorem counting_resources (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (fi di si : ℕ) (c : (TCtx TX).den) (s : Config) (S K : ℕ)
    (hn : s.pc ≠ .invoke) (hd : s.pc ≠ .done) (hf : s.pc ≠ .fault)
    (hb : s.pc ≠ .endpointZero)
    (harg : ((TArg TX).enc (c,encCfg s)).size ≤ S)
    (hnext : ((TArg TX).enc ((LatentMachine.EndpointControllerFL.stepF x).den (c,encCfg s))).size ≤ S)
    (hc : CC x (c,encCfg s) ≤ K) (hdep : CD x (c,encCfg s) ≤ K)
    (hm : CM x (c,encCfg s) ≤ K) :
    (stepF x repair fi di si).cost (c,encCfg s) ≤ localStepBudget S K ∧
    (stepF x repair fi di si).depth (c,encCfg s) ≤ localStepBudget S K ∧
    (stepF x repair fi di si).msize (c,encCfg s) ≤ localStepBudget S K := by
  have hpc : (c,encCfg s).2.1.1 ≠ 14 := by
    change pcCode s.pc ≠ 14
    cases h : s.pc <;> simp_all [pcCode]
  obtain ⟨ot,od,om⟩ := LatentMachine.EndpointControllerBounds.step_bounds x c s hn hd hf
  obtain ⟨nt,nd,nm⟩ := nonfinish_resources x repair fi di si (c,encCfg s) hpc
  obtain ⟨et,ed,em⟩ := pc_test_bounds x.eq s.pc
  change (eqF x.eq).cost ((c,encCfg s).2.1.1,14) ≤ _ at et
  change (eqF x.eq).depth ((c,encCfg s).2.1.1,14) ≤ _ at ed
  change (eqF x.eq).msize ((c,encCfg s).2.1.1,14) ≤ _ at em
  have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right harg 1) 2
  have hlin : S+1 ≤ (S+1)^2 := Nat.le_self_pow (by decide) _
  unfold localStepBudget
  constructor
  · omega
  constructor <;> omega

end QecReliability.TensorMachine.ControllerFL
