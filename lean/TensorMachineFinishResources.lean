import TensorMachineStepResources

/-! The final tensor iteration charges the actual repaired table in bits,
including copying it into the output configuration. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.ControllerFL
open FL FL.Lib FL.Tm Trans.Control Trans.BoundsStep

private theorem lookup_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl
private theorem lookup_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

set_option maxHeartbeats 3000000 in
theorem finish_result_size (repair : FnSig RepairArg (.list TR)) (fi : ℕ) (a : (TArg TX).den) :
    (Ty.enc TCfg ((finishF repair fi).den a)).size ≤
      (Ty.enc TCfg a.2).size + (Ty.enc (.list TR) (repair.den (repairInput a))).size+100 := by
  have h18 : (Enc.nat 18).size ≤ 21 := (lit_sz 18 (by omega)).2
  dsimp only [finishF,bodySig_den,finishBody,Tm.den,Env.one,lookup_zero,lookup_succ,repairInput]
  sz_norm
  omega

set_option maxHeartbeats 3000000 in
theorem finish_step_space (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (fi di si : ℕ) (a : (TArg TX).den) (hp : a.2.1.1 = 14) :
    (stepF x repair fi di si).msize a ≤
      (finishF repair fi).msize a + (eqF x.eq).msize (a.2.1.1,14)+
        ((TArg TX).enc a).size +
        ((TArg TX).enc (a.1,(finishF repair fi).den a)).size+100 := by
  have h14 : (Enc.nat 14).size ≤ 21 := (lit_sz 14 (by omega)).2
  dsimp only [stepF,dispatchF,bodySig_msize,bodySig_den,stepBody,dispatchBody,
    Trans.Control.Tm.eqLit,Tm.msize,Tm.den,Env.one,lookup_zero,lookup_succ]
  simp only [eqF_den,hp,decide_true,if_true,Ty.enc_nat,Ty.sz_prod,max_le_iff]
  (repeat' apply And.intro) <;> omega

def finalStepBudget (S R : ℕ) : ℕ := 5000*(S+R+1)+R+5000

theorem finish_resources (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (fi di si : ℕ) (a : (TArg TX).den) (S R : ℕ) (hp : a.2.1.1 = 14)
    (hs : ((TArg TX).enc a).size ≤ S)
    (ht : repair.cost (repairInput a) ≤ R) (hd : repair.depth (repairInput a) ≤ R)
    (hm : repair.msize (repairInput a) ≤ R)
    (ho : (Ty.enc (.list TR) (repair.den (repairInput a))).size ≤ R) :
    (stepF x repair fi di si).cost a ≤ finalStepBudget S R ∧
    (stepF x repair fi di si).depth a ≤ finalStepBudget S R ∧
    (stepF x repair fi di si).msize a ≤ finalStepBudget S R := by
  have eqt : (eqF x.eq).cost (a.2.1.1,14) ≤ 2000 := by
    rw [hp]; have hl := (lit_sz 14 (by omega)).1; simp only [eqF_cost]; omega
  have eqd : (eqF x.eq).depth (a.2.1.1,14) ≤ 20 := by
    rw [hp]; have hl := (lit_sz 14 (by omega)).1; simp only [eqF_depth]; omega
  have eqm : (eqF x.eq).msize (a.2.1.1,14) ≤ 100 := by
    rw [hp]; have hl := (lit_sz 14 (by omega)).1; simp only [eqF_msize]; omega
  have fc := finish_cost repair fi a
  have fd := finish_depth repair fi a
  have fm := finish_msize repair fi a
  have dc := dispatch_cost x repair fi di a
  have dd := dispatch_depth x repair fi di a
  simp only [hp,↓reduceIte] at dc dd eqt eqd eqm
  have sc := step_cost x repair fi di si a
  have sd := step_depth x repair fi di si a
  have sm := finish_step_space x repair fi di si a hp
  rw [hp] at sm
  have hr := finish_result_size repair fi a
  have hout : ((TArg TX).enc (a.1,(finishF repair fi).den a)).size ≤ S+R+100 := by
    have hi := @Trans.Bounds.shape2 (TCtx TX) TCfg a.1 a.2
    change ((TArg TX).enc a).size =
      ((TCtx TX).enc a.1).size + (TCfg.enc a.2).size + 1 at hi
    rw [Trans.Bounds.shape2]
    omega
  unfold finalStepBudget
  constructor
  · omega
  constructor <;> omega

end QecReliability.TensorMachine.ControllerFL
