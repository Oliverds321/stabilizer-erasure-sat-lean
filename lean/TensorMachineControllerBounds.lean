import TensorMachineControllerFL
import LatentEndpointStepBounds

/-! The extra tensor dispatch and finish bodies have fixed structural overhead.
Their resource bounds retain the real installed repair callback's measures. -/

set_option autoImplicit false
namespace QecReliability.TensorMachine.ControllerFL
open FL FL.Lib FL.Tm Trans.Control

private theorem lookup_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl
private theorem lookup_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

def repairInput (a : (TArg TX).den) : RepairArg.den :=
  (a.1.2,a.2.2.2.2.2.1.2.2.1,a.2.2.2.2.2.1.2.2.2.1)

/-- Finishing copies the existing configuration and stores the repaired table. -/
theorem finish_cost (repair : FnSig RepairArg (.list TR)) (idx : ℕ) (a : (TArg TX).den) :
    (finishF repair idx).cost a ≤ repair.cost (repairInput a) + 1000 := by
  have h18 : (Ty.enc .nat 18).size ≤ 21 := (Trans.BoundsStep.lit_sz 18 (by omega)).2
  dsimp only [finishF, bodySig_cost, finishBody, Tm.cost, Tm.den, Env.one,
    lookup_zero, lookup_succ, repairInput]
  omega

theorem finish_depth (repair : FnSig RepairArg (.list TR)) (idx : ℕ) (a : (TArg TX).den) :
    (finishF repair idx).depth a ≤ repair.depth (repairInput a) + 100 := by
  dsimp only [finishF, bodySig_depth, finishBody, Tm.depth, Tm.den, Env.one,
    lookup_zero, lookup_succ, repairInput]
  try simp only [max_le_iff]
  (repeat' apply And.intro) <;> omega

/-- Reusable wrapper cost without replacing the actual query/counting code. -/
theorem dispatch_cost (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (finishIdx idx : ℕ) (a : (TArg TX).den) :
    (dispatchF x repair finishIdx idx).cost a ≤
      (eqF x.eq).cost (a.2.1.1,14) + 100 +
      (if a.2.1.1 = 14 then (finishF repair finishIdx).cost a
       else (LatentMachine.EndpointControllerFL.dispatchF x).cost a) := by
  have h14 : (Enc.nat 14).size ≤ 21 := (Trans.BoundsStep.lit_sz 14 (by omega)).2
  dsimp only [dispatchF, bodySig_cost, dispatchBody, Tm.cost, Tm.den,
    Trans.Control.Tm.eqLit, Env.one, lookup_zero, lookup_succ]
  simp only [eqF_den]
  split <;> simp_all <;> omega

theorem dispatch_depth (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (finishIdx idx : ℕ) (a : (TArg TX).den) :
    (dispatchF x repair finishIdx idx).depth a ≤
      (eqF x.eq).depth (a.2.1.1,14) + 10 +
      (if a.2.1.1 = 14 then (finishF repair finishIdx).depth a
       else (LatentMachine.EndpointControllerFL.dispatchF x).depth a) := by
  dsimp only [dispatchF, bodySig_depth, dispatchBody, Tm.depth, Tm.den,
    Trans.Control.Tm.eqLit, Env.one, lookup_zero, lookup_succ]
  simp only [eqF_den]
  split <;> simp_all <;> omega

theorem step_cost (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (finishIdx dispatchIdx idx : ℕ) (a : (TArg TX).den) :
    (stepF x repair finishIdx dispatchIdx idx).cost a ≤
      (dispatchF x repair finishIdx dispatchIdx).cost a + 20 := by
  dsimp only [stepF, bodySig_cost, stepBody, Tm.cost, Tm.den, Env.one,
    lookup_zero, lookup_succ]
  omega

theorem step_depth (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (finishIdx dispatchIdx idx : ℕ) (a : (TArg TX).den) :
    (stepF x repair finishIdx dispatchIdx idx).depth a ≤
      (dispatchF x repair finishIdx dispatchIdx).depth a + 10 := by
  dsimp only [stepF, bodySig_depth, stepBody, Tm.depth, Tm.den, Env.one,
    lookup_zero, lookup_succ]
  omega

end QecReliability.TensorMachine.ControllerFL
