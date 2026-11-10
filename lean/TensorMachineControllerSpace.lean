import TensorMachineControllerBounds

/-! Intermediate space for the actual finish body is charged in bits: the
input state, the repaired table's encoded size, and the callback's own space. -/

set_option autoImplicit false
namespace QecReliability.TensorMachine.ControllerFL
open FL FL.Lib FL.Tm Trans.Control Trans.BoundsStep

private theorem lookup_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl
private theorem lookup_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

set_option maxHeartbeats 3000000 in
theorem finish_msize (repair : FnSig RepairArg (.list TR)) (idx : ℕ) (a : (TArg TX).den) :
    (finishF repair idx).msize a ≤
      1000 * ((Ty.enc (TArg TX) a).size +
        (Ty.enc (.list TR) (repair.den (repairInput a))).size + 1) +
      repair.msize (repairInput a) := by
  have h18 : (Enc.nat 18).size ≤ 21 := (Trans.BoundsStep.lit_sz 18 (by omega)).2
  generalize hS : (Ty.enc (TArg TX) a).size = S
  rcases a with ⟨⟨⟨q,r,B,m⟩,X⟩,g0,g1,g2,g3,g4,g5,g6⟩
  dsimp only [finishF,bodySig_msize,finishBody,Tm.msize,Tm.den,Env.one,
    lookup_zero,lookup_succ,repairInput]
  sz_norm at hS ⊢
  simp only [max_le_iff]
  (repeat' apply And.intro) <;> omega

/-- The top-level pair adds only its actual result size to dispatch space. -/
theorem step_msize (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (finishIdx dispatchIdx idx : ℕ) (a : (TArg TX).den) :
    (stepF x repair finishIdx dispatchIdx idx).msize a ≤
      (dispatchF x repair finishIdx dispatchIdx).msize a +
      (Ty.enc (TArg TX) ((stepF x repair finishIdx dispatchIdx idx).den a)).size := by
  dsimp only [TArg,stepF,bodySig_msize,bodySig_den,stepBody,Tm.msize,Tm.den,Env.one,
    lookup_zero,lookup_succ]
  omega

end QecReliability.TensorMachine.ControllerFL
