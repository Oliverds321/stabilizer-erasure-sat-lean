import TensorMachineContextBounds
import Trans.BoundsStep.Base

/-! Binary intermediate-space composition for tensor context construction. -/

set_option autoImplicit false
namespace QecReliability.TensorMachine.ContextFL
open FL FL.Lib FL.Tm Trans.Wire Trans.Control Trans.BoundsStep
private theorem lookup_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl
private theorem lookup_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable (L : Lib) (a : AIx) (gi : GridFL.Indices)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
  (base den oldCtx lengthIdx ctxIdx : ℕ)

def contextSpace (p : ParserFL.ParsedTy.den) : ℕ :=
  let gs := (GridFL.gridF L gi).den p.1
  let len := (lengthF GridFL.Row lengthIdx).den gs
  let k := (predF L.pred).den len
  let old := (LatentMachine.ContextFL.contextF L a Fp base den oldCtx).den p.2
  let reps := (k,p.2.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2.2.1)
  (GridFL.gridF L gi).msize p.1 + (lengthF GridFL.Row lengthIdx).msize gs +
    (predF L.pred).msize len + (LatentMachine.ContextFL.contextF L a Fp base den oldCtx).msize p.2 +
    (repBF L a).msize reps + 100*((Ty.enc ParserFL.ParsedTy p).size +
      (Ty.enc GridFL.Table gs).size + (Enc.nat len).size + (Enc.nat k).size +
      (Ty.enc (TCtx Trans.Wire.TX) old).size + (Enc.nat ((repBF L a).den reps)).size + 1)

set_option maxHeartbeats 3000000 in
theorem context_msize (p : ParserFL.ParsedTy.den) :
    (contextF L a gi Fp base den oldCtx lengthIdx ctxIdx).msize p ≤
      contextSpace L a gi Fp base den oldCtx lengthIdx p := by
  dsimp only [contextF,bodySig_msize,contextBody,Tm.msize,Tm.den,Env.one,lookup_zero,
    lookup_succ,contextSpace,LatentMachine.ContextFL.pC,LatentMachine.ContextFL.pD]
  sz_norm
  simp only [max_le_iff]
  (repeat' apply And.intro) <;> omega

end QecReliability.TensorMachine.ContextFL
