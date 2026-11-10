import TensorMachineContextFL
import TensorMachineGridCost
import TensorMachineGridSpace
import LatentContextBounds

/-! Resource composition for the runtime grid context. Precision and count
operands remain charged by their binary encodings. -/

set_option autoImplicit false
namespace QecReliability.TensorMachine.ContextFL
open FL FL.Lib FL.Tm Trans.Wire Trans.Control

private theorem lookup_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl
private theorem lookup_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable (L : Lib) (a : AIx) (gi : GridFL.Indices)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
  (base den oldCtx lengthIdx ctxIdx : ℕ)

def contextCost (p : ParserFL.ParsedTy.den) : ℕ :=
  let gs := (GridFL.gridF L gi).den p.1
  let len := (lengthF GridFL.Row lengthIdx).den gs
  let k := (predF L.pred).den len
  (GridFL.gridF L gi).cost p.1 + (lengthF GridFL.Row lengthIdx).cost gs +
    (predF L.pred).cost len + (LatentMachine.ContextFL.contextF L a Fp base den oldCtx).cost p.2 +
    (repBF L a).cost (k,p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1) + 200

def contextDepth (p : ParserFL.ParsedTy.den) : ℕ :=
  let gs := (GridFL.gridF L gi).den p.1
  let len := (lengthF GridFL.Row lengthIdx).den gs
  let k := (predF L.pred).den len
  (GridFL.gridF L gi).depth p.1 + (lengthF GridFL.Row lengthIdx).depth gs +
    (predF L.pred).depth len + (LatentMachine.ContextFL.contextF L a Fp base den oldCtx).depth p.2 +
    (repBF L a).depth (k,p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1) + 50

set_option maxHeartbeats 1000000 in
theorem context_cost (p : ParserFL.ParsedTy.den) :
    (contextF L a gi Fp base den oldCtx lengthIdx ctxIdx).cost p ≤
      contextCost L a gi Fp base den oldCtx lengthIdx p := by
  dsimp only [contextF,bodySig_cost,contextBody,Tm.cost,Tm.den,Env.one,lookup_zero,
    lookup_succ,contextCost,LatentMachine.ContextFL.pC,LatentMachine.ContextFL.pD]
  omega

set_option maxHeartbeats 1000000 in
theorem context_depth (p : ParserFL.ParsedTy.den) :
    (contextF L a gi Fp base den oldCtx lengthIdx ctxIdx).depth p ≤
      contextDepth L a gi Fp base den oldCtx lengthIdx p := by
  dsimp only [contextF,bodySig_depth,contextBody,Tm.depth,Tm.den,Env.one,lookup_zero,
    lookup_succ,contextDepth,LatentMachine.ContextFL.pC,LatentMachine.ContextFL.pD]
  omega

/-- The context is a constructed pair, so its retained result is included in
its actual intermediate-space measure. -/
theorem context_result_size (p : ParserFL.ParsedTy.den) :
    (Ty.enc (TCtx TX) ((contextF L a gi Fp base den oldCtx lengthIdx ctxIdx).den p)).size ≤
      (contextF L a gi Fp base den oldCtx lengthIdx ctxIdx).msize p := by
  dsimp only [TCtx,contextF,bodySig_msize,bodySig_den,contextBody,Tm.msize,Tm.den,
    Env.one,lookup_zero,lookup_succ]
  omega

end QecReliability.TensorMachine.ContextFL
