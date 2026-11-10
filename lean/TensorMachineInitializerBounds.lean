import TensorMachineInitializerFL
import TensorMachineContextBounds
import TensorMachineParserBounds
import Final.Init.Top

/-! Concrete initializer composition. Empty and zero-degree classes use the
same grid parser and counting-program constructor as every other input. -/

set_option autoImplicit false
namespace QecReliability.TensorMachine.InitializerFL
open FL FL.Lib FL.Tm Trans.Control

private theorem lookup_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl
private theorem lookup_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

/-- All terms in this bound are the compiler's actual callee measures. -/
theorem initial_split (parser : FnSig (.list .bool) ParserFL.ParsedTy)
    (context : FnSig ParserFL.ParsedTy (TCtx TX)) (y : IxI) (idx : ℕ) (bs : List Bool)
    (hc : (Ty.enc (TCtx TX) (context.den (parser.den bs))).size ≤ context.msize (parser.den bs)) :
    let p := parser.den bs
    let c := context.den p
    let I := (c.1.1,c.1.2.1,c.1.2.2.2)
    (initialF parser context y idx).cost bs ≤ parser.cost bs + context.cost p + (initF y).cost I + 100 ∧
    (initialF parser context y idx).depth bs ≤ parser.depth bs + context.depth p + (initF y).depth I + 20 ∧
    (initialF parser context y idx).msize bs ≤ parser.msize bs + 2*context.msize p +
      2*(initF y).msize I + 2*((Ty.prod .nat (.prod .nat .nat)).enc I).size + 100 := by
  dsimp only
  have hi := Final.Init.init_res_le y
    ((context.den (parser.den bs)).1.1,(context.den (parser.den bs)).1.2.1,
      (context.den (parser.den bs)).1.2.2.2)
  have hI := Ty.sz_prod .nat (.prod .nat .nat)
    ((context.den (parser.den bs)).1.1,(context.den (parser.den bs)).1.2.1,
      (context.den (parser.den bs)).1.2.2.2)
  have hC := Ty.sz_prod (.prod .nat (.prod .nat (.prod .nat .nat))) TX
    (context.den (parser.den bs))
  refine ⟨?_,?_,?_⟩
  · dsimp only [initialF,bodySig_cost,initialBody,Tm.cost,Tm.den,Env.one,lookup_zero,lookup_succ]
    omega
  · dsimp only [initialF,bodySig_depth,initialBody,Tm.depth,Tm.den,Env.one,lookup_zero,lookup_succ]
    omega
  · dsimp only [initialF,bodySig_msize,initialBody,Tm.msize,Tm.den,Env.one,lookup_zero,lookup_succ]
    simp only [TCtx,TCfg,Ty.sz_prod] at hc hi
    simp only [Ty.sz_prod,max_le_iff] at hI hC ⊢
    (repeat' apply And.intro) <;> omega

end QecReliability.TensorMachine.InitializerFL
