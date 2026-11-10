import Trans.BoundsStep.PhaseA

/-!
# Trans.BoundsStep.PhaseCall: the phases calling the external signatures

`.compile` (`x.compile` at `(X, request)`), `.endpointZero`/`.endpointOne` (`x.endpoint` at
`(X, false/true)`), with `X = a.1.2`, `request = a.2.2.1.1`: overhead constant (cost/depth) or
`size a` (side budget) plus the callee's bound at that argument.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (TR TEnt TKey TPre TOp TG0 TG1 TG2 TG3 TG4 TG5 TG6 TCfg TCtx
  TArg bodySig bodySig_cost bodySig_depth bodySig_msize bodySig_den)

private theorem phaseCall_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem phaseCall_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable {TX' : Ty} (x : Control.Ix TX')

/-! ## compile -/

theorem compileP_cost (a : (TArg TX').den) :
    (Control.compilePF x).cost a ≤ 1000 + x.compile.cost (a.1.2, a.2.2.1.1) := by
  have l3 := lit_sz 3 (by omega)
  dsimp only [Control.compilePF, bodySig_cost, Control.compilePBody, Tm.cost, Tm.den, Env.one, phaseCall_get_zero, phaseCall_get_succ,
    Ty.enc_nat]
  fin_le

theorem compileP_depth (a : (TArg TX').den) :
    (Control.compilePF x).depth a ≤ 2 + x.compile.depth (a.1.2, a.2.2.1.1) := by
  dsimp only [Control.compilePF, bodySig_depth, Control.compilePBody, Tm.depth, Tm.den, Env.one, phaseCall_get_zero, phaseCall_get_succ]
  fin_le

theorem compileP_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.compilePBody x) (Env.one a) ≤
      (Ty.enc (TArg TX') a).size + x.compile.msize (a.1.2, a.2.2.1.1) := by
  dsimp only [Control.compilePBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseCall_get_zero, phaseCall_get_succ]
  sz_norm
  fin_le

/-! ## endpoints -/

theorem endpointZero_cost (a : (TArg TX').den) :
    (Control.endpointZeroF x).cost a ≤ 1000 + x.endpoint.cost (a.1.2, false) := by
  have l15 := lit_sz 15 (by omega)
  dsimp only [Control.endpointZeroF, bodySig_cost, Control.endpointZeroBody, Tm.cost, Tm.den,
    Env.one, phaseCall_get_zero, phaseCall_get_succ, Ty.enc_nat]
  fin_le

theorem endpointZero_depth (a : (TArg TX').den) :
    (Control.endpointZeroF x).depth a ≤ 2 + x.endpoint.depth (a.1.2, false) := by
  dsimp only [Control.endpointZeroF, bodySig_depth, Control.endpointZeroBody, Tm.depth, Tm.den,
    Env.one, phaseCall_get_zero, phaseCall_get_succ]
  fin_le

theorem endpointZero_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.endpointZeroBody x) (Env.one a) ≤
      (Ty.enc (TArg TX') a).size + x.endpoint.msize (a.1.2, false) := by
  dsimp only [Control.endpointZeroBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseCall_get_zero, phaseCall_get_succ]
  sz_norm
  fin_le

theorem endpointOne_cost (a : (TArg TX').den) :
    (Control.endpointOneF x).cost a ≤ 1000 + x.endpoint.cost (a.1.2, true) := by
  have l16 := lit_sz 16 (by omega)
  dsimp only [Control.endpointOneF, bodySig_cost, Control.endpointOneBody, Tm.cost, Tm.den,
    Env.one, phaseCall_get_zero, phaseCall_get_succ, Ty.enc_nat]
  fin_le

theorem endpointOne_depth (a : (TArg TX').den) :
    (Control.endpointOneF x).depth a ≤ 2 + x.endpoint.depth (a.1.2, true) := by
  dsimp only [Control.endpointOneF, bodySig_depth, Control.endpointOneBody, Tm.depth, Tm.den,
    Env.one, phaseCall_get_zero, phaseCall_get_succ]
  fin_le

theorem endpointOne_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.endpointOneBody x) (Env.one a) ≤
      (Ty.enc (TArg TX') a).size + x.endpoint.msize (a.1.2, true) := by
  dsimp only [Control.endpointOneBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseCall_get_zero, phaseCall_get_succ]
  sz_norm
  fin_le

end QecReliability.Trans.BoundsStep
