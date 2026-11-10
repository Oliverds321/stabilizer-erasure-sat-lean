import TensorMachineContextFL
import Trans.Control.Init

/-! Tensor initialization invokes the certified parser, context builder and
existing counting-program constructor. Q=1 is a valid counting program, so
empty or all-zero degree lists require no unproved exceptional path. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.InitializerFL

open FL FL.Lib FL.Tm Trans.Control
open OracleCost.WholeWrapperCandidate

abbrev TX := ContextFL.TX

def initialBody (parser : FnSig (.list .bool) ParserFL.ParsedTy)
    (context : FnSig ParserFL.ParsedTy (TCtx TX)) (y : IxI) :
    Tm [.list .bool] (TArg TX) :=
  .letE (.app parser v0) <|
  .letE (.app context v0) <|
    .pair v0 (.app (initF y) (.pair (.fst (.fst v0))
      (.pair (.fst (.snd (.fst v0))) (.snd (.snd (.snd (.fst v0)))))))

def initialF (parser : FnSig (.list .bool) ParserFL.ParsedTy)
    (context : FnSig ParserFL.ParsedTy (TCtx TX)) (y : IxI) (idx : ℕ) :=
  bodySig idx (initialBody parser context y)

theorem initial_den (parser : FnSig (.list .bool) ParserFL.ParsedTy)
    (context : FnSig ParserFL.ParsedTy (TCtx TX)) (y : IxI) (idx : ℕ) (bs : List Bool) :
    let ctx := context.den (parser.den bs)
    (initialF parser context y idx).den bs =
      (ctx, encCfg (initial ctx.1.1 ctx.1.2.1 ctx.1.2.2.2)) := by
  simp only [initialF, bodySig_den, initialBody, tm_simp]
  rw [initF_den]

theorem initial_valid {parser : FnSig (.list .bool) ParserFL.ParsedTy}
    {context : FnSig ParserFL.ParsedTy (TCtx TX)} {y : IxI} {idx : ℕ} {P : FL.Program}
    (hp : ∀ bs, parser.ValidAt P bs) (hc : ∀ p, context.ValidAt P p)
    (hy : LibI y P) (hi : P[idx]? = some (initialBody parser context y).compile) :
    ∀ bs, (initialF parser context y idx).ValidAt P bs := by
  intro bs
  apply bodySig_valid hi
  simp [initialBody, tm_simp, hp, hc, init_valid hy]

theorem initial_computes {parser : FnSig (.list .bool) ParserFL.ParsedTy}
    {context : FnSig ParserFL.ParsedTy (TCtx TX)} {y : IxI} {idx : ℕ} {P : FL.Program}
    (hp : ∀ bs, parser.ValidAt P bs) (hc : ∀ p, context.ValidAt P p)
    (hy : LibI y P) (hi : P[idx]? = some (initialBody parser context y).compile)
    (bs : List Bool) :
    let ctx := context.den (parser.den bs)
    let F := initialF parser context y idx
    FL.Computes P idx ((Ty.list Ty.bool).enc bs)
      ((TArg TX).enc (ctx, encCfg (initial ctx.1.1 ctx.1.2.1 ctx.1.2.2.2)))
      (max (F.msize bs) ((Ty.list Ty.bool).enc bs).size) (F.cost bs) (F.depth bs) := by
  dsimp only
  have h := (initial_valid hp hc hy hi bs).computes
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [initial_den] at h
  exact h

end QecReliability.TensorMachine.InitializerFL
