import Trans.BoundsStep.Step
import Trans.Bounds.Loop
import Assembly.Loop
import Assembly.Poly

/-!
# Trans.BoundsStep.Envelope: the loop functions within one polynomial budget in `L = paperL`

With `SP L = statePoly G density sc L` (the size bridge `Bounds.instEnc_size_le`: every encoded
reachable state has size `≤ SP L`), callee envelopes `Cc Cd Cm` (cost/depth/size budget of
`x.compile` at `(X, request)` and of `x.endpoint` at `(X, false/true)`, supplied by the
query/hash side) and init envelopes `Ci Di Mi` (for `initTopF` at the machine input, also an
assumption here), the budget functions

* `valueB L = 30000 (SP L + 1) + 3 Cm(L) + Mi(L) + 100`,
* `costB  L = 5000000 (SP L + 1)² + 1100 (SP L + 1)³ + 3 Cc(L) + Ci(L) + 40000`,
* `depthB L = 2000 (SP L + 1) + 10 (SP L + 1)² + 3 Cd(L) + Di(L) + 100`

bound cost, depth, size budget AND argument size of every top-level call at every reachable
state (`step_budget`, `isDone_budget`, `isInvoke_budget`, `query_budget`, `resume_budget`,
`output_budget`, `arg_budget`, `init_budget`), and `budget_exists` packages them into one
`Assembly.Budget` (three `PolynomialEnvelope`s) via `Assembly.PolyBounded`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Control (TR encCfg encCtx encKey TArg TCfg TCtx)
open QecReliability.Trans.Wire (TX instX instEnc wireX)
open QecReliability.Trans.Bounds (statePoly ctxPoly coinPoly OIx ictx resumeTopF outputF)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

/-! ## Budget functions -/

section Budget
variable (G density sc : ℕ) (Cc Cd Cm Ci Di Mi : PolynomialEnvelope)

def valueB (L : ℕ) : ℕ := 30000 * (statePoly G density sc L + 1) + 3 * Cm.eval L + Mi.eval L + 100

def costB (L : ℕ) : ℕ :=
  5000000 * (statePoly G density sc L + 1) ^ 2 + 1100 * (statePoly G density sc L + 1) ^ 3 +
    3 * Cc.eval L + Ci.eval L + 40000

def depthB (L : ℕ) : ℕ :=
  2000 * (statePoly G density sc L + 1) + 10 * (statePoly G density sc L + 1) ^ 2 +
    3 * Cd.eval L + Di.eval L + 100

theorem retained_pb (h D : ℕ) :
    Assembly.PolyBounded (InputEncoding.retainedPolynomial h D) := by
  have e : InputEncoding.retainedPolynomial h D = fun L =>
      456192*L^6+3041280*L^5+8734176*L^4+14066448*L^3+
      (9*InputEncoding.queryVariableCoeff h D*InputEncoding.queryClauseCoeff h+13522372)*L^2+
      (18*InputEncoding.queryVariableCoeff h D*InputEncoding.queryClauseCoeff h+
        6*InputEncoding.queryVariableCoeff h D+21*InputEncoding.queryClauseCoeff h+7425342)*L+
      (9*InputEncoding.queryVariableCoeff h D*InputEncoding.queryClauseCoeff h+
        6*InputEncoding.queryVariableCoeff h D+2*(22:ℕ).size+21*InputEncoding.queryClauseCoeff h+
        1872548) := by
    funext L
    rw [InputEncoding.retainedPolynomial_expansion]
    ring
  rw [e]
  poly_bounded

theorem statePoly_pb : Assembly.PolyBounded (statePoly G density sc) := by
  have h1 : Assembly.PolyBounded (fun L => ctxPoly sc L) := by
    have e : (fun L => ctxPoly sc L) = fun L => 300 * (L + 1) ^ 3 + 8 * ((6 * L + 5) * (sc * (2 * L)))
        + 100 := by
      funext L; rfl
    rw [e]; poly_bounded
  have h2 := retained_pb G density
  have e : statePoly G density sc =
      fun L => ctxPoly sc L + 10 * InputEncoding.retainedPolynomial G density L + 401 := by
    funext L; rfl
  rw [e]
  apply Assembly.PolyBounded.add
  apply Assembly.PolyBounded.add
  · exact h1
  · apply Assembly.PolyBounded.mul (Assembly.PolyBounded.const _)
    exact h2
  · exact Assembly.PolyBounded.const _

theorem valueB_pb : Assembly.PolyBounded (valueB G density sc Cm Mi) := by
  have h := statePoly_pb G density sc
  unfold valueB
  poly_bounded

theorem costB_pb : Assembly.PolyBounded (costB G density sc Cc Ci) := by
  have h := statePoly_pb G density sc
  unfold costB
  poly_bounded

theorem depthB_pb : Assembly.PolyBounded (depthB G density sc Cd Di) := by
  have h := statePoly_pb G density sc
  unfold depthB
  poly_bounded

/-- **One budget for everything**: three explicit envelopes dominating the budget functions. -/
theorem budget_exists : ∃ Bd : Assembly.Budget, ∀ L,
    valueB G density sc Cm Mi L ≤ Bd.value.eval L ∧ costB G density sc Cc Ci L ≤ Bd.cost.eval L ∧
      depthB G density sc Cd Di L ≤ Bd.depth.eval L := by
  obtain ⟨Pv, hv⟩ := (valueB_pb G density sc Cm Mi).envelope
  obtain ⟨Pc, hc⟩ := (costB_pb G density sc Cc Ci).envelope
  obtain ⟨Pd, hd⟩ := (depthB_pb G density sc Cd Di).envelope
  exact ⟨⟨Pv, Pc, Pd⟩, fun L => ⟨hv L, hc L, hd L⟩⟩

end Budget

/-! ## The loop functions at reachable states -/

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t) (A : CertifiedParity (512*t) (64*t) t)

section Loop
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : MultiTape.Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT E density PtE PsE T) (hT : Monotone T)
    (Cc Cd Cm Ci Di Mi : PolynomialEnvelope)
    {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd' : 0 < d)

local notation "SPL" => statePoly (gateConstant hD hd A) density (seedConstant hD hd A)
  (paperL rows a b c d)
local notation "VB" => valueB (gateConstant hD hd A) density (seedConstant hD hd A) Cm Mi
  (paperL rows a b c d)
local notation "CB" => costB (gateConstant hD hd A) density (seedConstant hD hd A) Cc Ci
  (paperL rows a b c d)
local notation "DB" => depthB (gateConstant hD hd A) density (seedConstant hD hd A) Cd Di
  (paperL rows a b c d)

include hT ha hab hc hd' in
/-- Argument size of `step/isDone/isInvoke/query/output` (the encoded state). -/
theorem arg_budget {s : Config} (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) :
    (instEnc hD hd A a b c d k rows coins s).size ≤ VB := by
  have h := Bounds.instEnc_size_le hD hd A spec hT rows coins ha hab hc hd' hs
  unfold valueB
  omega

/-- `isDone`, `isInvoke`, `query`: constant bounds at every state. -/
theorem isDone_budget (x : Control.Ix TX) (s : Config) :
    (Control.isDoneF x).cost (ictx hD hd A a b c d k rows coins, encCfg s) ≤ CB ∧
      (Control.isDoneF x).depth (ictx hD hd A a b c d k rows coins, encCfg s) ≤ DB ∧
      (Control.isDoneF x).msize (ictx hD hd A a b c d k rows coins, encCfg s) ≤ VB := by
  obtain ⟨h1, h2, h3⟩ := Bounds.isDone_bounds x (ictx hD hd A a b c d k rows coins) s
  unfold costB depthB valueB
  omega

theorem isInvoke_budget (x : Control.Ix TX) (s : Config) :
    (Control.isInvokeF x).cost (ictx hD hd A a b c d k rows coins, encCfg s) ≤ CB ∧
      (Control.isInvokeF x).depth (ictx hD hd A a b c d k rows coins, encCfg s) ≤ DB ∧
      (Control.isInvokeF x).msize (ictx hD hd A a b c d k rows coins, encCfg s) ≤ VB := by
  obtain ⟨h1, h2, h3⟩ := Bounds.isInvoke_bounds x (ictx hD hd A a b c d k rows coins) s
  unfold costB depthB valueB
  omega

theorem query_budget (x : Control.Ix TX) (s : Config) :
    (Control.queryOfF x).cost (ictx hD hd A a b c d k rows coins, encCfg s) ≤ CB ∧
      (Control.queryOfF x).depth (ictx hD hd A a b c d k rows coins, encCfg s) ≤ DB ∧
      (Control.queryOfF x).msize (ictx hD hd A a b c d k rows coins, encCfg s) ≤ VB := by
  obtain ⟨h1, h2, h3⟩ := Bounds.queryOf_bounds x (ictx hD hd A a b c d k rows coins) s
  unfold costB depthB valueB
  omega

include hT ha hab hc hd' in
/-- `output` at every reachable state. -/
theorem output_budget (o : OIx) {s : Config}
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) :
    (outputF o TX).cost (ictx hD hd A a b c d k rows coins, encCfg s) ≤ CB ∧
      (outputF o TX).depth (ictx hD hd A a b c d k rows coins, encCfg s) ≤ DB ∧
      (outputF o TX).msize (ictx hD hd A a b c d k rows coins, encCfg s) ≤ VB := by
  obtain ⟨h1, h2, h3⟩ := Bounds.outputF_bounds o (ictx hD hd A a b c d k rows coins) s
  have hS := Bounds.instEnc_size_le hD hd A spec hT rows coins ha hab hc hd' hs
  have hsplit := Bounds.instEnc_size hD hd A a b c d k rows coins s
  generalize (Ty.enc TCfg (encCfg s)).size = C at h1 h2 h3 hsplit
  unfold costB depthB valueB
  generalize SPL = P at hS ⊢
  have e3 : (C + 1) ^ 3 ≤ (P + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have e2 : (C + 1) ^ 2 ≤ (P + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  refine ⟨?_, ?_, ?_⟩ <;> omega

include hT ha hab hc hd' in
/-- `resume` (argument `(answer, state)`) at a reachable `.invoke` state with its edge. -/
theorem resume_budget (o : OIx) (x : Control.Ix TX) (bit : Bool) {s : Config} {e : Edge}
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s)
    (he : Assembly.instStep hD hd A spec a b c d k rows coins s = some e)
    (hden : (resumeTopF o x).den (bit, (ictx hD hd A a b c d k rows coins, encCfg s)) =
      (ictx hD hd A a b c d k rows coins, encCfg e.next)) :
    (resumeTopF o x).cost (bit, (ictx hD hd A a b c d k rows coins, encCfg s)) ≤ CB ∧
      (resumeTopF o x).depth (bit, (ictx hD hd A a b c d k rows coins, encCfg s)) ≤ DB ∧
      (resumeTopF o x).msize (bit, (ictx hD hd A a b c d k rows coins, encCfg s)) ≤ VB ∧
      (Val.cons (Enc.bool bit) (instEnc hD hd A a b c d k rows coins s)).size ≤ VB := by
  obtain ⟨h1, h2, h3⟩ := Bounds.resumeTop_bounds x (ictx hD hd A a b c d k rows coins) s o bit
  have hS := Bounds.instEnc_size_le hD hd A spec hT rows coins ha hab hc hd' hs
  have hS' := Bounds.instEnc_size_le hD hd A spec hT rows coins ha hab hc hd'
    (Assembly.reachable_next hs he)
  rw [hden] at h3
  have hb := Enc.bool_size bit
  have e1 : (Ty.enc (.prod (TArg TX) .bool) ((ictx hD hd A a b c d k rows coins, encCfg s), bit)).size
      = (instEnc hD hd A a b c d k rows coins s).size + (Enc.bool bit).size + 1 := by
    rw [Bounds.shape2]; rfl
  have e2 : (Ty.enc (TArg TX) (ictx hD hd A a b c d k rows coins, encCfg e.next)).size =
      (instEnc hD hd A a b c d k rows coins e.next).size := rfl
  rw [e1, e2] at h3
  have e3 : (Val.cons (Enc.bool bit) (instEnc hD hd A a b c d k rows coins s)).size =
      1 + (Enc.bool bit).size + (instEnc hD hd A a b c d k rows coins s).size := rfl
  rw [e3]
  unfold costB depthB valueB
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

include hT ha hab hc hd' in
/-- **`step`** at a reachable non-invoke state with its edge, given the callee envelopes at the
arguments the step may use and the step's meaning (`Wire.wire_step_correct`). -/
theorem step_budget (x : Control.Ix TX) {s : Config} {e : Edge}
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) (hpc : s.pc ≠ .invoke)
    (he : Assembly.instStep hD hd A spec a b c d k rows coins s = some e)
    (hden : (Control.stepF x).den (ictx hD hd A a b c d k rows coins, encCfg s) =
      (ictx hD hd A a b c d k rows coins, encCfg e.next))
    (hcomp : x.compile.cost (instX hD hd A c d k rows coins, encKey s.request) ≤
        Cc.eval (paperL rows a b c d) ∧
      x.compile.depth (instX hD hd A c d k rows coins, encKey s.request) ≤
        Cd.eval (paperL rows a b c d) ∧
      x.compile.msize (instX hD hd A c d k rows coins, encKey s.request) ≤
        Cm.eval (paperL rows a b c d))
    (hend : ∀ bb : Bool, x.endpoint.cost (instX hD hd A c d k rows coins, bb) ≤
        Cc.eval (paperL rows a b c d) ∧
      x.endpoint.depth (instX hD hd A c d k rows coins, bb) ≤ Cd.eval (paperL rows a b c d) ∧
      x.endpoint.msize (instX hD hd A c d k rows coins, bb) ≤ Cm.eval (paperL rows a b c d)) :
    (Control.stepF x).cost (ictx hD hd A a b c d k rows coins, encCfg s) ≤ CB ∧
      (Control.stepF x).depth (ictx hD hd A a b c d k rows coins, encCfg s) ≤ DB ∧
      (Control.stepF x).msize (ictx hD hd A a b c d k rows coins, encCfg s) ≤ VB := by
  have hdone := Assembly.pc_ne_done_of_step he
  have hfault := Bounds.instReachable_ne_fault hD hd A spec hT rows coins ha hab hc hd' hs
  obtain ⟨h1, h2, h3⟩ := step_bounds x (ictx hD hd A a b c d k rows coins) s hpc hdone hfault
  have hS := Bounds.instEnc_size_le hD hd A spec hT rows coins ha hab hc hd' hs
  have hS' := Bounds.instEnc_size_le hD hd A spec hT rows coins ha hab hc hd'
    (Assembly.reachable_next hs he)
  rw [hden] at h3
  have eS : (Ty.enc (TArg TX) (ictx hD hd A a b c d k rows coins, encCfg s)).size =
      (instEnc hD hd A a b c d k rows coins s).size := rfl
  have eS' : (Ty.enc (TArg TX) (ictx hD hd A a b c d k rows coins, encCfg e.next)).size =
      (instEnc hD hd A a b c d k rows coins e.next).size := rfl
  rw [eS] at h1 h2 h3
  rw [eS'] at h3
  have eC : CC x (ictx hD hd A a b c d k rows coins, encCfg s) =
      x.compile.cost (instX hD hd A c d k rows coins, encKey s.request) +
      x.endpoint.cost (instX hD hd A c d k rows coins, false) +
      x.endpoint.cost (instX hD hd A c d k rows coins, true) := rfl
  have eD : CD x (ictx hD hd A a b c d k rows coins, encCfg s) =
      x.compile.depth (instX hD hd A c d k rows coins, encKey s.request) +
      x.endpoint.depth (instX hD hd A c d k rows coins, false) +
      x.endpoint.depth (instX hD hd A c d k rows coins, true) := rfl
  have eM : CM x (ictx hD hd A a b c d k rows coins, encCfg s) =
      x.compile.msize (instX hD hd A c d k rows coins, encKey s.request) +
      x.endpoint.msize (instX hD hd A c d k rows coins, false) +
      x.endpoint.msize (instX hD hd A c d k rows coins, true) := rfl
  rw [eC] at h1
  rw [eD] at h2
  rw [eM] at h3
  obtain ⟨c1, d1, m1⟩ := hcomp
  obtain ⟨c2, d2, m2⟩ := hend false
  obtain ⟨c3, d3, m3⟩ := hend true
  generalize (instEnc hD hd A a b c d k rows coins s).size = S0 at h1 h2 h3 hS
  unfold costB depthB valueB
  generalize SPL = P at hS hS' ⊢
  have q2 : (S0 + 1) ^ 2 ≤ (P + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- `init` at the machine input, from the init envelopes (the closed form of `initTopF` is not
proved here). -/
theorem init_budget {F : FnSig (.list .bool) (TArg TX)} {w : List Bool}
    (hcost : F.cost w ≤ Ci.eval (paperL rows a b c d))
    (hdepth : F.depth w ≤ Di.eval (paperL rows a b c d))
    (hmsize : F.msize w ≤ Mi.eval (paperL rows a b c d))
    (harg : (Ty.enc (.list .bool) w).size ≤ Mi.eval (paperL rows a b c d)) :
    F.cost w ≤ CB ∧ F.depth w ≤ DB ∧ F.msize w ≤ VB ∧ (Ty.enc (.list .bool) w).size ≤ VB := by
  unfold costB depthB valueB
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end Loop

end QecReliability.Trans.BoundsStep
