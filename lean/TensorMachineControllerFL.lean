import TensorMachineContextFL
import LatentEndpointDispatchFL

/-! Actual FL controller bodies for tensor output. The counting phases are
shared, but the first endpoint phase is replaced by the complete tensor repair
call. Thus no old two-endpoint linear repair is used for tensor output. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.ControllerFL

open FL FL.Lib FL.Tm Trans.Control Trans.Control.Tm
open OracleCost OracleCost.WholeWrapperCandidate RationalOutput

abbrev TX := ContextFL.TX
abbrev RepairArg : Ty := .prod TX (.prod (.list TEnt) (.list TEnt))

/-- All grid entries are repaired together, using the full retained context. -/
def finishBody (repair : FnSig RepairArg (.list TR)) : Tm [TArg TX] TCfg :=
  .letE (.app repair (.pair (A.X v0)
    (.pair (F.goodTable (A.cfg v0)) (F.badTable (A.cfg v0))))) <|
  F.cfgWith (A.cfg v1) (g0 := setPc (A.cfg v1) 18)
    (g5 := F.g5With (A.cfg v1) (output := v0))

def finishF (repair : FnSig RepairArg (.list TR)) (idx : ℕ) :=
  bodySig idx (finishBody repair)

/-- Intercept the first endpoint boundary, after both count tables are complete. -/
def dispatchBody (x : Ix TX) (repair : FnSig RepairArg (.list TR)) (finishIdx : ℕ) :
    Tm [TArg TX] TCfg :=
  .ite (Tm.eqLit x (F.pc (A.cfg v0)) 14)
    (.app (finishF repair finishIdx) v0)
    (.app (LatentMachine.EndpointControllerFL.dispatchF x) v0)

def dispatchF (x : Ix TX) (repair : FnSig RepairArg (.list TR)) (finishIdx idx : ℕ) :=
  bodySig idx (dispatchBody x repair finishIdx)

def stepBody (x : Ix TX) (repair : FnSig RepairArg (.list TR)) (finishIdx dispatchIdx : ℕ) :
    Tm [TArg TX] (TArg TX) :=
  .pair (.fst v0) (.app (dispatchF x repair finishIdx dispatchIdx) v0)

def stepF (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (finishIdx dispatchIdx idx : ℕ) := bodySig idx (stepBody x repair finishIdx dispatchIdx)

theorem finish_valid {repair : FnSig RepairArg (.list TR)} {idx : ℕ} {P : FL.Program}
    (hr : ∀ a, repair.ValidAt P a)
    (hi : P[idx]? = some (finishBody repair).compile) :
    ∀ a, (finishF repair idx).ValidAt P a := by
  intro a
  apply bodySig_valid hi
  simp [finishBody, tm_simp, hr]

theorem dispatch_valid {x : Ix TX} {repair : FnSig RepairArg (.list TR)}
    {finishIdx idx : ℕ} {P : FL.Program}
    (he : ∀ a, (eqF x.eq).ValidAt P a)
    (hf : ∀ a, (finishF repair finishIdx).ValidAt P a)
    (hd : ∀ a, (LatentMachine.EndpointControllerFL.dispatchF x).ValidAt P a)
    (hi : P[idx]? = some (dispatchBody x repair finishIdx).compile) :
    ∀ a, (dispatchF x repair finishIdx idx).ValidAt P a := by
  intro a
  apply bodySig_valid hi
  simp [dispatchBody, Tm.eqLit, tm_simp, he, hf, hd]

theorem step_valid {x : Ix TX} {repair : FnSig RepairArg (.list TR)}
    {finishIdx dispatchIdx idx : ℕ} {P : FL.Program}
    (hd : ∀ a, (dispatchF x repair finishIdx dispatchIdx).ValidAt P a)
    (hi : P[idx]? = some (stepBody x repair finishIdx dispatchIdx).compile) :
    ∀ a, (stepF x repair finishIdx dispatchIdx idx).ValidAt P a := by
  intro a
  apply bodySig_valid hi
  simp [stepBody, tm_simp, hd]

/-- This equality ensures tensor repair results, rather than raw estimates,
are the values stored in the final output field. -/
theorem finish_den (repair : FnSig RepairArg (.list TR)) (idx q r B m : ℕ)
    (X : TX.den) (s : Config) (values : List Ratio)
    (hr : repair.den (X, s.goodTable, s.badTable) = values.map toR) :
    (finishF repair idx).den (encCtx q r B m X, encCfg s) =
      encCfg { s with pc := .done, output := values } := by
  simp only [finishF, bodySig_den, finishBody, tm_simp, encCtx, encCfg]
  rw [hr]
  rfl

theorem dispatch_den_endpoint (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (finishIdx idx q r B m : ℕ) (X : TX.den) (s : Config) (hs : s.pc = .endpointZero) :
    (dispatchF x repair finishIdx idx).den (encCtx q r B m X, encCfg s) =
      (finishF repair finishIdx).den (encCtx q r B m X, encCfg s) := by
  simp [dispatchF, bodySig_den, dispatchBody, Tm.eqLit, tm_simp, eqF_den,
    encCtx, encCfg, hs, pcCode]

theorem dispatch_den_other (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (finishIdx idx q r B m : ℕ) (X : TX.den) (s : Config) (hs : s.pc ≠ .endpointZero) :
    (dispatchF x repair finishIdx idx).den (encCtx q r B m X, encCfg s) =
      (LatentMachine.EndpointControllerFL.dispatchF x).den (encCtx q r B m X, encCfg s) := by
  have hc : pcCode s.pc ≠ 14 := by
    intro h
    exact hs (pcCode_injective h)
  simp only [dispatchF, bodySig_den, dispatchBody, tm_simp, Tm.eqLit, eqF_den]
  simp only [encCtx, encCfg, hc, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem step_den_endpoint (x : Ix TX) (repair : FnSig RepairArg (.list TR))
    (finishIdx dispatchIdx idx q r B m : ℕ) (X : TX.den) (s : Config)
    (hs : s.pc = .endpointZero) (values : List Ratio)
    (hr : repair.den (X, s.goodTable, s.badTable) = values.map toR) :
    (stepF x repair finishIdx dispatchIdx idx).den (encCtx q r B m X, encCfg s) =
      (encCtx q r B m X, encCfg { s with pc := .done, output := values }) := by
  simp only [stepF, bodySig_den, stepBody, tm_simp]
  rw [dispatch_den_endpoint x repair finishIdx dispatchIdx q r B m X s hs,
    finish_den repair finishIdx q r B m X s values hr]

end QecReliability.TensorMachine.ControllerFL
