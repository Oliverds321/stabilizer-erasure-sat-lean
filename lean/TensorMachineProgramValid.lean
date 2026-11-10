import TensorMachineProgram

/-! Validity of all seven actual assembly callbacks. The only package inputs
are the already compiled tensor query/repair bodies and the existing hash
implementation; parser, context, counting phases, observers and output are
discharged from their installed code. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.Program

open FL FL.Lib FL.Tm Trans.Wire Trans.Control
open Trans.Query.Plain (ProgP)

variable (source : FL.Program) (Q : FnSig QueryFL.CompilerArg (.list .bool))
  (repair : FnSig ControllerFL.RepairArg (.list TR))
  (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

local notation "PP" => program source Q repair base den density E pg nb
local notation "CX" => controller source Q base den density E pg nb
local notation "OLD" => Install.prog base den density E pg nb

structure Valid : Prop where
  initial : ∀ bs, (initializer source base den).ValidAt PP bs
  step : ∀ a, (tensorStep source Q repair base den density E pg nb).ValidAt PP a
  isDone : ∀ a, (isDoneF CX).ValidAt PP a
  isInvoke : ∀ a, (isInvokeF CX).ValidAt PP a
  query : ∀ a, (queryOfF CX).ValidAt PP a
  resume : ∀ a, (Trans.Bounds.resumeTopF Install.oX CX).ValidAt PP a
  output : ∀ a, (Trans.Bounds.outputF Install.oX TX).ValidAt PP a

set_option maxRecDepth 2000 in
set_option maxHeartbeats 3000000 in
theorem valid
    (hs : Install.Extends (Installed.program base den density E pg nb) source)
    (hQ : ∀ a, Q.ValidAt source a) (hr : ∀ a, repair.ValidAt source a)
    (hHash : ∀ a, (Install.hashFn E pg nb).ValidAt OLD a) :
    Valid source Q repair base den density E pg nb := by
  have hx := extends_source source Q repair base den density E pg nb
  have he : Install.Extends (Installed.program base den density E pg nb) PP := by
    intro k b hk
    exact hx k b (hs k b hk)
  have hp : Install.Extends OLD PP := by
    intro k b hk
    exact he k b (Installed.extends_prefix base den density E pg nb k b hk)
  have hw : Install.Extends (LatentMachine.WrappersInstalled.program base den density E pg nb) PP := by
    intro k b hk
    exact he k b (Installed.extends_controller base den density E pg nb k b
      (LatentMachine.ControllerInstalled.extends_wrappers base den density E pg nb k b hk))
  have hcExt : Install.Extends (LatentMachine.InitializerInstalled.program base den density E pg nb) PP := by
    intro k b hk
    exact hw k b (LatentMachine.WrappersInstalled.extends_initializer base den density E pg nb k b hk)
  have oldL := Install.wL_ok base den density E pg nb
  have S := Install.std_ok base den density E pg nb
  have hL : Install.wL.OK PP := {
    succ := fun a => Install.ValidAt.extend hp (oldL.succ a)
    pred := fun a => Install.ValidAt.extend hp (oldL.pred a)
    add := fun a => Install.ValidAt.extend hp (oldL.add a)
    sub := fun a => Install.ValidAt.extend hp (oldL.sub a)
    le := fun a => Install.ValidAt.extend hp (oldL.le a)
    eq := fun a => Install.ValidAt.extend hp (oldL.eq a)
    mul := fun a => Install.ValidAt.extend hp (oldL.mul a)
    bitLen := fun a => Install.ValidAt.extend hp (oldL.bitLen a)
    dm := fun a ha => Install.ValidAt.extend hp (oldL.dm a ha)
    take := fun t a => Install.ValidAt.extend hp (oldL.take t a)
    drop := fun t a => Install.ValidAt.extend hp (oldL.drop t a)
    range := fun a => Install.ValidAt.extend hp (oldL.range a)
    rev := fun t a => Install.ValidAt.extend hp (oldL.rev t a)
    rep := fun t a => Install.ValidAt.extend hp (oldL.rep t a) }
  have hslot := slots source Q repair base den density E pg nb
  have hhashW := Trans.Wire.hashW_valid oldL
    (Install.query_valid base den density E pg nb) hHash Install.wC_ok
  have hcompiler : ∀ a, (compiler source Q base den density E pg nb).ValidAt PP a :=
    QueryFL.compile_valid Install.wL Install.wC Q (Install.hashFn E pg nb)
      base den density 16 source.length hL
      (fun a => Install.ValidAt.extend hx (hQ a))
      (fun a => Install.ValidAt.extend hp (S.getD GridFL.Row a))
      (fun a => Install.ValidAt.extend hp (hhashW a)) hslot.compiler
  have holdEndpoint : ∀ a, (LatentMachine.WrappersFL.endpointWF Install.wL
      LatentMachine.WrappersInstalled.indices Install.yR).ValidAt PP a :=
    fun a => Install.ValidAt.extend hw (LatentMachine.WrappersInstalled.endpoint_valid
      base den density E pg nb a)
  have hendpoint : ∀ a, (endpointF (source.length + 1)).ValidAt PP a := by
    intro a
    apply bodySig_valid hslot.endpoint
    simp [endpointBody, tm_simp, holdEndpoint]
  have hlib : LibOK PP CX := ControlLibrary.library_valid base den density E pg nb
    _ _ _ _ _ _ he (Install.cX_lib hHash) hcompiler hendpoint
  have hphase := ControlLibrary.phases_valid base den density E pg nb _ _ _ _ _ _
    he hlib hslot.compileP hslot.endpointZero hslot.endpointOne
  have hlegacy := LatentMachine.EndpointControllerFL.dispatch_valid hlib hphase hslot.legacyDispatch
  have hfinish := ControllerFL.finish_valid (fun a => Install.ValidAt.extend hx (hr a)) hslot.finish
  have hdispatch := ControllerFL.dispatch_valid hlib.eq hfinish hlegacy hslot.dispatch
  have hstep := ControllerFL.step_valid hdispatch hslot.step
  have hgrid := fun ds => Install.ValidAt.extend he (Installed.grid_valid base den density E pg nb ds)
  have hlen := fun xs => Install.ValidAt.extend hp (S.length GridFL.Row xs)
  have hctxOld := fun p => Install.ValidAt.extend hcExt
    (LatentMachine.InitializerInstalled.context_valid base den density E pg nb p)
  have hrep := fun p => Install.ValidAt.extend hp (repB_valid oldL Install.wA_ok p)
  have hcontext := ContextFL.context_valid Install.wL Install.wA Installed.gridIndices Install.paramsFn
    base den 295 13 (source.length + 9) hL hgrid hlen hctxOld hrep hslot.context
  have hparser := fun bs => Install.ValidAt.extend he (Installed.parse_valid base den density E pg nb bs)
  have hinit := fun a => Install.ValidAt.extend hp (init_valid Install.yI_ok a)
  have hinitial : ∀ bs, (initializer source base den).ValidAt PP bs := by
    intro bs
    apply bodySig_valid hslot.initial
    simp [InitializerFL.initialBody, context, tm_simp, hparser, hcontext, hinit]
  have hdone : ∀ a, (isDoneF CX).ValidAt PP a := by
    intro a
    apply bodySig_valid (he _ _ rfl)
    simp [isDoneBody, Trans.Control.Tm.eqLit, tm_simp, hlib.eq]
  have hinvoke : ∀ a, (isInvokeF CX).ValidAt PP a := by
    intro a
    apply bodySig_valid (he _ _ rfl)
    simp [isInvokeBody, Trans.Control.Tm.eqLit, tm_simp, hlib.eq]
  have hquery : ∀ a, (queryOfF CX).ValidAt PP a := by
    intro a
    apply bodySig_valid (he _ _ rfl)
    simp [queryOfBody, tm_simp]
  have ho : Install.oX.OK PP TX CX := {
    pred := fun a => Install.ValidAt.extend hp (S.pred a)
    bitLen := fun a => Install.ValidAt.extend hp (S.bitLen a)
    replicate := fun a => Install.ValidAt.extend hp (S.replicate .bool a)
    append := fun a => Install.ValidAt.extend hp (S.append .bool a)
    word := he _ _ rfl
    natHeader := he _ _ rfl
    ratHdr := he _ _ rfl
    outWord := he _ _ rfl
    output := he _ _ rfl
    resumeTop := he _ _ rfl }
  have hanswer := answer_valid hlib (he _ _ rfl)
  have hanswerST := Trans.Bounds.answerST_valid hanswer (he _ _ rfl)
  exact ⟨hinitial, hstep, hdone, hinvoke, hquery,
    ho.resumeTop_valid hanswerST, ho.output_valid⟩

end QecReliability.TensorMachine.Program
