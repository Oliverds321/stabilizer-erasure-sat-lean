import TensorMachineControlLibrary
import TensorMachineInitializerFL
import TensorMachineQueryFL
import Assembly.Main

/-! Final program composition for tensor counting and repair. Eleven fixed
adapter/controller bodies are appended after the actual query and repair
packages. No runtime class list or coefficient index selects program code. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.Program

open FL FL.Lib FL.Tm Trans.Wire Trans.Control
open Trans.Query.Plain (ProgP)

abbrev TX := ContextFL.TX

def endpointBody : Tm [.prod TX .bool] TR :=
  .app (LatentMachine.WrappersFL.endpointWF Install.wL
    LatentMachine.WrappersInstalled.indices Install.yR)
    (.pair (.snd (.snd (.fst v0))) (.snd v0))

def endpointF (idx : ℕ) := bodySig idx endpointBody

variable (source : FL.Program) (Q : FnSig QueryFL.CompilerArg (.list .bool))
  (repair : FnSig ControllerFL.RepairArg (.list TR))
  (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def compiler := QueryFL.compileF Install.wL Install.wC Q (Install.hashFn E pg nb)
  base den density 16 source.length

def controller : Ix TX := ControlLibrary.indices
  (compiler source Q base den density E pg nb) (endpointF (source.length + 1))
  (source.length + 2) (source.length + 3) (source.length + 4) (source.length + 5)

def context := ContextFL.contextF Install.wL Install.wA Installed.gridIndices
  Install.paramsFn base den 295 13 (source.length + 9)

def initializer := InitializerFL.initialF
  (ParserFL.parseF Install.wL Install.wH Install.wP LatentMachine.ParserInstalled.indices
    Installed.degreesIdx Installed.parseIdx)
  (context source base den) Install.yI (source.length + 10)

def tensorStep := ControllerFL.stepF (controller source Q base den density E pg nb) repair
  (source.length + 6) (source.length + 7) (source.length + 8)

def segment : FL.Program :=
  let x := controller source Q base den density E pg nb
  [(QueryFL.compileBody Install.wL Install.wC Q (Install.hashFn E pg nb)
      base den density 16).compile,
   endpointBody.compile,
   (compilePBody x).compile,
   (endpointZeroBody x).compile,
   (endpointOneBody x).compile,
   (LatentMachine.EndpointControllerFL.dispatchBody x).compile,
   (ControllerFL.finishBody repair).compile,
   (ControllerFL.dispatchBody x repair (source.length + 6)).compile,
   (ControllerFL.stepBody x repair (source.length + 6) (source.length + 7)).compile,
   (ContextFL.contextBody Install.wL Install.wA Installed.gridIndices Install.paramsFn
      base den 295 13).compile,
   (InitializerFL.initialBody
      (ParserFL.parseF Install.wL Install.wH Install.wP LatentMachine.ParserInstalled.indices
        Installed.degreesIdx Installed.parseIdx)
      (context source base den) Install.yI).compile]

def program : FL.Program := source ++ segment source Q repair base den density E pg nb

def assemblyIndices : Assembly.Indices :=
  ⟨source.length + 10, source.length + 8, 277, 278, 279, 285, 284⟩

theorem segment_length : (segment source Q repair base den density E pg nb).length = 11 := rfl

theorem program_length : (program source Q repair base den density E pg nb).length =
    source.length + 11 := by rw [program, List.length_append, segment_length]

theorem extends_source : Install.Extends source (program source Q repair base den density E pg nb) :=
  Install.extends_append _ _

structure Slots (P : FL.Program) : Prop where
  compiler : P[source.length]? = some (QueryFL.compileBody Install.wL Install.wC Q
    (Install.hashFn E pg nb) base den density 16).compile
  endpoint : P[source.length + 1]? = some endpointBody.compile
  compileP : P[source.length + 2]? = some (compilePBody (controller source Q base den density E pg nb)).compile
  endpointZero : P[source.length + 3]? = some (endpointZeroBody (controller source Q base den density E pg nb)).compile
  endpointOne : P[source.length + 4]? = some (endpointOneBody (controller source Q base den density E pg nb)).compile
  legacyDispatch : P[source.length + 5]? = some
    (LatentMachine.EndpointControllerFL.dispatchBody (controller source Q base den density E pg nb)).compile
  finish : P[source.length + 6]? = some (ControllerFL.finishBody repair).compile
  dispatch : P[source.length + 7]? = some
    (ControllerFL.dispatchBody (controller source Q base den density E pg nb) repair (source.length + 6)).compile
  step : P[source.length + 8]? = some
    (ControllerFL.stepBody (controller source Q base den density E pg nb) repair
      (source.length + 6) (source.length + 7)).compile
  context : P[source.length + 9]? = some (ContextFL.contextBody Install.wL Install.wA Installed.gridIndices
    Install.paramsFn base den 295 13).compile
  initial : P[source.length + 10]? = some (InitializerFL.initialBody
    (ParserFL.parseF Install.wL Install.wH Install.wP LatentMachine.ParserInstalled.indices
      Installed.degreesIdx Installed.parseIdx) (Program.context source base den) Install.yI).compile

theorem slots : Slots source Q repair base den density E pg nb
    (program source Q repair base den density E pg nb) := by
  constructor <;> simp [program, segment, List.getElem?_append_right]

/-- The same generic register/tape assembly executes these concrete seven indices. -/
noncomputable def machine {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    (sat : OracleCost.MultiTape.Machine k Γ Λ) :=
  Assembly.theMachine sat (program source Q repair base den density E pg nb)
    (assemblyIndices source)

end QecReliability.TensorMachine.Program
