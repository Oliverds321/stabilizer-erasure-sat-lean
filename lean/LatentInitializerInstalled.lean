import LatentParserInstalled
import LatentInitializerFL

/-! Concrete context/terminal/initializer installation at fixed slots295–297.
All their actual callees are discharged from the unchanged installed prefix;
there is no assumed initializer or parser contract. This does not yet replace
the old controller's external query functions or prove a whole-machine bound. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.InitializerInstalled
open FL FL.Lib Trans.Wire
open Trans.Query.Plain (ProgP)
open Trans.Control (bodySig_valid)

abbrev ctxIdx : ℕ := 295
abbrev terminalIdx : ℕ := 296
abbrev topIdx : ℕ := 297

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def segment : FL.Program :=
  [(ContextFL.contextBody Install.wL Install.wA Install.paramsFn base den).compile,
   InitializerFL.terminalBody.compile,
   (InitializerFL.initialBody Install.wL Install.wH Install.wP ParserInstalled.indices
     Install.wA Install.yI Install.yR Install.paramsFn base den ctxIdx terminalIdx).compile]

def program : FL.Program :=
  ParserInstalled.program base den density E pg nb ++ segment base den

local notation "PP" => program base den density E pg nb
local notation "OLD" => Install.prog base den density E pg nb

theorem extends_parser : Install.Extends (ParserInstalled.program base den density E pg nb) PP :=
  Install.extends_append _ _

theorem extends_prefix : Install.Extends OLD PP := by
  intro i b hi
  exact extends_parser base den density E pg nb i b
    (ParserInstalled.extends_prefix base den density E pg nb i b hi)

theorem program_length : (program base den density E pg nb).length = 298 := by
  simp only [program,List.length_append,ParserInstalled.program_length]
  rfl

set_option maxRecDepth 4096 in
theorem context_slot : PP[ctxIdx]? = some
    (ContextFL.contextBody Install.wL Install.wA Install.paramsFn base den).compile := rfl

set_option maxRecDepth 4096 in
theorem terminal_slot : PP[terminalIdx]? = some InitializerFL.terminalBody.compile := rfl

set_option maxRecDepth 4096 in
theorem initializer_slot : PP[topIdx]? = some
    (InitializerFL.initialBody Install.wL Install.wH Install.wP ParserInstalled.indices
      Install.wA Install.yI Install.yR Install.paramsFn base den ctxIdx terminalIdx).compile := rfl

theorem context_valid : ∀ x,
    (ContextFL.contextF Install.wL Install.wA Install.paramsFn base den ctxIdx).ValidAt PP x := by
  have hL := Install.wL_ok base den density E pg nb
  have he := extends_prefix base den density E pg nb
  have hadd := fun x => Install.ValidAt.extend he (hL.add x)
  have hcell := fun x => Install.ValidAt.extend he
    (Trans.Wire.cellB_valid hL Install.wA_ok x)
  have hrep := fun x => Install.ValidAt.extend he
    (Trans.Wire.repB_valid hL Install.wA_ok x)
  have hseed := fun x => Install.ValidAt.extend he
    (Trans.Wire.seedB_valid hL Install.params_ok Install.wA_ok x)
  intro x
  apply bodySig_valid (context_slot base den density E pg nb)
  simp [ContextFL.contextBody,ContextFL.pN,ContextFL.pR,ContextFL.pRows,
    ContextFL.pProgram,ContextFL.pA,ContextFL.pB,ContextFL.pC,ContextFL.pD,
    ContextFL.pCoins,tm_simp,hadd,hcell,hrep,hseed]

/-- Concrete installed initializer, valid at every raw input word. -/
theorem initializer_valid : ∀ w,
    (InitializerFL.initialF Install.wL Install.wH Install.wP ParserInstalled.indices
      Install.wA Install.yI Install.yR Install.paramsFn base den ctxIdx terminalIdx topIdx).ValidAt PP w := by
  have he := extends_prefix base den density E pg nb
  have hp := fun w => Install.ValidAt.extend (extends_parser base den density E pg nb)
    (ParserInstalled.parser_valid base den density E pg nb w)
  have hc := context_valid base den density E pg nb
  have hy := fun x => Install.ValidAt.extend he (Trans.Control.init_valid Install.yI_ok x)
  have hz := fun x => Install.ValidAt.extend he (Trans.Control.endpoint_valid Install.yR_ok x)
  have ht : ∀ x, (InitializerFL.terminalF terminalIdx).ValidAt PP x := fun x =>
    bodySig_valid (terminal_slot base den density E pg nb)
      (by simp [InitializerFL.terminalBody,tm_simp])
  intro w
  apply bodySig_valid (initializer_slot base den density E pg nb)
  simp only [InitializerFL.initialBody,tm_simp,hp,hc,hy,hz,ht,true_and]
  split_ifs <;> trivial

end QecReliability.LatentMachine.InitializerInstalled
