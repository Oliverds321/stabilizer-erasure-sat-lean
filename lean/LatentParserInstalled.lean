import LatentProgramParserFL
import Install.OK

/-! A concrete fixed extension of the pinned installed program. The nine parser
bodies occupy indices 286–294; no runtime rows, dimensions or circuit choose
indices or code. The existing 286-body prefix remains literally unchanged.
This installs the parser, not yet the latent controller or whole machine. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ParserInstalled
open FL FL.Lib Trans.Wire
open ParserFL
open Trans.Query.Plain (ProgP)

abbrev indices : ParserFL.Indices :=
  ⟨286,287,288,289,290,291,292,293,294⟩

def segment : FL.Program :=
  [(gateBody Install.wL Install.wH).compile,
   (manyStepBody (gateF Install.wL Install.wH indices.gate)).compile,
   (foldlBody (manyStepF (gateF Install.wL Install.wH indices.gate) indices.gateStep)
     indices.gateFold).compile,
   (manyBody Install.wL (gateF Install.wL Install.wH indices.gate)
     indices.gateStep indices.gateFold).compile,
   (manyStepBody (hdrF Install.wL Install.wH)).compile,
   (foldlBody (manyStepF (hdrF Install.wL Install.wH) indices.outputStep)
     indices.outputFold).compile,
   (manyBody Install.wL (hdrF Install.wL Install.wH)
     indices.outputStep indices.outputFold).compile,
   (ParserFL.programBody Install.wL Install.wH indices).compile,
   (ParserFL.parseBody Install.wL Install.wH Install.wP indices).compile]

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def program : FL.Program := Install.prog base den density E pg nb ++ segment

local notation "PP" => program base den density E pg nb
local notation "OLD" => Install.prog base den density E pg nb

theorem program_length : (program base den density E pg nb).length = 295 := by
  simp only [program,Install.prog,List.length_append,Install.seg_length]
  rfl

theorem extends_prefix : Install.Extends OLD PP := Install.extends_append _ _

theorem parser_slots : indices.OK Install.wL Install.wH Install.wP PP :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem library_valid : Install.wL.OK PP := by
  have h := Install.wL_ok base den density E pg nb
  have he := extends_prefix base den density E pg nb
  exact {
    succ := fun x => Install.ValidAt.extend he (h.succ x)
    pred := fun x => Install.ValidAt.extend he (h.pred x)
    add := fun x => Install.ValidAt.extend he (h.add x)
    sub := fun x => Install.ValidAt.extend he (h.sub x)
    le := fun x => Install.ValidAt.extend he (h.le x)
    eq := fun x => Install.ValidAt.extend he (h.eq x)
    mul := fun x => Install.ValidAt.extend he (h.mul x)
    bitLen := fun x => Install.ValidAt.extend he (h.bitLen x)
    dm := fun x hx => Install.ValidAt.extend he (h.dm x hx)
    take := fun t x => Install.ValidAt.extend he (h.take t x)
    drop := fun t x => Install.ValidAt.extend he (h.drop t x)
    range := fun x => Install.ValidAt.extend he (h.range x)
    rev := fun t x => Install.ValidAt.extend he (h.rev t x)
    rep := fun t x => Install.ValidAt.extend he (h.rep t x) }

theorem header_slots : Install.wH.OK Install.wL PP :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem row_precision_slots : Install.wP.OK Install.wL Install.wH PP :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The actual appended program evaluates the general parser on every input. -/
theorem parser_valid : ∀ w,
    (ParserFL.parseF Install.wL Install.wH Install.wP indices).ValidAt PP w :=
  ParserFL.parse_valid Install.wL Install.wH Install.wP indices
    (library_valid base den density E pg nb)
    (header_slots base den density E pg nb)
    (row_precision_slots base den density E pg nb)
    (parser_slots base den density E pg nb)

end QecReliability.LatentMachine.ParserInstalled
