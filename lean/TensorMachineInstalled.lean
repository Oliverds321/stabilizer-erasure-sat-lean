import TensorMachineGridFL
import TensorMachineInput
import LatentControllerInstalled

/-! Fixed installation of the tensor grid and degree-list input parser. The
309 existing bodies remain literally unchanged; eleven additional bodies are
chosen before any runtime class list, circuit, precision, or random tape. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.Installed

open FL FL.Lib Trans.Wire
open Trans.Query.Plain (ProgP)

abbrev gridIndices : GridFL.Indices := ⟨309,310,311,312,313,314,315,316,317⟩
abbrev degreesIdx : ℕ := 318
abbrev parseIdx : ℕ := 319

def segment : FL.Program :=
  [GridFL.prefixStepBody.compile,
   (foldrBody (GridFL.prefixStepF gridIndices) gridIndices.prefixFold).compile,
   (GridFL.prefixBody gridIndices).compile,
   (appendBody GridFL.Row gridIndices.append).compile,
   (GridFL.expandStepBody gridIndices).compile,
   (foldrBody (GridFL.expandStepF gridIndices) gridIndices.expandFold).compile,
   (GridFL.expandBody Install.wL gridIndices).compile,
   (foldrBody (GridFL.expandF Install.wL gridIndices) gridIndices.gridFold).compile,
   (GridFL.gridBody Install.wL gridIndices).compile,
   (ParserFL.degreesBody Install.wL Install.wH LatentMachine.ParserInstalled.indices).compile,
   (ParserFL.parseBody Install.wL Install.wH Install.wP
     LatentMachine.ParserInstalled.indices degreesIdx).compile]

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def program : FL.Program :=
  LatentMachine.ControllerInstalled.program base den density E pg nb ++ segment

local notation "PP" => program base den density E pg nb
local notation "OLD" => Install.prog base den density E pg nb

theorem program_length : (PP).length = 320 := by
  simp only [program, List.length_append, LatentMachine.ControllerInstalled.program_length]
  rfl

theorem extends_controller :
    Install.Extends (LatentMachine.ControllerInstalled.program base den density E pg nb) PP :=
  Install.extends_append _ _

theorem extends_prefix : Install.Extends OLD PP := by
  intro i b hi
  exact extends_controller base den density E pg nb i b
    (LatentMachine.ControllerInstalled.extends_prefix base den density E pg nb i b hi)

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

theorem grid_slots : GridFL.Indices.OK Install.wL gridIndices PP :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem header_slots : Install.wH.OK Install.wL PP := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem row_precision_slots : Install.wP.OK Install.wL Install.wH PP :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem parser_slots : LatentMachine.ParserInstalled.indices.OK
    Install.wL Install.wH Install.wP PP := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem grid_valid : ∀ ds, (GridFL.gridF Install.wL gridIndices).ValidAt PP ds :=
  GridFL.grid_valid (library_valid base den density E pg nb) (grid_slots base den density E pg nb)

set_option maxRecDepth 2000 in
theorem degrees_slot : PP[degreesIdx]? = some
    (ParserFL.degreesBody Install.wL Install.wH LatentMachine.ParserInstalled.indices).compile := rfl

set_option maxRecDepth 2000 in
theorem parse_slot : PP[parseIdx]? = some (ParserFL.parseBody Install.wL Install.wH Install.wP
    LatentMachine.ParserInstalled.indices degreesIdx).compile := rfl

theorem degrees_valid : ∀ bs, (ParserFL.degreesF Install.wL Install.wH
    LatentMachine.ParserInstalled.indices degreesIdx).ValidAt PP bs :=
  ParserFL.degrees_valid (library_valid base den density E pg nb)
    (header_slots base den density E pg nb) (parser_slots base den density E pg nb)
    (degrees_slot base den density E pg nb)

theorem parse_valid : ∀ bs, (ParserFL.parseF Install.wL Install.wH Install.wP
    LatentMachine.ParserInstalled.indices degreesIdx parseIdx).ValidAt PP bs :=
  ParserFL.parse_valid (degrees_valid base den density E pg nb)
    (LatentMachine.ParserFL.parse_valid _ _ _ _ (library_valid base den density E pg nb)
      (header_slots base den density E pg nb) (row_precision_slots base den density E pg nb)
      (parser_slots base den density E pg nb))
    (parse_slot base den density E pg nb)

/-- The actual installed program enumerates every runtime coefficient index. -/
theorem grid_computes (ds : List ℕ) :
    FL.Computes PP gridIndices.grid ((Ty.list Ty.nat).enc ds)
      (GridFL.Table.enc (grid ds))
      (max ((GridFL.gridF Install.wL gridIndices).msize ds) ((Ty.list Ty.nat).enc ds).size)
      ((GridFL.gridF Install.wL gridIndices).cost ds)
      ((GridFL.gridF Install.wL gridIndices).depth ds) :=
  GridFL.grid_computes (library_valid base den density E pg nb)
    (grid_slots base den density E pg nb) ds

/-- The installed finite-data parser evaluates to the exact tensor input payload. -/
theorem parse_computes (bs : List Bool) :
    let F := ParserFL.parseF Install.wL Install.wH Install.wP
      LatentMachine.ParserInstalled.indices degreesIdx parseIdx
    FL.Computes PP parseIdx ((Ty.list Ty.bool).enc bs)
      (ParserFL.ParsedTy.enc (TensorMachine.parse bs))
      (max (F.msize bs) ((Ty.list Ty.bool).enc bs).size) (F.cost bs) (F.depth bs) := by
  dsimp only
  have h := (parse_valid base den density E pg nb bs).computes
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [ParserFL.parseF_den] at h
  exact h

end QecReliability.TensorMachine.Installed
