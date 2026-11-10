import TensorRepairFL
import TensorMachineInstalled

/-! Fixed installation of the 22-body rational tensor-repair segment. Its slots
are selected before degrees, coefficients, circuit data, or random bits arrive. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairInstalled
open FL FL.Lib TensorMachine.RepairFL
open Trans.Query.Plain (ProgP)

abbrev indices : RepairFL.Indices :=
  ⟨320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341⟩

def segment : FL.Program :=
  [(LinearRepairFL.lesserBody Install.wL.mul Install.wL.le).compile,
   (LinearRepairFL.greaterBody Install.wL.mul Install.wL.le).compile,
   (keyStepBody Install.wL).compile,
   (foldlBody (keyStepF Install.wL indices) indices.keyFold).compile,
   (keyLeBody Install.wL indices).compile,
   (keyEqBody Install.wL indices).compile,
   (lowerStepBody Install.wL indices).compile,
   (foldrBody (lowerStepF Install.wL indices) indices.lowerFold).compile,
   (lowerBody Install.wL indices).compile,
   (upperStepBody Install.wL indices).compile,
   (foldrBody (upperStepF Install.wL indices) indices.upperFold).compile,
   (upperBody Install.wL indices).compile,
   (anchorStepBody Install.wL indices).compile,
   (foldrBody (anchorStepF Install.wL indices) indices.anchorFold).compile,
   (anchorBody Install.wL indices).compile,
   (substStepBody Install.wL indices).compile,
   (foldrBody (substStepF Install.wL indices) indices.substFold).compile,
   (substBody Install.wL indices).compile,
   (pointBody Install.wL indices).compile,
   (outStepBody Install.wL indices).compile,
   (foldrBody (outStepF Install.wL indices) indices.outFold).compile,
   (repairBody Install.wL indices).compile]

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def program : FL.Program := TensorMachine.Installed.program base den density E pg nb ++ segment
local notation "PP" => program base den density E pg nb

theorem program_length : (PP).length = 342 := by
  simp only [program, List.length_append, TensorMachine.Installed.program_length]
  rfl

theorem extends_tensor : Install.Extends
    (TensorMachine.Installed.program base den density E pg nb) PP :=
  Install.extends_append _ _

theorem library_valid : Install.wL.OK PP := by
  have h := TensorMachine.Installed.library_valid base den density E pg nb
  have he := extends_tensor base den density E pg nb
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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem slots : RepairFL.Indices.OK Install.wL indices PP :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem repair_valid : ∀ x, (repairF Install.wL indices).ValidAt PP x :=
  RepairFL.repair_valid (library_valid base den density E pg nb) (slots base den density E pg nb)

theorem repair_computes (data anchors : RawTable) :
    FL.Computes PP indices.repair ((Ty.prod TTable TTable).enc (data,anchors))
      (TOutput.enc (repairR data anchors))
      (max ((repairF Install.wL indices).msize (data,anchors))
        ((Ty.prod TTable TTable).enc (data,anchors)).size)
      ((repairF Install.wL indices).cost (data,anchors))
      ((repairF Install.wL indices).depth (data,anchors)) :=
  RepairFL.repair_computes (library_valid base den density E pg nb)
    (slots base den density E pg nb) data anchors

end QecReliability.TensorMachine.RepairInstalled
