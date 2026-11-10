import TensorMachineLowering
import GeneralInstalled

/-! The fixed 387-body general-circuit multiclass program: the 384-body tensor
program with the three general-callback bodies inserted before the controller
segment, and the general callback in place of the full repair. -/

set_option autoImplicit false
namespace QecReliability.TensorMachineG.Concrete
open QecReliability.TensorMachine
open FL FL.Lib Trans.Wire
open Trans.Query.Plain (ProgP)

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

abbrev source := GeneralInstalled.program base den density E pg nb
abbrev query := QueryInstalled.query
abbrev repair := GeneralInstalled.callback

def program : FL.Program := Program.program (source base den density E pg nb)
  query repair base den density E pg nb

def indices : Assembly.Indices := Program.assemblyIndices (source base den density E pg nb)

theorem program_length : (program base den density E pg nb).length = 387 := by
  simp only [program, Program.program_length, source, GeneralInstalled.program_length]

theorem init_index : (indices base den density E pg nb).init = 386 := by
  simp only [indices,Program.assemblyIndices,source,GeneralInstalled.program_length]

theorem step_index : (indices base den density E pg nb).step = 384 := by
  simp only [indices,Program.assemblyIndices,source,GeneralInstalled.program_length]

/-- Every callback used by the assembly executes its literal installed code. -/
theorem valid (hHash : ∀ a, (Install.hashFn E pg nb).ValidAt
    (Install.prog base den density E pg nb) a) :
    Program.Valid (source base den density E pg nb) query repair base den density E pg nb :=
  Program.valid _ _ _ _ _ _ _ _ _
    (GeneralInstalled.extends_tensor base den density E pg nb)
    (GeneralInstalled.query_valid base den density E pg nb)
    (GeneralInstalled.callback_valid base den density E pg nb) hHash

/-- Finite-tape machine with a fixed SAT engine embedded on disjoint tapes. -/
noncomputable def machine {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    (sat : OracleCost.MultiTape.Machine k Γ Λ) :=
  Assembly.theMachine sat (program base den density E pg nb) (indices base den density E pg nb)

end QecReliability.TensorMachineG.Concrete
