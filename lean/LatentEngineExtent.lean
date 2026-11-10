import LatentMachineInput
import ResourceQuantumQueryBounds

/-! The external SAT rate sees only linear structural extent, independently
of physical/latent dimension equality, precision and serialized bit length. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open OracleCost OracleCost.WholeWrapperCandidate

/-- Uses the same conservative coefficient as the paper-length query bound,
but charges only n+r+row incidences+the full shared circuit extent. -/
theorem engine_variables_satExtent {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (G density : ℕ) :
    QuantumService.engineVariables rows C density (G * keySize n r) ≤
      InputEncoding.queryVariableCoeff G density * (satExtent rows C + 1) := by
  let S := satExtent rows C + 1
  have hn : n ≤ S := by dsimp [S,satExtent,circuitExtent]; omega
  have hr : r ≤ S := by dsimp [S,satExtent,circuitExtent]; omega
  have hi : rowIncidences rows ≤ S := by dsimp [S,satExtent,circuitExtent]; omega
  have hc : C.gates ≤ S := by dsimp [S,satExtent,circuitExtent]; omega
  have h1 : 1 ≤ S := by dsimp [S]; omega
  have hq : keySize n r ≤ 2*S := (key_extent rows C).trans (by dsimp [S]; omega)
  have hg : G * keySize n r ≤ G * (2*S) := Nat.mul_le_mul_left G hq
  have hv : QuantumService.variableBound rows C (G * keySize n r) ≤ (46+2*G)*S := by
    unfold QuantumService.variableBound
    calc
      _ ≤ 46*S + G*(2*S) := by omega
      _ = _ := by ring
  have hm : QuantumService.clauseBound rows C (G * keySize n r) ≤ (180+8*G)*S := by
    unfold QuantumService.clauseBound
    calc
      _ ≤ 180*S + 4*(G*(2*S)) := by omega
      _ = _ := by ring
  unfold QuantumService.engineVariables InputEncoding.queryVariableCoeff
  apply max_le
  · exact hv.trans (Nat.mul_le_mul_right S (by omega))
  · calc
      density * QuantumService.clauseBound rows C (G * keySize n r)
          ≤ density*((180+8*G)*S) := Nat.mul_le_mul_left density hm
      _ = (density*(180+8*G))*S := by ring
      _ ≤ (46+2*G+density*(180+8*G))*S := Nat.mul_le_mul_right S (by omega)

end QecReliability.LatentMachine
