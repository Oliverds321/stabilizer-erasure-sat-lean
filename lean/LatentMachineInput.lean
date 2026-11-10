import WholeWrapperInputEncoding

/-! Runtime data/extent layer for the general latent machine extension.
This module does not claim that a finite-tape parser has been implemented.
Physical dimension n and latent dimension r are independent, including zero.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open OracleCost.WholeWrapperCandidate.InputEncoding

def input {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (a b c d : ℕ) (coins : List Bool) : List Bool :=
  problemBits rows C a b c d ++ coins

/-- Includes every shared gate, edge and output occurrence; no bounded-size promise. -/
def circuitExtent {n r : ℕ} (C : Program r n) : ℕ :=
  C.gates + C.circuit.edges + n

def satExtent {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n) : ℕ :=
  n + r + rowIncidences rows + circuitExtent C

theorem input_length {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (a b c d : ℕ) (coins : List Bool) :
    (input rows C a b c d coins).length =
      (problemBits rows C a b c d).length + coins.length := by
  simp [input]

/-- In particular randomness is never silently excluded from input-tape space. -/
theorem input_length_le {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (a b c d : ℕ) (coins : List Bool) :
    (input rows C a b c d coins).length ≤ paperLength rows C a b c d + coins.length := by
  rw [input_length]
  unfold paperLength
  omega

theorem satExtent_le_paperLength {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (a b c d : ℕ) :
    satExtent rows C ≤ paperLength rows C a b c d := by
  have hr := rowsBits_length_lower rows
  have hC := programBits_length_lower C
  unfold satExtent circuitExtent paperLength problemBits
  simp only [List.length_append]
  omega

/-- The counting-key universe is r+2n, never 3n unless r=n. -/
theorem key_extent {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n) :
    keySize n r ≤ 2 * satExtent rows C := by
  unfold keySize satExtent circuitExtent
  omega

/-- Exactly r+1 coefficient slots and twice that many good/bad jobs. -/
def coefficientSlots (r : ℕ) : ℕ := r + 1
def countingJobs (r : ℕ) : ℕ := 2 * coefficientSlots r

theorem zero_latent_slots : coefficientSlots 0 = 1 := rfl
theorem zero_physical_key (r : ℕ) : keySize 0 r = r := by simp [keySize]

end QecReliability.LatentMachine
