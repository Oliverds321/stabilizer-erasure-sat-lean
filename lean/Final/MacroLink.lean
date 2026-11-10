import Final.Statement
import Final.Macro

/-!
# Glue between `Final.Statement` and `Final.Macro`

Definitional identifications the bridge theorem needs: the paper input length,
and the coin string on the input tape versus the stored random word.
-/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace QecReliability.Final
open OracleCost OracleCost.WholeWrapperCandidate SharedCircuit
open SharedCircuit.FixedLocalEmitter.AllLength FiniteLocalSelectorCandidate

theorem paperL_eq_macroL {n : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ) :
    paperL rows a b c d = macroL rows a b c d := rfl

theorem problemBits_length_le_paperL {n : ℕ} (rows : List (List (PauliCoord n)))
    (a b c d : ℕ) :
    (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d).length ≤
      paperL rows a b c d := by
  unfold paperL InputEncoding.paperLength
  omega

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : CertifiedParity (512*t) (64*t) t)

/-- For `n = k+1`, the coins on the tape are literally the cells of the stored word. -/
theorem machineInput_coinWord {k : ℕ} (rows : List (List (PauliCoord (k+1)))) (a b c d : ℕ)
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) :
    machineInput rows a b c d (List.ofFn coins) =
      InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram (k+1)) a b c d ++
        (show CodeHash.FiniteRandomTape.InputWord (coinBits hD hd A c d (k+1)) from
          coinWord hD hd A c d (k+1) coins).cells := by
  rw [coinWord_cells]
  rfl

/-- The number of coins is polynomial in `paperL` (and `0` for `n = 0`). -/
theorem coinBits_le_paperL {n : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ)
    (ha : 0 < a) (hc : 0 < c) :
    coinBits hD hd A c d n ≤
      (6 * paperL rows a b c d + 5) * (seedConstant hD hd A * (2 * paperL rows a b c d)) :=
  randomBits_input_polynomial hD hd A a b c d ha hc n rows

end QecReliability.Final
