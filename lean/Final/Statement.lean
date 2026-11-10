import OracleCost.EncodedSAT
import OracleCost.StoredCodeHashEngineConfidenceCandidate
import PhysicalBridge.PhysicalShapeConfidence
import PhysicalBridge.RationalRepair
import PhysicalBridge.ZeroLengthDispatchCandidate
import WholeWrapperInputEncoding

/-!
# The statement of thm:main at machine level

`MainTheorem` below is a `Prop`, not a theorem. It is the statement of the main
result for an arbitrary external SAT machine that satisfies the premise below.


What the statement says. Fix any external exact-SAT machine `E` satisfying the
paper's SAT premise `EncodedSAT E D PtE PsE T` (a finite multi-tape machine deciding
density-`D` width-three formulas in time `PtE(|q|) * T(vars)` and visited cells
`PsE(|q|)`). Then there is ONE fixed multi-tape machine `M` (chosen before the
instance) such that for every stabilizer presentation `rows` on `n` qubits and
precision parameters `ε = a/b ∈ (0,1]`, `δ = c/d`:

* `M` is run on the structural problem encoding followed by `N` coin bits, where
  `N` is polynomial in the input length `L` (all randomness is read from the
  input tape, so it is counted in space);
* for EVERY coin string, `M` halts with a coefficient vector `v` written on output
  tape `o`, within time `poly(L, 1/ε) * (T(K * (n + incidences + 1)) + 1)` and with
  at most `poly(L)` visited cells summed over all tapes (no `1/ε` factor in space);
  `v` always has the deterministic shape structure (monotone, exact endpoints);
* the optimal-fidelity target is the true optimum over all recovery channels, and
  with probability at least `1 - δ` over uniform coins, the Bernstein curve of `v`
  approximates the optimal fidelity `F(p)` relatively in both tails,
  `|R p - F p| ≤ ε F p` and `|R p - F p| ≤ ε (1 - F p)`, simultaneously for every
  iid erasure probability `p ∈ [0,1]`.

Space counts every visited cell of every tape (`MultiTape.Completed.cells`),
including the input/coin tape. Time counts every transition plus the final halt
inspection (`Completed.time`).
-/

set_option autoImplicit false

namespace QecReliability.Final
open OracleCost OracleCost.MultiTape SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.ConcreteQuantum RationalOutput QecPhysical QecPhysical.Stabilizer
open OracleCost.StoredCodeHashConfidence

/-- Self-delimiting output word of a coefficient vector: numerator then denominator
of every coefficient, in order, each as a `QueryCodec.natHeader` word. -/
def outputWord {r : ℕ} (v : RationalOutput.Vector r) : List Bool :=
  v.entries.toList.flatMap (fun x => QueryCodec.natHeader x.num ++ QueryCodec.natHeader x.den)

/-- The machine input: the paper's structural problem encoding (stabilizer rows,
iid erasure program, `a b c d`) followed by the coin string. -/
def machineInput {n : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ)
    (coins : List Bool) : List Bool :=
  OracleCost.WholeWrapperCandidate.InputEncoding.problemBits rows
    (ZeroLengthDispatch.iidProgram n) a b c d ++ coins

/-- Input length `L` of the manuscript: `n + r` plus the structural encoding length. -/
def paperL {n : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ) : ℕ :=
  OracleCost.WholeWrapperCandidate.InputEncoding.paperLength rows
    (ZeroLengthDispatch.iidProgram n) a b c d

/-- The halted run holds `outputWord v` on tape `o`, head on its first cell. -/
def Outputs {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    (M : Machine k Γ Λ) {bits : List Bool} (run : Completed M bits) (o : Fin (k+1))
    {r : ℕ} (v : RationalOutput.Vector r) : Prop :=
  run.final.core.tapes o = Turing.Tape.mk₁ ((outputWord v).map M.inputSymbol)

open scoped Classical in
/-- thm:main (iid flagged erasure), machine level. See the module docstring. -/
def MainTheorem : Prop :=
  ∀ {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    (E : Machine kE ΓE ΛE) (D : ℕ) (PtE PsE : PolynomialEnvelope) (T : ℕ → ℕ),
    EncodedSAT E D PtE PsE T → Monotone T →
  ∃ (k : ℕ) (Γ Λ : Type) (_ : Fintype Γ) (_ : Inhabited Γ) (_ : Fintype Λ)
    (M : Machine k Γ Λ) (o : Fin (k+1))
    (coinCount : ∀ n : ℕ, List (List (PauliCoord n)) → ℕ → ℕ → ℕ → ℕ → ℕ)
    (Ptime Pspace Pcoins : PolynomialEnvelope) (K : ℕ),
  ∀ (n : ℕ) (rows : List (List (PauliCoord n))) (a b c d : ℕ),
    0 < a → a ≤ b → 0 < c → 0 < d →
    coinCount n rows a b c d ≤ Pcoins.eval (paperL rows a b c d) ∧
    (∀ coins : List Bool, coins.length = coinCount n rows a b c d →
      ∃ (run : Completed M (machineInput rows a b c d coins)) (v : RationalOutput.Vector n),
        Outputs M run o v ∧
        run.time ≤ Ptime.eval (paperL rows a b c d + b / a) *
          (T (K * (n + rowIncidences rows + 1)) + 1) ∧
        run.cells ≤ Pspace.eval (paperL rows a b c d) ∧
        ShapeStructure (rowSpace rows) (circuitMap (ZeroLengthDispatch.iidProgram n))
          v.curve) ∧
    ∀ lift : Lift (rowSpace rows),
      PhysicalTargetOptimality rows (ZeroLengthDispatch.iidProgram n) lift ∧
      (1 - (c:ℝ)/d) * 2 ^ coinCount n rows a b c d ≤
        ((Finset.univ.filter (fun w : Fin (coinCount n rows a b c d) → Bool =>
          ∀ (run : Completed M (machineInput rows a b c d (List.ofFn w)))
            (v : RationalOutput.Vector n), Outputs M run o v →
            AllPhysicalTails rows (ZeroLengthDispatch.iidProgram n) lift ((a:ℝ)/b)
              v.curve)).card : ℝ)

end QecReliability.Final
