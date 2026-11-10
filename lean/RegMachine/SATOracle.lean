import RegMachine.RegMap
import OracleCost.EncodedSAT

/-!
# The SAT engine as an oracle

From an `EncodedSAT E D Ptime Pspace T` machine and a query-length cap `L` we build an
`OracleSpec` whose allowed queries are the canonical encoded requests of length `≤ L`,
whose answer on `encode request` is satisfiability of the request, whose abstract cost
is the engine's actual `time + cells` on that query, and whose engine space is bounded
by `Pspace.eval L` (`satOracle_spec`). Plugging it into `oracle_completed` gives
`sat_program_completed`: register programs that call the SAT engine compile to a
single `MultiTape.Machine` embedding `E`, with the stated time and space bounds.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost QecReliability.OracleCost.MultiTape
open QecReliability.OracleCost.MultiTape.InjectiveTapeLift Turing

variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- Oracle answering with the (unique) completed run of `E`, restricted to canonical
queries of length at most `L`. -/
noncomputable def satOracle (E : Machine kE ΓE ΛE) (D L : ℕ) : OracleSpec := by
  classical
  exact
    { oracle := fun w => if h : Nonempty (Completed E w) then (Classical.choice h).output else false
      ocost := fun w => if h : Nonempty (Completed E w) then
        (Classical.choice h).time + (Classical.choice h).cells else 0
      qok := fun w => CanonicalDensityInput D w ∧ w.length ≤ L }

theorem satOracle_run (E : Machine kE ΓE ΛE) (D L : ℕ) {w : List Bool} (run : Completed E w) :
    (satOracle E D L).oracle w = run.output ∧
      (satOracle E D L).ocost w = run.time + run.cells := by
  have h : Nonempty (Completed E w) := ⟨run⟩
  have hu := Completed.unique (Classical.choice h) run
  simp only [satOracle, dif_pos h]
  refine ⟨hu.2.2.2, ?_⟩
  rw [hu.2.1, hu.2.2.1]

variable {D : ℕ} {Ptime Pspace : PolynomialEnvelope} {T : ℕ → ℕ}

/-- The SAT oracle: correct answers, cost = actual engine time + cells, and engine
space bounded by `Pspace.eval L` on every allowed query. -/
theorem satOracle_spec {E : Machine kE ΓE ΛE} (spec : EncodedSAT E D Ptime Pspace T) (L : ℕ) :
    (∀ request : SATRequest, D * request.formula.length ≤ request.varCount →
      ((satOracle E D L).oracle (QueryCodec.encode request) = true ↔
          ∃ a, PrefixCNF.eval request.formula a = true) ∧
        (satOracle E D L).ocost (QueryCodec.encode request) ≤
          Ptime.eval (QueryCodec.encode request).length * T request.varCount +
            Pspace.eval (QueryCodec.encode request).length) ∧
    (∀ w, (satOracle E D L).qok w → ∃ run : Completed E w,
      run.output = (satOracle E D L).oracle w ∧
      run.time + run.cells ≤ (satOracle E D L).ocost w ∧ run.cells ≤ Pspace.eval L) := by
  refine ⟨fun request hd => ?_, fun w hw => ?_⟩
  · obtain ⟨run, hout, htime, hcells⟩ := spec.complete request hd
    obtain ⟨ho, hc⟩ := satOracle_run E D L run
    rw [ho, hc]
    exact ⟨hout, Nat.add_le_add htime hcells⟩
  · obtain ⟨⟨request, hd, rfl⟩, hL⟩ := hw
    obtain ⟨run, -, -, hcells⟩ := spec.complete request hd
    obtain ⟨ho, hc⟩ := satOracle_run E D L run
    exact ⟨run, ho.symm, hc.ge, hcells.trans (Pspace.monotone hL)⟩

variable {k : ℕ}

/-- **SAT-calling register programs on one multi-tape machine.** -/
theorem sat_program_completed {R n S L : ℕ} {E : Machine kE ΓE ΛE}
    (spec : EncodedSAT E D Ptime Pspace T) (ρ : Embedding R k) (e : Embedding kE k)
    (hρ0 : ρ 0 = 0) (hdisj : ∀ r j, ρ r ≠ e j)
    (prog : Prog (OInstr (R + 1)) n) {bits : List Bool} {N C : ℕ} {t : Regs (R + 1)} {b : Bool}
    (h : Exec (oracleSem (satOracle E D L) (R + 1) (fun _ => True)) prog (Fits S) prog.entry
      (inputRegs bits) N C t b) :
    ∃ run : Completed (oracleMachine E e (prog.map ρ)) bits,
      run.output = b ∧ run.time ≤ (3 * kE + 5) * C + N ∧
      run.cells ≤ (k + 1) * (2 * max S (Pspace.eval L) + 3) ∧
      (∀ r, run.final.core.tapes (ρ r) = Tape.mk₁ ((t r).map RegSyms.sym)) :=
  let ⟨run, h1, h2, h3, h4, _, _⟩ :=
    oracle_completed E ρ e hρ0 hdisj (satOracle E D L) (satOracle_spec spec L).2 prog h
  ⟨run, h1, h2, h3, h4⟩

end QecReliability.RegMachine
