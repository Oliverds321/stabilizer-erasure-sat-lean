import ExternalSATObservedTransport
import OracleCost.QueryCodec
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler

/-! An actual finite-controller component of dimension-aware preprocessing.
Input is ONE already isolated fixed-width binary word, not a whole query.
Output is the exact external unary natural field on a physical tape. The
halting Boolean is the output head, not a SAT decision. Pending compilation. -/
namespace QecReliability.ExternalSATBridge.PrimitiveTransport

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open scoped BigOperators

/-- All native observations count at most one new cell per tape per step. -/
theorem observed_cells_step {M : Computation.PrimitiveMachine} {s s' : TargetObserved M}
    (hs : MultiTape.observedStep (machine M) s = some s') :
    MultiTape.visitedCells s' ≤ MultiTape.visitedCells s + (M.tapeCount + 1) := by
  have hcard : ∀ i, (s'.visited i).card ≤ (s.visited i).card + 1 := by
    intro i
    rw [observed_visited_step hs]
    exact Finset.card_insert_le _ _
  calc
    MultiTape.visitedCells s' ≤ ∑ i, ((s.visited i).card + 1) :=
      Finset.sum_le_sum (fun i _ => hcard i)
    _ = MultiTape.visitedCells s + (M.tapeCount + 1) := by
      simp [Finset.sum_add_distrib, MultiTape.visitedCells]

theorem observed_trace_cells {M : Computation.PrimitiveMachine}
    {s s' : TargetObserved M} {steps : ℕ}
    (tr : MultiTape.Trace (machine M) s steps s') :
    MultiTape.visitedCells s' ≤ MultiTape.visitedCells s + steps * (M.tapeCount + 1) := by
  induction tr with
  | nil s => simp
  | @cons s t u n hs ht ih =>
    have hstep := observed_cells_step hs
    nlinarith

theorem initial_cells_le (M : Computation.PrimitiveMachine) (bits : List Bool) :
    MultiTape.visitedCells (MultiTape.initialObserved (machine M) bits) ≤
      bits.length + (M.tapeCount + 1) := by
  let s := MultiTape.initialObserved (machine M) bits
  have hzero : (s.visited 0).card ≤ bits.length + 1 := by
    change (insert (0 : ℤ) ((Finset.range bits.length).image (fun j : ℕ => (j : ℤ)))).card ≤ _
    have hi := Finset.card_image_le (s := Finset.range bits.length) (f := fun j : ℕ => (j : ℤ))
    have hc := Finset.card_insert_le (0 : ℤ)
      ((Finset.range bits.length).image (fun j : ℕ => (j : ℤ)))
    rw [Finset.card_range] at hi
    omega
  have hother : ∀ i : Fin M.tapeCount, (s.visited i.succ).card = 1 := by
    intro i
    simp [s, MultiTape.initialObserved]
  calc
    MultiTape.visitedCells s = (s.visited 0).card + M.tapeCount := by
      simp [MultiTape.visitedCells, Fin.sum_univ_succ, hother]
    _ ≤ (bits.length + 1) + M.tapeCount := Nat.add_le_add_right hzero _
    _ = bits.length + (M.tapeCount + 1) := by omega

theorem binary_word_value (k n : ℕ) (hn : n < 2 ^ k) :
    CounterPrograms.value (QueryCodec.word k n) = n := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    rfl
  | succ k ih =>
    have hdiv : n / 2 < 2 ^ k := by rw [pow_succ] at hn; omega
    simp only [QueryCodec.word, CounterPrograms.value, ih (n / 2) hdiv]
    have hmod := Nat.mod_lt n (by omega : 0 < 2)
    by_cases hm : n % 2 = 1 <;> simp [hm] <;> omega

noncomputable abbrev natFieldEncoder : Computation.PrimitiveMachine :=
  GuardedCompiler.primitive CounterConversions.encodeNatProgram

@[simp] theorem natFieldEncoder_tapeCount : natFieldEncoder.tapeCount = 3 := rfl

def natFieldOutput : Fin natFieldEncoder.tapeCount :=
  ⟨1, by rw [natFieldEncoder_tapeCount]; decide⟩

theorem natField_initial (bits : List Bool) :
    (CounterConversions.state CounterConversions.zeroRegs bits []).withPC
      (some CounterConversions.encodeNatProgram.entry) =
      BitProgram.initial CounterConversions.encodeNatProgram bits := by
  unfold CounterConversions.state CounterConversions.zeroRegs
    StructuredProgram.State.withPC BitProgram.initial
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The external compiler gives a real physical unary word with at most 224
steps per product of input value+1 and binary width+1; not an exact time. -/
theorem natField_primitive_run (k n : ℕ) (hn : n < 2 ^ k) :
    ∃ steps final,
      Computation.Trace natFieldEncoder.step steps
        (natFieldEncoder.init (QueryCodec.word k n)) final ∧
      steps ≤ 224 * (n + 1) * (k + 1) ∧
      final.state = .inl ((Encoding.encodeNat n).head?.getD false) ∧
      final.tapes natFieldOutput =
        Turing.Tape.mk₁ ((Encoding.encodeNat n).map some) := by
  let bits := QueryCodec.word k n
  have hrun := CounterConversions.encodeNat_runs CounterConversions.zeroRegs bits
  rw [natField_initial] at hrun
  obtain ⟨final, ⟨steps, hsteps, htrace⟩, hhalt, hout⟩ :=
    GuardedCompiler.primitive_word_execution CounterConversions.encodeNatProgram hrun rfl
      (show (CounterConversions.state CounterConversions.zeroRegs []
        (Encoding.encodeNat (CounterPrograms.value bits))).stacks
          CounterConversions.encodeNatProgram.outputStack =
          Encoding.encodeNat (CounterPrograms.value bits) from rfl)
  refine ⟨steps, final, htrace, ?_, ?_, ?_⟩
  · have hb : 7 * CounterConversions.runtimeBound bits = 224 * (n + 1) * (k + 1) := by
      simp only [CounterConversions.runtimeBound, bits, binary_word_value k n hn,
        QueryCodec.word_length]
      ring
    rw [hb] at hsteps
    exact hsteps
  · simpa [bits, binary_word_value k n hn] using hhalt
  · have hindex : (CounterConversions.encodeNatProgram.outputStack :
        Fin natFieldEncoder.tapeCount) = natFieldOutput := by
      apply Fin.ext
      rfl
    simpa [bits, binary_word_value k n hn, hindex] using hout

/-- The adapted machine has four tapes. Source output tape1 becomes native
slot1=tape2; native tape1 is idle. The result is one encoded natural field,
not a decoded/normalized CNF and not a SAT answer. -/
theorem natField_completed (k n : ℕ) (hn : n < 2 ^ k) :
    ∃ run : MultiTape.Completed (machine natFieldEncoder) (QueryCodec.word k n),
      run.time ≤ 224 * (n + 1) * (k + 1) + 1 ∧
      run.cells ≤ k + 4 + 4 * (224 * (n + 1) * (k + 1)) ∧
      run.final.core.tapes (slot natFieldEncoder natFieldOutput) =
        Turing.Tape.mk₁ ((Encoding.encodeNat n).map some) ∧
      run.output = (Encoding.encodeNat n).head?.getD false := by
  obtain ⟨steps, final, htrace, hsteps, hhalt, hout⟩ := natField_primitive_run k n hn
  obtain ⟨located, hlocated, hconfig⟩ := locatedTrace_lift
    (c := locatedInit natFieldEncoder (QueryCodec.word k n)) htrace
  obtain ⟨s, hs, hrel⟩ := lift_observedTrace natFieldEncoder hlocated
    (MultiTape.initialObserved (machine natFieldEncoder) (QueryCodec.word k n))
    (related_initial natFieldEncoder (QueryCodec.word k n))
  have hproj : project natFieldEncoder s.core = final := hrel.core.trans hconfig
  have hstate : s.core.label = .inl ((Encoding.encodeNat n).head?.getD false) :=
    (congrArg Computation.PrimitiveMachine.Cfg.state hproj).trans hhalt
  let run : MultiTape.Completed (machine natFieldEncoder) (QueryCodec.word k n) :=
    ⟨steps, s, _, hs, answer_of_halting_label natFieldEncoder s.core _ hstate⟩
  have hspace := observed_trace_cells hs
  have hinitial := initial_cells_le natFieldEncoder (QueryCodec.word k n)
  have htapes := congrArg (fun c : natFieldEncoder.Cfg => c.tapes natFieldOutput) hproj
  refine ⟨run, ?_, ?_, htapes.trans hout, rfl⟩
  · change steps + 1 ≤ _
    omega
  · change MultiTape.visitedCells s ≤ _
    change MultiTape.visitedCells s ≤
      MultiTape.visitedCells (MultiTape.initialObserved (machine natFieldEncoder)
        (QueryCodec.word k n)) + steps * 4 at hspace
    have hi : MultiTape.visitedCells (MultiTape.initialObserved (machine natFieldEncoder)
        (QueryCodec.word k n)) ≤ k + 4 := by
      simpa only [QueryCodec.word_length, natFieldEncoder_tapeCount] using hinitial
    nlinarith

end QecReliability.ExternalSATBridge.PrimitiveTransport
