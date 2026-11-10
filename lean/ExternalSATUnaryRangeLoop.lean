import ExternalSATCandidateChild

/-! A physical unary-controlled range loop. The supplied visit command is fixed
syntax; its actual Eval traces are composed below. Semantic indices occur only
in the proof. This generic loop is not a completed canonical frontend. -/
namespace QecReliability.ExternalSATBridge.UnaryRangeLoop

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

abbrev Frame (s : ℕ) := Fin (s + 2) → List Bool

def zeroRegs : Fin 16 → Bool := fun _ => false

def store {s : ℕ} (counter code : List Bool) (frame : Frame s) :
    StructuredProgram.State 16 (s + 2) :=
  ⟨zeroRegs, Function.update (Function.update frame 0 counter) 1 code⟩

def observed {s : ℕ} (bit : Bool) (counter code : List Bool) (frame : Frame s) :
    StructuredProgram.State 16 (s + 2) :=
  ⟨Function.update zeroRegs 0 bit, (store counter code frame).stacks⟩

def remaining : ℕ → List Bool
  | 0 => []
  | n + 1 => Encoding.encodeNat n

def gate {s : ℕ} : StructuredCalls.Cmd 16 (s + 2) := .base
  (.seq (.atom (.pop 0 0 1)) (.atom (.set 1 false)))

theorem gate_word {s : ℕ} (b : Bool) (tail code : List Bool) (frame : Frame s) :
    Eval gate 2 (store (b :: tail) code frame) (observed b tail code frame) := by
  apply Eval.base
  have h := (StructuredProgram.Eval.atom (.pop (0 : Fin (s + 2)) (0 : Fin 16) 1)
    (store (b :: tail) code frame)).seq
      (StructuredProgram.Eval.atom (.set (1 : Fin 16) false) _)
  have hr : Function.update (readRegs zeroRegs 0 1 (some b)) 1 false =
      Function.update zeroRegs 0 b := by
    funext j; fin_cases j <;> simp [readRegs, zeroRegs]
  have hs : Function.update (Function.update (Function.update frame 0 (b :: tail)) 1 code)
      0 tail = Function.update (Function.update frame 0 tail) 1 code := by
    funext j
    by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;> simp_all
  simpa [store, observed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hr, hs] using h

theorem gate_nat {s : ℕ} (n : ℕ) (code : List Bool) (frame : Frame s) :
    Eval gate 2 (store (Encoding.encodeNat n) code frame)
      (observed (decide (0 < n)) (remaining n) code frame) := by
  cases n with
  | zero => simpa [Encoding.encodeNat, remaining] using gate_word false [] code frame
  | succ n => simpa [Encoding.encodeNat, remaining, List.replicate_succ] using
      gate_word true (Encoding.encodeNat n) code frame

def clearTest {s : ℕ} : StructuredCalls.Cmd 16 (s + 2) := .base (.atom (.set 0 false))

theorem clear_eval {s : ℕ} (counter code : List Bool) (frame : Frame s) :
    Eval clearTest 1 (observed true counter code frame) (store counter code frame) := by
  apply Eval.base
  have h := StructuredProgram.Eval.atom (.set (0 : Fin 16) false)
    (observed true counter code frame)
  have hr : Function.update (Function.update zeroRegs 0 true) 0 false = zeroRegs := by
    funext j; fin_cases j <;> simp [zeroRegs]
  simpa [store, observed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hr] using h

def advance {s : ℕ} : StructuredCalls.Cmd 16 (s + 2) := .base
  (.seq (.atom (.set 0 true)) (.seq (.atom (.push 1 0)) (.atom (.set 0 false))))

theorem advance_eval {s : ℕ} (counter code : List Bool) (frame : Frame s) :
    Eval advance 3 (store counter code frame) (store counter (true :: code) frame) := by
  apply Eval.base
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 16) true) (store counter code frame)).seq
    ((StructuredProgram.Eval.atom (.push (1 : Fin (s + 2)) (0 : Fin 16)) _).seq
      (StructuredProgram.Eval.atom (.set (0 : Fin 16) false) _))
  have hr : Function.update (Function.update zeroRegs 0 true) 0 false = zeroRegs := by
    funext j; fin_cases j <;> simp [zeroRegs]
  simpa [store, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hr] using h

def iteration {s : ℕ} (visit : StructuredCalls.Cmd 16 (s + 2)) :
    StructuredCalls.Cmd 16 (s + 2) := .seq clearTest (.seq visit (.seq advance gate))
def loop {s : ℕ} (visit : StructuredCalls.Cmd 16 (s + 2)) :
    StructuredCalls.Cmd 16 (s + 2) := .while 0 (iteration visit)
def command {s : ℕ} (visit : StructuredCalls.Cmd 16 (s + 2)) :
    StructuredCalls.Cmd 16 (s + 2) := .seq gate (loop visit)

/-- The callback hypothesis supplies REAL traces of one fixed command at each
visited state. It is a composition premise, not an unmeasured runtime oracle. -/
theorem loop_eval {s : ℕ} (visit : StructuredCalls.Cmd 16 (s + 2))
    (n a K : ℕ) (frames : ℕ → Frame s)
    (hvisit : ∀ i, i < n → ∃ k, k ≤ K ∧
      Eval visit k (store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames i))
        (store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames (i + 1)))) :
    ∃ k, k ≤ n * (K + 7) + 1 ∧
      Eval (loop visit) k
        (observed (decide (0 < n)) (remaining n) (Encoding.encodeNat a) (frames 0))
        (store [] (Encoding.encodeNat (a + n)) (frames n)) := by
  induction n generalizing a frames with
  | zero =>
    refine ⟨1, by omega, ?_⟩
    have h : Eval (loop visit) 1
        (observed false [] (Encoding.encodeNat a) (frames 0))
        (observed false [] (Encoding.encodeNat a) (frames 0)) := .while_false (by simp [observed])
    have hr : Function.update zeroRegs 0 false = zeroRegs := by
      funext j; fin_cases j <;> simp [zeroRegs]
    simpa [observed, store, remaining, hr] using h
  | succ n ih =>
    obtain ⟨k, hk, hv⟩ := hvisit 0 (by omega)
    simp only [Nat.add_zero, Nat.sub_zero, Nat.add_sub_cancel] at hv
    have ha : true :: Encoding.encodeNat a = Encoding.encodeNat (a + 1) := by
      simp [Encoding.encodeNat, List.replicate_succ]
    have hi := (clear_eval (Encoding.encodeNat n) (Encoding.encodeNat a) (frames 0)).seq
      (hv.seq ((advance_eval (Encoding.encodeNat n) (Encoding.encodeNat a) (frames 1)).seq
        (gate_nat n (true :: Encoding.encodeNat a) (frames 1))))
    rw [ha] at hi
    have htail : ∀ i, i < n → ∃ k, k ≤ K ∧
        Eval visit k
          (store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + 1 + i)) (frames (i + 1)))
          (store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + 1 + i))
            (frames (i + 1 + 1))) := by
      intro i hi
      obtain ⟨j, hj, he⟩ := hvisit (i + 1) (by omega)
      have hn : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
      have haa : a + (i + 1) = a + 1 + i := by omega
      exact ⟨j, hj, by simpa only [hn, haa] using he⟩
    obtain ⟨j, hj, ht⟩ := ih (a + 1) (fun i => frames (i + 1)) htail
    have hh := Eval.while_true (by simp [observed] :
      (observed true (Encoding.encodeNat n) (Encoding.encodeNat a) (frames 0)).regs 0 = true) hi ht
    refine ⟨(1 + (k + (3 + 2))) + j + 1, ?_, ?_⟩
    · nlinarith
    · have haa : a + 1 + n = a + (n + 1) := by omega
      simpa only [loop, iteration, remaining, Nat.zero_lt_succ, decide_true, haa] using hh

/-- Physical counter terminator is consumed. The code ends at a+n and must be
cleared by a caller before it is used as an absent candidate-slot sentinel. -/
theorem eval_range {s : ℕ} (visit : StructuredCalls.Cmd 16 (s + 2))
    (n a K : ℕ) (frames : ℕ → Frame s)
    (hvisit : ∀ i, i < n → ∃ k, k ≤ K ∧
      Eval visit k (store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames i))
        (store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames (i + 1)))) :
    ∃ k, k + 1 ≤ n * (K + 7) + 4 ∧
      Eval (command visit) k (store (Encoding.encodeNat n) (Encoding.encodeNat a) (frames 0))
        (store [] (Encoding.encodeNat (a + n)) (frames n)) := by
  obtain ⟨k, hk, he⟩ := loop_eval visit n a K frames hvisit
  exact ⟨2 + k, by omega, (gate_nat n (Encoding.encodeNat a) (frames 0)).seq he⟩

noncomputable abbrev program {s : ℕ} (visit : StructuredCalls.Cmd 16 (s + 2)) :=
  compiled (command visit) 0 1

theorem source_range {s : ℕ} (visit : StructuredCalls.Cmd 16 (s + 2))
    (n a K : ℕ) (frames : ℕ → Frame s)
    (hvisit : ∀ i, i < n → ∃ k, k ≤ K ∧
      Eval visit k (store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames i))
        (store (Encoding.encodeNat (n - 1 - i)) (Encoding.encodeNat (a + i)) (frames (i + 1)))) :
    BitProgram.RunsIn (program visit) (n * (K + 7) + 4)
      ((store (Encoding.encodeNat n) (Encoding.encodeNat a) (frames 0)).withPC
        (some (program visit).entry))
      ((store [] (Encoding.encodeNat (a + n)) (frames n)).withPC none) := by
  obtain ⟨k, hk, he⟩ := eval_range visit n a K frames hvisit
  exact ⟨k + 1, hk, compiled_halt_trace he 0 1⟩

end QecReliability.ExternalSATBridge.UnaryRangeLoop
