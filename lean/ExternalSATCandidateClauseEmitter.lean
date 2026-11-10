import ExternalSATFrameEmitter

/-! One actual two-level canonical-list entry emitter. Candidate slots0,1,2 are
preserved; [] means absent, whereas every unary encodeNat word is present. The
inner list payload is physically built, reversed, then escaped again into the
outer reversed accumulator. No whole-CNF traversal is asserted here. -/
namespace QecReliability.ExternalSATBridge.CandidateClauseEmitter

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

abbrev Candidates := Fin 3 → List Bool
abbrev zeroRegs : Fin 2 → Bool := fun _ => false

def store (r : Fin 2 → Bool) (c : Candidates)
    (work inner scratch outer : List Bool) : StructuredProgram.State 2 7 :=
  ⟨r, ![c 0, c 1, c 2, work, inner, scratch, outer]⟩

abbrev data (c : Candidates) (work inner scratch outer : List Bool) :=
  store zeroRegs c work inner scratch outer

abbrev candidatePort (i : Fin 3) : Fin 7 := i.castAdd 4

theorem reset_regs (r : Fin 2 → Bool) : readRegs r 0 1 none = zeroRegs := by
  funext i; fin_cases i <;> rfl

abbrev copyProgram (i : Fin 3) : Program 2 7 8 :=
  StackRoutines.copyProgram (candidatePort i) 3 5 0 1

theorem copy_trace (i : Fin 3) (r : Fin 2 → Bool) (c : Candidates) (inner outer : List Bool) :
    Trace (copyProgram i) (7 * (c i).length + 5)
      ((store r c [] inner [] outer).withPC (some (copyProgram i).entry))
      ((data c (c i) inner [] outer).withPC none) := by
  have h3 : candidatePort i ≠ 3 := by fin_cases i <;> decide
  have h5 : candidatePort i ≠ 5 := by fin_cases i <;> decide
  have ht := StackRoutines.copyProgram_trace (candidatePort i) (3 : Fin 7) 5 (0 : Fin 2) 1
    h3 h5 (by decide) (by decide) r
    (![c 0, c 1, c 2, [], inner, [], outer] : Fin 7 → List Bool) rfl
  have hh := StackRoutines.halt_after_trace (copyProgram i) ht 7 rfl rfl
  have hlookup : (![c 0, c 1, c 2, [], inner, [], outer] : Fin 7 → List Bool) (candidatePort i) = c i := by
    fin_cases i <;> rfl
  have hstacks : StackRoutines.copyStacks (candidatePort i) (3 : Fin 7)
      (![c 0, c 1, c 2, [], inner, [], outer] : Fin 7 → List Bool) =
      ![c 0, c 1, c 2, c i, inner, [], outer] := by
    simp only [StackRoutines.copyStacks, hlookup]
    funext j; fin_cases j <;> simp
  simpa only [StackRoutines.copyResult, reset_regs, hstacks, hlookup,
    data, store, StructuredProgram.State.withPC, Nat.add_assoc,
    show (4 : ℕ) + 1 = 5 from rfl] using hh

abbrev innerPorts : Fin 2 → Fin 7 := ![3, 4]
abbrev outerPorts : Fin 2 → Fin 7 := ![4, 6]

theorem innerPorts_injective : Function.Injective innerPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [innerPorts]
theorem outerPorts_injective : Function.Injective outerPorts := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [outerPorts]

abbrev frameData (r : Fin 2 → Bool) (a b : List Bool) : StructuredProgram.State 2 2 := ⟨r, ![a, b]⟩

theorem inner_embed (c : Candidates) (outer : List Bool) (r : Fin 2 → Bool) (a b : List Bool) :
    embedState (id : Fin 2 → Fin 2) innerPorts (data c [] [] [] outer)
      (frameData r a b) = store r c a b [] outer := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id innerPorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi; fin_cases i <;> simp_all [data, store, innerPorts, Fin.exists_fin_succ]

theorem outer_embed (c : Candidates) (r : Fin 2 → Bool) (a b : List Bool) :
    embedState (id : Fin 2 → Fin 2) outerPorts (data c [] [] [] [])
      (frameData r a b) = store r c [] a [] b := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ Function.injective_id outerPorts_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi; fin_cases i <;> simp_all [data, store, outerPorts, Fin.exists_fin_succ]

abbrev innerProgram := ProgramLinking.liftProgram FrameEmitter.program (id : Fin 2 → Fin 2) innerPorts
abbrev outerProgram := ProgramLinking.liftProgram FrameEmitter.program (id : Fin 2 → Fin 2) outerPorts

theorem frame_trace (r : Fin 2 → Bool) (bits accumulator : List Bool) :
    Trace FrameEmitter.program (4 * bits.length + 4)
      ((frameData r bits accumulator).withPC (some FrameEmitter.program.entry))
      ((frameData zeroRegs [] ((Encoding.frame bits).reverse ++ accumulator)).withPC none) := by
  have hr : FrameEmitter.regs none = zeroRegs := by funext i; fin_cases i <;> rfl
  simpa only [FrameEmitter.cfg, FrameEmitter.finalCfg, hr, frameData,
    StructuredProgram.State.withPC, show FrameEmitter.program.entry = 0 from rfl] using
    FrameEmitter.emit_trace r bits accumulator

theorem inner_frame_eval (r : Fin 2 → Bool) (c : Candidates) (bits inner outer : List Bool) :
    Eval (.call innerProgram) (4 * bits.length + 4) (store r c bits inner [] outer)
      (data c [] ((Encoding.frame bits).reverse ++ inner) [] outer) := by
  have h := eval_call_lifted FrameEmitter.program (id : Fin 2 → Fin 2) innerPorts
    (data c [] [] [] outer) Function.injective_id innerPorts_injective (frame_trace r bits inner)
  simpa only [inner_embed] using h

theorem outer_frame_eval (r : Fin 2 → Bool) (c : Candidates) (bits outer : List Bool) :
    Eval (.call outerProgram) (4 * bits.length + 4) (store r c [] bits [] outer)
      (data c [] [] [] ((Encoding.frame bits).reverse ++ outer)) := by
  have h := eval_call_lifted FrameEmitter.program (id : Fin 2 → Fin 2) outerPorts
    (data c [] [] [] []) Function.injective_id outerPorts_injective (frame_trace r bits outer)
  simpa only [outer_embed] using h

def push (port : Fin 7) (bit : Bool) : StructuredCalls.Cmd 2 7 :=
  .base (.seq (.atom (.set 0 bit)) (.atom (.push port 0)))

abbrev marked (bit : Bool) : Fin 2 → Bool := Function.update zeroRegs 0 bit

theorem push_inner_eval (bit : Bool) (c : Candidates) (work inner outer : List Bool) :
    Eval (push 4 bit) 2 (data c work inner [] outer)
      (store (marked bit) c work (bit :: inner) [] outer) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 2) bit) (data c work inner [] outer)).seq
    (StructuredProgram.Eval.atom (.push (4 : Fin 7) 0) _)
  have hlookup : (![c 0, c 1, c 2, work, inner, [], outer] : Fin 7 → List Bool) 4 = inner := rfl
  have hstacks : Function.update
      (![c 0, c 1, c 2, work, inner, [], outer] : Fin 7 → List Bool) 4 (bit :: inner) =
      ![c 0, c 1, c 2, work, bit :: inner, [], outer] := by
    funext i; fin_cases i <;> simp
  apply Eval.base
  simpa [push, data, store, marked, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    hlookup, hstacks, funext_iff, Fin.forall_fin_succ] using h

theorem push_outer_eval (c : Candidates) (inner outer : List Bool) :
    Eval (push 6 true) 2 (data c [] inner [] outer)
      (store (marked true) c [] inner [] (true :: outer)) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 2) true) (data c [] inner [] outer)).seq
    (StructuredProgram.Eval.atom (.push (6 : Fin 7) 0) _)
  have hlookup : (![c 0, c 1, c 2, [], inner, [], outer] : Fin 7 → List Bool) 6 = outer := rfl
  have hstacks : Function.update
      (![c 0, c 1, c 2, [], inner, [], outer] : Fin 7 → List Bool) 6 (true :: outer) =
      ![c 0, c 1, c 2, [], inner, [], true :: outer] := by
    funext i; fin_cases i <;> simp
  apply Eval.base
  simpa [push, data, store, marked, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    hlookup, hstacks, funext_iff, Fin.forall_fin_succ] using h

abbrev reverseProgram : Program 2 7 10 := StackRoutines.reverseProgram 4 3 5 0 1

theorem reverse_trace (c : Candidates) (inner outer : List Bool) :
    Trace reverseProgram (9 * inner.length + 7)
      ((data c [] inner [] outer).withPC (some reverseProgram.entry))
      ((data c [] inner.reverse [] outer).withPC none) := by
  have ht := StackRoutines.reverseProgram_trace (4 : Fin 7) 3 5 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide) zeroRegs
    (![c 0, c 1, c 2, [], inner, [], outer] : Fin 7 → List Bool) rfl rfl
  have hh := StackRoutines.halt_after_trace reverseProgram ht 9 rfl rfl
  have hstacks : StackRoutines.reverseStacks (4 : Fin 7)
      (![c 0, c 1, c 2, [], inner, [], outer] : Fin 7 → List Bool) =
      ![c 0, c 1, c 2, [], inner.reverse, [], outer] := by
    funext i; fin_cases i <;> simp [StackRoutines.reverseStacks]
  simpa only [StackRoutines.reverseResult, reset_regs, hstacks, data, store,
    StructuredProgram.State.withPC, Nat.add_assoc,
    show (![c 0, c 1, c 2, [], inner, [], outer] : Fin 7 → List Bool) 4 = inner from rfl,
    show (6 : ℕ) + 1 = 7 from rfl] using hh

def peek (i : Fin 3) : StructuredCalls.Cmd 2 7 := .base (.atom (.peek (candidatePort i) 0 1))
def peeked (i : Fin 3) (c : Candidates) (inner outer : List Bool) : StructuredProgram.State 2 7 :=
  store (readRegs zeroRegs 0 1 (c i).head?) c [] inner [] outer

theorem peek_eval (i : Fin 3) (c : Candidates) (inner outer : List Bool) :
    Eval (peek i) 1 (data c [] inner [] outer) (peeked i c inner outer) := by
  fin_cases i <;> exact .base (.atom _ _)

noncomputable def presentCommand (i : Fin 3) : StructuredCalls.Cmd 2 7 :=
  .seq (.call (copyProgram i)) (.seq (push 4 true) (.call innerProgram))
noncomputable def slotCommand (i : Fin 3) : StructuredCalls.Cmd 2 7 :=
  .seq (peek i) (.ite 1 (presentCommand i) (.base .skip))

def fragment (word : List Bool) : List Bool := if word = [] then [] else true :: Encoding.frame word
def slotCost (word : List Bool) : ℕ := if word = [] then 2 else 11 * word.length + 13

theorem slot_eval (i : Fin 3) (c : Candidates) (inner outer : List Bool) :
    Eval (slotCommand i) (slotCost (c i)) (data c [] inner [] outer)
      (data c [] ((fragment (c i)).reverse ++ inner) [] outer) := by
  have ep := peek_eval i c inner outer
  by_cases hempty : c i = []
  · have heq : peeked i c inner outer = data c [] inner [] outer := by
      simp only [peeked, hempty, List.head?_nil, reset_regs]
    rw [heq] at ep
    have hs : Eval (.base StructuredProgram.Cmd.skip) 0
        (data c [] inner [] outer) (data c [] inner [] outer) := .base (.skip _)
    have hi : Eval (.ite 1 (presentCommand i) (.base .skip)) 1
        (data c [] inner [] outer) (data c [] inner [] outer) :=
      .ite_false (show (data c [] inner [] outer).regs 1 = false from rfl) hs
    simpa [slotCommand, slotCost, fragment, hempty] using ep.seq hi
  · have hc := copy_trace i (readRegs zeroRegs 0 1 (c i).head?) c inner outer
    have ec : Eval (.call (copyProgram i)) (7 * (c i).length + 5)
        (peeked i c inner outer) (data c (c i) inner [] outer) := .call _ hc
    have hpush := push_inner_eval true c (c i) inner outer
    have hf := inner_frame_eval (marked true) c (c i) (true :: inner) outer
    have hy : Eval (presentCommand i)
        ((7 * (c i).length + 5) + (2 + (4 * (c i).length + 4)))
        (peeked i c inner outer)
        (data c [] ((Encoding.frame (c i)).reverse ++ true :: inner) [] outer) := ec.seq (hpush.seq hf)
    have hp : (peeked i c inner outer).regs 1 = true := by
      change (readRegs zeroRegs 0 1 (c i).head?) 1 = true
      rw [readRegs_present]
      cases h : c i <;> simp_all
    have hi : Eval (.ite 1 (presentCommand i) (.base .skip))
        (((7 * (c i).length + 5) + (2 + (4 * (c i).length + 4))) + 1)
        (peeked i c inner outer)
        (data c [] ((Encoding.frame (c i)).reverse ++ true :: inner) [] outer) :=
      .ite_true hp hy
    have hall := ep.seq hi
    convert hall using 1 <;>
      simp [slotCommand, slotCost, fragment, hempty, List.reverse_cons, List.append_assoc] <;> omega

noncomputable def itemsCommand : StructuredCalls.Cmd 2 7 :=
  .seq (slotCommand 0) (.seq (slotCommand 1) (slotCommand 2))
def pieces (c : Candidates) : List Bool := fragment (c 0) ++ fragment (c 1) ++ fragment (c 2)
def payload (c : Candidates) : List Bool := pieces c ++ [false]
def entry (c : Candidates) : List Bool := true :: Encoding.frame (payload c)
def itemsCost (c : Candidates) : ℕ := slotCost (c 0) + (slotCost (c 1) + slotCost (c 2))

theorem items_eval (c : Candidates) (outer : List Bool) :
    Eval itemsCommand (itemsCost c) (data c [] [] [] outer)
      (data c [] (pieces c).reverse [] outer) := by
  have h0 := slot_eval 0 c [] outer
  have h1 := slot_eval 1 c (fragment (c 0)).reverse outer
  have h2 := slot_eval 2 c ((fragment (c 1)).reverse ++ (fragment (c 0)).reverse) outer
  have h0' : Eval (slotCommand 0) (slotCost (c 0)) (data c [] [] [] outer)
      (data c [] (fragment (c 0)).reverse [] outer) := by simpa using h0
  simpa only [itemsCommand, itemsCost, pieces, List.reverse_append, List.append_assoc] using h0'.seq (h1.seq h2)

noncomputable def command : StructuredCalls.Cmd 2 7 :=
  .seq itemsCommand (.seq (push 4 false)
    (.seq (.call reverseProgram) (.seq (push 6 true) (.call outerProgram))))
noncomputable abbrev program := compiled command 0 6

def exactCost (c : Candidates) : ℕ := itemsCost c + 13 * (payload c).length + 15

/-- Both escaping levels are emitted by actual calls, with a physical reversal
between them. Candidate words survive and every scratch port is empty afterward. -/
theorem clause_eval (c : Candidates) (outer : List Bool) :
    Eval command (exactCost c) (data c [] [] [] outer)
      (data c [] [] [] ((entry c).reverse ++ outer)) := by
  have hi := items_eval c outer
  have hp := push_inner_eval false c [] (pieces c).reverse outer
  have hzero : marked false = zeroRegs := by funext i; fin_cases i <;> rfl
  have hp' : Eval (push 4 false) 2 (data c [] (pieces c).reverse [] outer)
      (data c [] (payload c).reverse [] outer) := by
    simpa only [hzero, payload, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append] using hp
  have hr : Eval (.call reverseProgram) (9 * (payload c).length + 7)
      (data c [] (payload c).reverse [] outer) (data c [] (payload c) [] outer) := by
    simpa only [List.length_reverse, List.reverse_reverse] using
      (Eval.call reverseProgram (reverse_trace c (payload c).reverse outer))
  have ho := push_outer_eval c (payload c) outer
  have hf := outer_frame_eval (marked true) c (payload c) (true :: outer)
  have hall := hi.seq (hp'.seq (hr.seq (ho.seq hf)))
  have htime : itemsCost c + (2 + ((9 * (payload c).length + 7) +
      (2 + (4 * (payload c).length + 4)))) = exactCost c := by
    dsimp only [exactCost]
    omega
  have hentry : (Encoding.frame (payload c)).reverse ++ true :: outer =
      (entry c).reverse ++ outer := by
    simp [entry, List.reverse_cons, List.append_assoc]
  simpa only [command, htime, hentry] using hall

def wordSize (c : Candidates) : ℕ := (c 0).length + (c 1).length + (c 2).length

theorem slotCost_le (word : List Bool) : slotCost word ≤ 11 * word.length + 13 := by
  by_cases h : word = [] <;> simp [slotCost, h]
theorem fragment_length_le (word : List Bool) : (fragment word).length ≤ 2 * word.length + 2 := by
  by_cases h : word = [] <;> simp [fragment, h]

theorem source_bound (c : Candidates) : exactCost c + 1 ≤ 64 * (wordSize c + 4) := by
  have h0 := slotCost_le (c 0); have h1 := slotCost_le (c 1); have h2 := slotCost_le (c 2)
  have l0 := fragment_length_le (c 0); have l1 := fragment_length_le (c 1); have l2 := fragment_length_le (c 2)
  simp only [exactCost, itemsCost, payload, pieces, List.length_append,
    List.length_cons, List.length_nil, wordSize]
  omega

theorem source_words (c : Candidates) (outer : List Bool) :
    BitProgram.RunsIn program (64 * (wordSize c + 4))
      ((data c [] [] [] outer).withPC (some program.entry))
      ((data c [] [] [] ((entry c).reverse ++ outer)).withPC none) :=
  ⟨exactCost c + 1, source_bound c, compiled_halt_trace (clause_eval c outer) 0 6⟩

def slots : List ℕ → Candidates
  | [] => ![[], [], []]
  | [a] => ![Encoding.encodeNat a, [], []]
  | [a, b] => ![Encoding.encodeNat a, Encoding.encodeNat b, []]
  | a :: b :: d :: _ => ![Encoding.encodeNat a, Encoding.encodeNat b, Encoding.encodeNat d]

theorem encodeNat_ne_nil (n : ℕ) : Encoding.encodeNat n ≠ [] := by
  intro h
  have hl := Encoding.length_encodeNat n
  rw [h] at hl
  simp at hl

theorem payload_slots (codes : List ℕ) (hlen : codes.length ≤ 3) :
    payload (slots codes) = Encoding.encodeList Encoding.encodeNat codes := by
  cases codes with
  | nil => simp [payload, pieces, fragment, slots, Encoding.encodeList]
  | cons a codes =>
    cases codes with
    | nil => simp [payload, pieces, fragment, slots, Encoding.encodeList, encodeNat_ne_nil]
    | cons b codes =>
      cases codes with
      | nil => simp [payload, pieces, fragment, slots, Encoding.encodeList, encodeNat_ne_nil, List.append_assoc]
      | cons d codes =>
        cases codes with
        | nil => simp [payload, pieces, fragment, slots, Encoding.encodeList, encodeNat_ne_nil, List.append_assoc]
        | cons e codes => simp only [List.length_cons] at hlen; omega

/-- Exact requested outer encodeList entry for a prefix-filled candidate of
zero through three unary words. Code0 is [false], never an absent empty slot. -/
theorem source_clause (codes : List ℕ) (hlen : codes.length ≤ 3) (outer : List Bool) :
    BitProgram.RunsIn program (64 * (wordSize (slots codes) + 4))
      ((data (slots codes) [] [] [] outer).withPC (some program.entry))
      ((data (slots codes) [] [] []
        ((true :: Encoding.frame (Encoding.encodeList Encoding.encodeNat codes)).reverse ++ outer)).withPC none) := by
  simpa only [entry, payload_slots codes hlen] using source_words (slots codes) outer

end QecReliability.ExternalSATBridge.CandidateClauseEmitter
