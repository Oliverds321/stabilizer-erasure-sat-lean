import ExternalSATFieldMembership
import ExternalSATUnaryFieldExtractor
import ExternalSATRawClauseParser

/-! A fixed raw-clause matcher: real two-bit arity dispatch, actual unary field
extraction and measured membership calls, and actual candidate-presence peeks.
The scanner preserves candidates and arbitrary input/output suffixes. -/
namespace QecReliability.ExternalSATBridge.RawClauseMatcher
open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram StructuredCalls

abbrev memberRegister : Fin 10 → Fin 12 := fun i => i.castAdd 2
abbrev memberStack : Fin 8 → Fin 10 := fun i => i.castAdd 2
abbrev extractRegister : Fin 2 → Fin 12 := fun i => i.castAdd 10
def extractStack : Fin 2 → Fin 10 := ![8, 3]

def regs (seen : Fin 3 → Bool) (bad low high : Bool) : Fin 12 → Bool :=
  ![false, false, false, false, false, seen 0, seen 1, seen 2, bad, false, low, high]
def store (candidate : Fin 3 → List Bool) (field input out : List Bool)
    (seen : Fin 3 → Bool) (bad low high : Bool) : StructuredProgram.State 12 10 :=
  ⟨regs seen bad low high,
    ![candidate 0, candidate 1, candidate 2, field, [], [], [], [], input, out]⟩
abbrev noSeen : Fin 3 → Bool := fun _ => false

theorem memberRegister_injective : Function.Injective memberRegister := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 12 => x.val) h
theorem memberStack_injective : Function.Injective memberStack := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 10 => x.val) h
theorem extractRegister_injective : Function.Injective extractRegister := by
  intro a b h; apply Fin.ext; exact congrArg (fun x : Fin 12 => x.val) h
theorem extractStack_injective : Function.Injective extractStack := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [extractStack]

theorem member_embed (candidate : Fin 3 → List Bool) (field input out : List Bool)
    (seen : Fin 3 → Bool) (bad low high : Bool) :
    embedState memberRegister memberStack (store candidate [] input out noSeen false low high)
      (FieldMembership.store candidate field seen bad false) =
        store candidate field input out seen bad low high := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ memberRegister_injective memberStack_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [memberRegister, store, regs, Fin.exists_fin_succ]
  · intro i hi
    fin_cases i <;> simp_all [memberStack, store, Fin.exists_fin_succ]

theorem extract_embed (candidate : Fin 3 → List Bool) (field input out : List Bool)
    (seen : Fin 3 → Bool) (bad low high : Bool) :
    embedState extractRegister extractStack (store candidate [] [] out seen bad low high)
      (⟨fun _ => false, ![input, field]⟩ : StructuredProgram.State 2 2) =
        store candidate field input out seen bad low high := by
  apply HeaderToUnary.embed_eq _ _ _ _ _ extractRegister_injective extractStack_injective
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [extractRegister, store, regs, Fin.exists_fin_succ]
  · intro i hi
    fin_cases i <;> simp_all [extractStack, store, Fin.exists_fin_succ]

noncomputable def fieldCommand : StructuredCalls.Cmd 12 10 :=
  .seq (.call (ProgramLinking.liftProgram UnaryFieldExtractor.program extractRegister extractStack))
    (.call (ProgramLinking.liftProgram FieldMembership.program memberRegister memberStack))
def fieldCost (candidate : Fin 3 → List Bool) (n : ℕ) : ℕ :=
  3 * n + 6 + FieldMembership.timeBound candidate (Encoding.encodeNat n)

theorem field_eval (candidate : Fin 3 → List Bool) (n : ℕ) (tail out : List Bool)
    (seen : Fin 3 → Bool) (bad low high : Bool) :
    ∃ steps, steps ≤ fieldCost candidate n ∧
      Eval fieldCommand steps
        (store candidate [] (Encoding.encodeNat n ++ tail) out seen bad low high)
        (store candidate [] tail out
          (FieldMembership.updatedSeen candidate (Encoding.encodeNat n) seen)
          (FieldMembership.updatedBad candidate (Encoding.encodeNat n) bad) low high) := by
  obtain ⟨ne, hne, he⟩ := UnaryFieldExtractor.source_run n (fun _ => false) tail []
  have hr : UnaryFieldExtractor.regs false false = (fun _ : Fin 2 => false) := by
    funext i; fin_cases i <;> rfl
  simp only [hr, List.append_nil] at he
  have ee := eval_call_lifted UnaryFieldExtractor.program extractRegister extractStack
    (store candidate [] [] out seen bad low high)
    extractRegister_injective extractStack_injective he
  rw [extract_embed, extract_embed] at ee
  obtain ⟨nm, hnm, hm⟩ := FieldMembership.source_run candidate (Encoding.encodeNat n) seen bad
  have em := eval_call_lifted FieldMembership.program memberRegister memberStack
    (store candidate [] tail out noSeen false low high)
    memberRegister_injective memberStack_injective hm
  rw [member_embed, member_embed] at em
  exact ⟨ne + nm, Nat.add_le_add hne hnm, ee.seq em⟩

def fields (codes : List ℕ) : List Bool := codes.flatMap Encoding.encodeNat

def afterSeen (candidate : Fin 3 → List Bool) : List ℕ → (Fin 3 → Bool) → (Fin 3 → Bool)
  | [], seen => seen
  | n :: ns, seen => afterSeen candidate ns
      (FieldMembership.updatedSeen candidate (Encoding.encodeNat n) seen)
def afterBad (candidate : Fin 3 → List Bool) : List ℕ → Bool → Bool
  | [], bad => bad
  | n :: ns, bad => afterBad candidate ns
      (FieldMembership.updatedBad candidate (Encoding.encodeNat n) bad)

noncomputable def repeatFields : ℕ → StructuredCalls.Cmd 12 10
  | 0 => .base .skip
  | k + 1 => .seq fieldCommand (repeatFields k)
def fieldsCost (candidate : Fin 3 → List Bool) (codes : List ℕ) : ℕ :=
  (codes.map (fieldCost candidate)).sum

theorem repeat_eval (candidate : Fin 3 → List Bool) (codes : List ℕ)
    (tail out : List Bool) (seen : Fin 3 → Bool) (bad low high : Bool) :
    ∃ steps, steps ≤ fieldsCost candidate codes ∧
      Eval (repeatFields codes.length) steps
        (store candidate [] (fields codes ++ tail) out seen bad low high)
        (store candidate [] tail out (afterSeen candidate codes seen)
          (afterBad candidate codes bad) low high) := by
  induction codes generalizing seen bad with
  | nil => exact ⟨0, by simp [fieldsCost], .base (.skip _)⟩
  | cons n ns ih =>
    obtain ⟨k, hk, he⟩ := field_eval candidate n (fields ns ++ tail) out seen bad low high
    obtain ⟨j, hj, ht⟩ := ih
      (FieldMembership.updatedSeen candidate (Encoding.encodeNat n) seen)
      (FieldMembership.updatedBad candidate (Encoding.encodeNat n) bad)
    refine ⟨k + j, ?_, ?_⟩
    · simpa only [fieldsCost, List.map_cons, List.sum_cons] using Nat.add_le_add hk hj
    · simpa only [repeatFields, List.length_cons, fields, List.flatMap_cons,
        List.append_assoc, afterSeen, afterBad] using he.seq ht

def atoms : List (StructuredProgram.Atom 12 10) → StructuredProgram.Cmd 12 10
  | [] => .skip
  | a :: as => .seq (.atom a) (atoms as)
theorem atoms_eval (as : List (StructuredProgram.Atom 12 10))
    (d : StructuredProgram.State 12 10) :
    StructuredProgram.Eval (atoms as) as.length d (as.foldl (fun d a => a.eval d) d) := by
  induction as generalizing d with
  | nil => exact StructuredProgram.Eval.skip d
  | cons a as ih =>
    simpa only [atoms, List.length_cons, List.foldl_cons, Nat.add_comm] using
      (StructuredProgram.Eval.atom a d).seq (ih (a.eval d))
theorem state_ext (a b : StructuredProgram.State 12 10)
    (hr : ∀ i, a.regs i = b.regs i) (hs : ∀ i, a.stacks i = b.stacks i) : a = b := by
  have hr' := funext hr; have hs' := funext hs
  cases a; cases b; simp_all

def prefixAtoms : List (StructuredProgram.Atom 12 10) :=
  [.pop 8 10 0, .pop 8 11 0, .set 0 false]
def prefixCommand : StructuredCalls.Cmd 12 10 := .base (atoms prefixAtoms)
theorem prefix_eval (candidate : Fin 3 → List Bool) (low high : Bool) (tail out : List Bool) :
    Eval prefixCommand 3 (store candidate [] (low :: high :: tail) out noSeen false false false)
      (store candidate [] tail out noSeen false low high) := by
  apply Eval.base
  have h := atoms_eval prefixAtoms
    (store candidate [] (low :: high :: tail) out noSeen false false false)
  have he : prefixAtoms.foldl (fun d a => a.eval d)
      (store candidate [] (low :: high :: tail) out noSeen false false false) =
      store candidate [] tail out noSeen false low high := by
    apply state_ext <;> intro i <;> fin_cases i <;>
      simp [prefixAtoms, store, regs, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  rw [he] at h
  simpa only [show prefixAtoms.length = 3 from rfl] using h

noncomputable def dispatch : StructuredCalls.Cmd 12 10 :=
  .ite 11 (.ite 10 (repeatFields 3) (repeatFields 2))
    (.ite 10 (repeatFields 1) (repeatFields 0))
theorem dispatch_eval (candidate : Fin 3 → List Bool) (codes : List ℕ) (hc : codes.length ≤ 3)
    (tail out : List Bool) :
    ∃ steps, steps ≤ fieldsCost candidate codes + 2 ∧
      Eval dispatch steps
        (store candidate [] (fields codes ++ tail) out noSeen false
          (RawClauseParser.lowBit codes.length) (RawClauseParser.highBit codes.length))
        (store candidate [] tail out (afterSeen candidate codes noSeen)
          (afterBad candidate codes false)
          (RawClauseParser.lowBit codes.length) (RawClauseParser.highBit codes.length)) := by
  obtain ⟨k, hk, he⟩ := repeat_eval candidate codes tail out noSeen false
    (RawClauseParser.lowBit codes.length) (RawClauseParser.highBit codes.length)
  refine ⟨k + 2, by omega, ?_⟩
  have hlen : codes.length = 0 ∨ codes.length = 1 ∨ codes.length = 2 ∨ codes.length = 3 := by omega
  rcases hlen with h | h | h | h
  · simp only [h] at he ⊢
    exact .ite_false rfl (.ite_false rfl he)
  · simp only [h] at he ⊢
    exact .ite_false rfl (.ite_true rfl he)
  · simp only [h] at he ⊢
    exact .ite_true rfl (.ite_false rfl he)
  · simp only [h] at he ⊢
    exact .ite_true rfl (.ite_true rfl he)

def finishAtoms : List (StructuredProgram.Atom 12 10) :=
  [.bnot 2 8,
    .peek 0 0 1, .bnot 1 1, .bor 1 1 5, .band 2 2 1,
    .peek 1 0 1, .bnot 1 1, .bor 1 1 6, .band 2 2 1,
    .peek 2 0 1, .bnot 1 1, .bor 1 1 7, .band 2 2 1,
    .push 9 2,
    .set 0 false, .set 1 false, .set 2 false, .set 3 false,
    .set 4 false, .set 5 false, .set 6 false, .set 7 false,
    .set 8 false, .set 9 false, .set 10 false, .set 11 false]
def result (candidate : Fin 3 → List Bool) (seen : Fin 3 → Bool) (bad : Bool) : Bool :=
  ((!bad && ((candidate 0).isEmpty || seen 0)) && ((candidate 1).isEmpty || seen 1)) &&
    ((candidate 2).isEmpty || seen 2)

theorem absent_head (w : List Bool) : (!w.head?.isSome) = w.isEmpty := by
  cases w <;> rfl

theorem absent_head_none (w : List Bool) : w.head?.isNone = w.isEmpty := by
  cases w <;> rfl

theorem finish_eval (candidate : Fin 3 → List Bool) (tail out : List Bool)
    (seen : Fin 3 → Bool) (bad low high : Bool) :
    Eval (.base (atoms finishAtoms)) 26 (store candidate [] tail out seen bad low high)
      (store candidate [] tail (result candidate seen bad :: out) noSeen false false false) := by
  apply Eval.base
  have h := atoms_eval finishAtoms (store candidate [] tail out seen bad low high)
  have he : finishAtoms.foldl (fun d a => a.eval d)
      (store candidate [] tail out seen bad low high) =
      store candidate [] tail (result candidate seen bad :: out) noSeen false false false := by
    apply state_ext <;> intro i <;> fin_cases i <;>
      simp [finishAtoms, store, regs, result, absent_head, absent_head_none, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  rw [he] at h
  simpa only [show finishAtoms.length = 26 from rfl] using h

noncomputable def command : StructuredCalls.Cmd 12 10 :=
  .seq prefixCommand (.seq dispatch (.base (atoms finishAtoms)))
noncomputable abbrev program := compiled command 8 9

def rawClause (codes : List ℕ) : List Bool := QueryCodec.word 2 codes.length ++ fields codes
def clauseResult (candidate : Fin 3 → List Bool) (codes : List ℕ) : Bool :=
  result candidate (afterSeen candidate codes noSeen) (afterBad candidate codes false)

/-- The flags have their ordinary set-membership meaning, including duplicates. -/
theorem afterSeen_spec (candidate : Fin 3 → List Bool) (codes : List ℕ)
    (seen : Fin 3 → Bool) (i : Fin 3) :
    afterSeen candidate codes seen i =
      (seen i || codes.any (fun n => decide (Encoding.encodeNat n = candidate i))) := by
  induction codes generalizing seen with
  | nil => simp [afterSeen]
  | cons n ns ih =>
    simp [afterSeen, ih, FieldMembership.updatedSeen, Bool.or_assoc]

theorem afterBad_spec (candidate : Fin 3 → List Bool) (codes : List ℕ) (bad : Bool) :
    afterBad candidate codes bad = (bad || codes.any (fun n =>
      !(decide (Encoding.encodeNat n = candidate 0) ||
        decide (Encoding.encodeNat n = candidate 1) || decide (Encoding.encodeNat n = candidate 2)))) := by
  induction codes generalizing bad with
  | nil => simp [afterBad]
  | cons n ns ih =>
    simp [afterBad, ih, FieldMembership.updatedBad, Bool.or_assoc]

/-- No foreign field, and every nonempty candidate slot seen. Empty slots really
are detected by physical peeks in finishAtoms, not by a semantic instruction. -/
theorem clauseResult_eq (candidate : Fin 3 → List Bool) (codes : List ℕ) :
    clauseResult candidate codes =
      (((!(codes.any (fun n => !(decide (Encoding.encodeNat n = candidate 0) ||
          decide (Encoding.encodeNat n = candidate 1) || decide (Encoding.encodeNat n = candidate 2)))) &&
        ((candidate 0).isEmpty || codes.any (fun n => decide (Encoding.encodeNat n = candidate 0)))) &&
        ((candidate 1).isEmpty || codes.any (fun n => decide (Encoding.encodeNat n = candidate 1)))) &&
        ((candidate 2).isEmpty || codes.any (fun n => decide (Encoding.encodeNat n = candidate 2)))) := by
  simp only [clauseResult, result, afterSeen_spec, afterBad_spec, noSeen, Bool.false_or]

/-- Exact correspondence to the already accepted raw parser's representation. -/
theorem rawClause_literalCodes {v : ℕ} (c : List (PrefixCNF.Literal v)) :
    rawClause (c.map (fun l => Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)))) =
      RawClauseParser.rawClause c := by
  simp [rawClause, fields, RawClauseParser.rawClause, RawClauseParser.fields,
    List.flatMap_map, Function.comp_def]

theorem eval_clause (candidate : Fin 3 → List Bool) (codes : List ℕ) (hc : codes.length ≤ 3)
    (tail out : List Bool) :
    ∃ steps, steps + 1 ≤ fieldsCost candidate codes + 32 ∧
      Eval command steps
        (store candidate [] (rawClause codes ++ tail) out noSeen false false false)
        (store candidate [] tail (clauseResult candidate codes :: out) noSeen false false false) := by
  obtain ⟨k, hk, he⟩ := dispatch_eval candidate codes hc tail out
  have hp := prefix_eval candidate (RawClauseParser.lowBit codes.length)
    (RawClauseParser.highBit codes.length) (fields codes ++ tail) out
  have hw : QueryCodec.word 2 codes.length =
      [RawClauseParser.lowBit codes.length, RawClauseParser.highBit codes.length] := by
    rfl
  have ht := hp.seq (he.seq (finish_eval candidate tail out _ _ _ _))
  refine ⟨3 + (k + 26), by omega, ?_⟩
  simpa only [command, rawClause, hw, List.cons_append, List.nil_append,
    List.append_assoc, clauseResult] using ht

theorem source_run (candidate : Fin 3 → List Bool) (codes : List ℕ) (hc : codes.length ≤ 3)
    (tail out : List Bool) :
    BitProgram.RunsIn program (fieldsCost candidate codes + 32)
      ((store candidate [] (rawClause codes ++ tail) out noSeen false false false).withPC
        (some program.entry))
      ((store candidate [] tail (clauseResult candidate codes :: out) noSeen false false false).withPC none) := by
  obtain ⟨n, hn, he⟩ := eval_clause candidate codes hc tail out
  exact ⟨n + 1, hn, compiled_halt_trace he 8 9⟩
noncomputable abbrev primitive := GuardedCompiler.primitive program

theorem primitive_run (candidate : Fin 3 → List Bool) (codes : List ℕ) (hc : codes.length ≤ 3)
    (tail out : List Bool) :
    Computation.RunsIn primitive.step (7 * (fieldsCost candidate codes + 32))
      (GuardedCompiler.primitiveCfg program
        ((store candidate [] (rawClause codes ++ tail) out noSeen false false false).withPC
          (some program.entry)))
      (GuardedCompiler.primitiveCfg program
        ((store candidate [] tail (clauseResult candidate codes :: out) noSeen false false false).withPC none)) :=
  GuardedCompiler.primitive_execution program (source_run candidate codes hc tail out)

end QecReliability.ExternalSATBridge.RawClauseMatcher
#print axioms QecReliability.ExternalSATBridge.RawClauseMatcher.source_run
#print axioms QecReliability.ExternalSATBridge.RawClauseMatcher.primitive_run
