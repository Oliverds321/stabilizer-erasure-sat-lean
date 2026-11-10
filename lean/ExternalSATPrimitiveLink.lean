import ExternalSATCanonicalFrontend

/-! Actual sequential composition of primitive finite tables. The first table's
halt instruction is replaced by a write-back of the symbol it just read and a
jump to the second table's entry. This costs the SAME one primitive transition.
Only the second table's Boolean is an answer. No SAT-engine witness is asserted.
Fresh second-stage work tapes are allocated physically, not supplied as metadata.
-/
namespace QecReliability.ExternalSATBridge.PrimitiveLink
open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open Computation

abbrev Tape := Turing.Tape (Option Bool)
variable (F M : PrimitiveMachine) (out : Fin F.tapeCount)

def frontSlot (i : Fin F.tapeCount) : Fin (F.tapeCount + M.tapeCount) := i.castAdd _
def freshSlot (i : Fin M.tapeCount) : Fin (F.tapeCount + M.tapeCount) := Fin.natAdd _ i

theorem front_inj (i j : Fin F.tapeCount) : frontSlot F M i = frontSlot F M j ↔ i = j := by
  constructor
  · intro h; apply Fin.ext; exact congrArg (fun x : Fin (F.tapeCount + M.tapeCount) => x.val) h
  · rintro rfl; rfl

theorem fresh_inj (i j : Fin M.tapeCount) : freshSlot F M i = freshSlot F M j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg (fun x : Fin (F.tapeCount + M.tapeCount) => x.val) h
    change F.tapeCount + i.val = F.tapeCount + j.val at hv
    omega
  · rintro rfl; rfl

theorem front_ne_fresh (i : Fin F.tapeCount) (j : Fin M.tapeCount) :
    frontSlot F M i ≠ freshSlot F M j := by
  intro h
  have hv := congrArg (fun x : Fin (F.tapeCount + M.tapeCount) => x.val) h
  have hi := i.isLt
  change i.val = F.tapeCount + j.val at hv
  omega

def engineSlot (i : Fin M.tapeCount) : Fin (F.tapeCount + M.tapeCount) :=
  if i = M.inputTape then frontSlot F M out else freshSlot F M i

theorem engine_injective : Function.Injective (engineSlot F M out) := by
  intro i j h
  by_cases hi : i = M.inputTape
  · by_cases hj : j = M.inputTape
    · exact hi.trans hj.symm
    · simp only [engineSlot, if_pos hi, if_neg hj] at h
      exact False.elim (front_ne_fresh F M out j h)
  · by_cases hj : j = M.inputTape
    · simp only [engineSlot, if_neg hi, if_pos hj] at h
      exact False.elim (front_ne_fresh F M out i h.symm)
    · simp only [engineSlot, if_neg hi, if_neg hj] at h
      exact (fresh_inj F M i j).mp h

def frontTransition (q : Fin F.stateCount) (bit : Option Bool) :
    Bool ⊕ (Fin (F.stateCount + M.stateCount) × Turing.TM0.Stmt (Option Bool)) :=
  match F.transition q bit with
  | .inl _ => .inr (Fin.natAdd F.stateCount M.start, .write bit)
  | .inr (q', action) => .inr (q'.castAdd M.stateCount, action)

def engineTransition (q : Fin M.stateCount) (bit : Option Bool) :
    Bool ⊕ (Fin (F.stateCount + M.stateCount) × Turing.TM0.Stmt (Option Bool)) :=
  match M.transition q bit with
  | .inl answer => .inl answer
  | .inr (q', action) => .inr (Fin.natAdd F.stateCount q', action)

/-- Fixed finite table, with no access to either proof trace or input length. -/
def machine : PrimitiveMachine where
  tapeCount := F.tapeCount + M.tapeCount
  stateCount := F.stateCount + M.stateCount
  inputTape := frontSlot F M F.inputTape
  start := F.start.castAdd M.stateCount
  scan := Fin.addCases (fun q => frontSlot F M (F.scan q))
    (fun q => engineSlot F M out (M.scan q))
  transition := Fin.addCases (frontTransition F M) (engineTransition F M)

def frontTapes (tapes : Fin F.tapeCount → Tape) : Fin (F.tapeCount + M.tapeCount) → Tape :=
  Fin.addCases tapes (fun _ => Turing.Tape.mk₁ [])

@[simp] theorem frontTapes_front (tapes : Fin F.tapeCount → Tape) (i : Fin F.tapeCount) :
    frontTapes F M tapes (frontSlot F M i) = tapes i := by simp [frontTapes, frontSlot]
@[simp] theorem frontTapes_fresh (tapes : Fin F.tapeCount → Tape) (i : Fin M.tapeCount) :
    frontTapes F M tapes (freshSlot F M i) = Turing.Tape.mk₁ [] := by simp [frontTapes, freshSlot]

theorem frontTapes_update (tapes : Fin F.tapeCount → Tape) (i : Fin F.tapeCount) (t : Tape) :
    frontTapes F M (Function.update tapes i t) =
      Function.update (frontTapes F M tapes) (frontSlot F M i) t := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change frontTapes F M (Function.update tapes i t) (frontSlot F M k) =
      Function.update (frontTapes F M tapes) (frontSlot F M i) t (frontSlot F M k)
    simp only [frontTapes_front, Function.update_apply, front_inj]
  · change frontTapes F M (Function.update tapes i t) (freshSlot F M k) =
      Function.update (frontTapes F M tapes) (frontSlot F M i) t (freshSlot F M k)
    simp [Function.update_apply, Ne.symm (front_ne_fresh F M i k)]

def frontState : Bool ⊕ Fin F.stateCount → Bool ⊕ Fin (F.stateCount + M.stateCount)
  | .inl _ => .inr (Fin.natAdd F.stateCount M.start)
  | .inr q => .inr (q.castAdd M.stateCount)

def frontCfg (c : F.Cfg) : (machine F M out).Cfg :=
  ⟨frontState F M c.state, frontTapes F M c.tapes⟩

def engineState : Bool ⊕ Fin M.stateCount → Bool ⊕ Fin (F.stateCount + M.stateCount)
  | .inl answer => .inl answer
  | .inr q => .inr (Fin.natAdd F.stateCount q)

def EngineRelated (c : (machine F M out).Cfg) (d : M.Cfg) : Prop :=
  c.state = engineState F M d.state ∧ ∀ i, c.tapes (engineSlot F M out i) = d.tapes i

/-- A successful frontend transition, including its last halt, is one real
linked transition. The final marker is discarded by the finite table itself. -/
theorem front_step {a b : F.Cfg} (h : F.step a = some b) :
    (machine F M out).step (frontCfg F M out a) = some (frontCfg F M out b) := by
  rcases a with ⟨state, tapes⟩
  cases state with
  | inl answer => simp [PrimitiveMachine.step] at h
  | inr q =>
    cases ht : F.transition q (tapes (F.scan q)).head with
    | inl answer =>
      simp only [PrimitiveMachine.step, ht, Option.some.injEq] at h
      subst b
      have hu : Function.update (frontTapes F M tapes) (frontSlot F M (F.scan q))
          (tapes (F.scan q)) = frontTapes F M tapes := by
        funext i
        by_cases hi : i = frontSlot F M (F.scan q)
        · subst i
          simp [Function.update_apply]
        · simp [Function.update_apply, hi]
      simp [PrimitiveMachine.step, machine, frontCfg, frontState, frontTransition,
        ht, hu]
      exact hu
    | inr result =>
      obtain ⟨q', action⟩ := result
      simp only [PrimitiveMachine.step, ht, Option.some.injEq] at h
      subst b
      cases action <;>
        simp [PrimitiveMachine.step, machine, frontCfg, frontState, frontTransition,
          ht, frontTapes_update] <;> rfl

theorem front_trace {a b : F.Cfg} {n : Nat} (h : Trace F.step n a b) :
    Trace (machine F M out).step n (frontCfg F M out a) (frontCfg F M out b) := by
  induction h with
  | refl a => exact .refl _
  | cons hs ht ih => exact .cons (front_step F M out hs) ih

theorem front_initial (bits : List Bool) :
    frontCfg F M out (F.init bits) = (machine F M out).init bits := by
  change (⟨.inr (F.start.castAdd M.stateCount), frontTapes F M (F.init bits).tapes⟩ :
    (machine F M out).Cfg) = ⟨.inr (F.start.castAdd M.stateCount), _⟩
  congr 1
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change frontTapes F M (F.init bits).tapes (frontSlot F M k) =
      (if frontSlot F M k = frontSlot F M F.inputTape
       then Turing.Tape.mk₁ (bits.map some) else Turing.Tape.mk₁ [])
    simp [PrimitiveMachine.init, front_inj]
  · change frontTapes F M (F.init bits).tapes (freshSlot F M k) =
      (if freshSlot F M k = frontSlot F M F.inputTape
       then Turing.Tape.mk₁ (bits.map some) else Turing.Tape.mk₁ [])
    simp [Ne.symm (front_ne_fresh F M F.inputTape k)]

/-- Head-relative exact word equality suffices: no absolute-coordinate origin
assumption is smuggled in. All other engine tapes are genuinely fresh blanks. -/
theorem handoff {final : F.Cfg} {answer : Bool} {word : List Bool}
    (hh : final.state = .inl answer)
    (hw : final.tapes out = Turing.Tape.mk₁ (word.map some)) :
    EngineRelated F M out (frontCfg F M out final) (M.init word) := by
  constructor
  · change frontState F M final.state = engineState F M (.inr M.start)
    rw [hh] <;> rfl
  · intro i
    by_cases hi : i = M.inputTape
    · simp [frontCfg, engineSlot, hi, PrimitiveMachine.init, hw]
    · simp [frontCfg, engineSlot, hi, PrimitiveMachine.init]

theorem engine_update (tapes : Fin (F.tapeCount + M.tapeCount) → Tape)
    (i : Fin M.tapeCount) (t : Tape) :
    (fun j => Function.update tapes (engineSlot F M out i) t (engineSlot F M out j)) =
      Function.update (fun j => tapes (engineSlot F M out j)) i t := by
  funext j
  simp only [Function.update_apply, (engine_injective F M out).eq_iff]

/-- The second phase is the actual engine table, with an injective tape map. -/
theorem engine_step {a b : M.Cfg} {c : (machine F M out).Cfg}
    (h : M.step a = some b) (hc : EngineRelated F M out c a) :
    ∃ d, (machine F M out).step c = some d ∧ EngineRelated F M out d b := by
  rcases a with ⟨state, tapes⟩
  rcases hc with ⟨hstate, htapes⟩
  have hfun : (fun i => c.tapes (engineSlot F M out i)) = tapes := funext htapes
  cases state with
  | inl answer => simp [PrimitiveMachine.step] at h
  | inr q =>
    cases ht : M.transition q (tapes (M.scan q)).head with
    | inl answer =>
      simp only [PrimitiveMachine.step, ht, Option.some.injEq] at h
      subst b
      refine ⟨⟨.inl answer, c.tapes⟩, ?_, rfl, htapes⟩
      simp [PrimitiveMachine.step, machine, hstate, engineState, engineTransition, htapes, ht]
    | inr result =>
      obtain ⟨q', action⟩ := result
      simp only [PrimitiveMachine.step, ht, Option.some.injEq] at h
      subst b
      let nextTape := PrimitiveTransport.perform action (c.tapes (engineSlot F M out (M.scan q)))
      refine ⟨⟨.inr (Fin.natAdd F.stateCount q'),
        Function.update c.tapes (engineSlot F M out (M.scan q)) nextTape⟩, ?_, rfl, ?_⟩
      · cases action <;>
          simp [PrimitiveMachine.step, machine, hstate, engineState, engineTransition,
            htapes, ht, nextTape, PrimitiveTransport.perform]
      · have hp := engine_update F M out c.tapes (M.scan q) nextTape
        rw [hfun] at hp
        intro i
        have he := congrFun hp i
        cases action <;>
          simp only [nextTape, PrimitiveTransport.perform, htapes] at he ⊢ <;>
          exact he

theorem engine_trace {a b : M.Cfg} {n : Nat} (h : Trace M.step n a b)
    (c : (machine F M out).Cfg) (hc : EngineRelated F M out c a) :
    ∃ d, Trace (machine F M out).step n c d ∧ EngineRelated F M out d b := by
  induction h generalizing c with
  | refl a => exact ⟨c, .refl c, hc⟩
  | cons hs ht ih =>
    obtain ⟨c', hs', hc'⟩ := engine_step F M out hs hc
    obtain ⟨d, hd, hrel⟩ := ih c' hc'
    exact ⟨d, .cons hs' hd, hrel⟩

/-- Composition preserves exact primitive transition counts and the genuine
second-stage answer. Both premises are real executions of explicit machines. -/
theorem sequential_trace (bits word : List Bool) {nf nm : Nat} {f : F.Cfg} {m : M.Cfg}
    {marker answer : Bool} (hf : Trace F.step nf (F.init bits) f)
    (hfh : f.state = .inl marker) (hword : f.tapes out = Turing.Tape.mk₁ (word.map some))
    (hm : Trace M.step nm (M.init word) m) (hmh : m.state = .inl answer) :
    ∃ final, Trace (machine F M out).step (nf + nm) ((machine F M out).init bits) final ∧
      final.state = .inl answer ∧ (∀ i, final.tapes (engineSlot F M out i) = m.tapes i) := by
  have hfront := front_trace F M out hf
  rw [front_initial] at hfront
  obtain ⟨final, heng, hrel⟩ := engine_trace F M out hm _ (handoff F M out hfh hword)
  refine ⟨final, hfront.trans heng, ?_, hrel.2⟩
  exact hrel.1.trans (congrArg (engineState F M) hmh)

/-- Specialization to the ACCEPTED complete canonical frontend. M remains an
explicit arbitrary machine; supplying its actual run is not asserting a SAT solver. -/
noncomputable abbrev queryMachine (M : PrimitiveMachine) :=
  machine QueryCanonicalCompleted.sourceMachine M QueryCanonicalCompleted.outputIndex

theorem query_then_engine (M : PrimitiveMachine) (q : SATRequest)
    {nm : Nat} {m : M.Cfg} {answer : Bool}
    (hm : Trace M.step nm (M.init (Encoding.encodeCNF (FormulaBridge.formula q.formula))) m)
    (hmh : m.state = .inl answer) :
    ∃ steps final, Trace (queryMachine M).step steps ((queryMachine M).init (QueryCodec.encode q)) final ∧
      steps ≤ 7 * QueryCanonicalController.timeBound q + nm ∧ final.state = .inl answer := by
  obtain ⟨nf, f, hf, hnf, hfh, hword⟩ := QueryCanonicalCompleted.primitive_run q
  obtain ⟨final, ht, hh, _⟩ := sequential_trace QueryCanonicalCompleted.sourceMachine M
    QueryCanonicalCompleted.outputIndex (QueryCodec.encode q)
    (Encoding.encodeCNF (FormulaBridge.formula q.formula)) hf hfh hword hm hmh
  exact ⟨nf + nm, final, ht, Nat.add_le_add_right hnf nm, hh⟩

end QecReliability.ExternalSATBridge.PrimitiveLink
