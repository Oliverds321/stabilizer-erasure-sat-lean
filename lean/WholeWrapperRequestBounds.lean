import WholeWrapperReachableBounds

/-! Actual opcode operands, reachable request indices, and the
single currently retained serialized SAT query. No whole-state bound premise. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- Operand validity is supplied by the real finite schedule, not advice. -/
def OpcodeBound (q r m : ℕ) : Opcode → Prop
  | .beginCoefficient _ j => j≤r
  | .base rep => rep<2*m+1
  | .cell scale => scale≤q
  | _ => True

theorem trialCode_op_bound {q r m rep : ℕ} (hrep : rep<2*m+1)
    {op : Opcode} (h : op∈trialCode q rep) : OpcodeBound q r m op := by
  simp only [trialCode,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with (rfl | h) | rfl
  · exact hrep
  · obtain ⟨scale,hs,rfl⟩ := List.mem_map.mp h
    exact Nat.le_of_lt_succ (List.mem_range.mp hs)
  · trivial

theorem coefficientCode_op_bound {q r m j : ℕ} (hj : j≤r) (side : Bool)
    {op : Opcode} (h : op∈coefficientCode q m side j) : OpcodeBound q r m op := by
  simp only [coefficientCode,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with (rfl | h) | rfl | rfl
  · exact hj
  · obtain ⟨rep,hrep,hop⟩ := List.mem_flatMap.mp h
    exact trialCode_op_bound (List.mem_range.mp hrep) hop
  · trivial
  · trivial

theorem program_op_bound {q r m : ℕ} {op : Opcode}
    (h : op∈program q r m) : OpcodeBound q r m op := by
  simp only [program,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with (h | h) | rfl
  · obtain ⟨j,hj,hop⟩ := List.mem_flatMap.mp h
    exact coefficientCode_op_bound (Nat.le_of_lt_succ (List.mem_range.mp hj)) true hop
  · obtain ⟨j,hj,hop⟩ := List.mem_flatMap.mp h
    exact coefficientCode_op_bound (Nat.le_of_lt_succ (List.mem_range.mp hj)) false hop
  · trivial

/-- Extract the current prefix bound directly from the checked native
ControlOK/StackOK relation, including while the wrapper intercepts Await. -/
theorem native_await_prefix_length {q B depth cap : ℕ}
    {state : PrefixTransitions.Config} {pre : List Bool}
    (h : PrefixTransitions.Valid q (4*B+1) state)
    (hc : state.control=.await depth pre cap) : pre.length≤q := by
  obtain ⟨d,b,hcontrol,hstack⟩ := h
  rw [hc] at hcontrol
  change depth=d ∧ cap=b ∧ pre.length+depth=q ∧ 0<cap at hcontrol
  omega

structure RequestInvariant (q r m : ℕ) (s : Config) : Prop where
  code : ∀ op∈s.code, OpcodeBound q r m op
  coefficient : s.coefficient≤r
  repetition : s.repetition<2*m+1
  scale : s.scale≤q
  request : ValidKey q r m s.request

theorem initial_request_invariant (q r m : ℕ) :
    RequestInvariant q r m (initial q r m) := by
  constructor
  · exact fun _ h => program_op_bound h
  · exact Nat.zero_le r
  · change 0<2*m+1
    omega
  · exact Nat.zero_le q
  · change 0<r+1 ∧ 0<2*m+1
    omega

set_option maxHeartbeats 800000 in
theorem step_request_invariant {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge}
    (hnative : PrefixTransitions.Valid q (4*B+1) s.prefixState)
    (hs : RequestInvariant q r m s)
    (he : step q r B m shape ext s=some edge) :
    RequestInvariant q r m edge.next := by
  have hpre : ∀ depth pre cap,
      s.prefixState.control=.await depth pre cap → pre.length≤q :=
    fun _ _ _ hc => native_await_prefix_length hnative hc
  rcases hs with ⟨hcode,hcoefficient,hrepetition,hscale,hrequest⟩
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge,OpcodeBound,ValidKey]
  all_goals constructor <;> try simp_all [OpcodeBound,ValidKey]
  all_goals first | omega | aesop

theorem reachable_request_invariant {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    RequestInvariant q r m s := by
  obtain ⟨totals,events,h⟩ := h
  have both := h.preserves
    (fun s => PrefixTransitions.Valid q (4*B+1) s.prefixState ∧
      RequestInvariant q r m s)
    (by intro s e hs he; exact ⟨step_prefix_valid hs.1 he,
        step_request_invariant hs.1 hs.2 he⟩)
    ⟨initial_prefix_valid q r B m,initial_request_invariant q r m⟩
  exact both.2

/-- A local frontend size contract on typed requests. It will be discharged
below by the exact original encoder and explicit hash-circuit gate bound. -/
def QueryBound (q r m Q : ℕ) (ext : External) : Prop :=
  ∀ key, ValidKey q r m key → (ext.compileQuery key).bits.length≤Q

theorem step_query_bound {q r B m Q : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge} (hfront : QueryBound q r m Q ext)
    (hreq : RequestInvariant q r m s) (hq : s.query.length≤Q)
    (he : step q r B m shape ext s=some edge) : edge.next.query.length≤Q := by
  have hb := hfront s.request hreq.request
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals try simp_all [localEdge]

theorem reachable_query_bound {q r B m Q : ℕ} {shape : Bool} {ext : External}
    {s : Config} (hfront : QueryBound q r m Q ext)
    (h : Reachable q r B m shape ext s) : s.query.length≤Q := by
  obtain ⟨totals,events,h⟩ := h
  have all := h.preserves
    (fun s => PrefixTransitions.Valid q (4*B+1) s.prefixState ∧
      RequestInvariant q r m s ∧ s.query.length≤Q)
    (by intro s e hs he; exact ⟨step_prefix_valid hs.1 he,
        step_request_invariant hs.1 hs.2.1 he,
        step_query_bound hfront hs.2.1 hs.2.2 he⟩)
    ⟨initial_prefix_valid q r B m,initial_request_invariant q r m,by simp [initial]⟩
  exact all.2.2

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))
    (service : SATService) (m : ℕ) (ω : Fin (2*m+1) → Ω)

/-- The buffer bound is for the SAME padded serialization used by EncodedSAT.
This is a representation-size theorem, not a construction-time theorem. -/
theorem concrete_query_bound (D g : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)
    (hg : ∀ scale seed, (K.program scale seed).gates≤g) :
    QueryBound (keySize n r) r m (QuantumService.engineInputBound rows C D g) ext := by
  intro key hvalid
  rw [hboundary.query key hvalid]
  cases key with
  | base side j rep =>
      change (QueryCodec.encode (padRequest D
        (QuantumService.baseRequest rows C (side,⟨j,hvalid.1⟩) []))).length≤_
      have hd := QuantumService.base_dimensions rows C g (side,⟨j,hvalid.1⟩) []
      exact (padRequest_size _ hd.1 hd.2 (D:=D)).2
  | cell side j rep scale pre =>
      change (QueryCodec.encode (padRequest D
        (QuantumService.cellRequest rows C H K (side,⟨j,hvalid.1⟩)
          ⟨scale,hvalid.2.2.1⟩ (ω ⟨rep,hvalid.2.1⟩) pre))).length≤_
      have hd := QuantumService.cell_dimensions rows C H K g
        (side,⟨j,hvalid.1⟩) ⟨scale,hvalid.2.2.1⟩ (ω ⟨rep,hvalid.2.1⟩) pre
        (hg _ _)
      exact (padRequest_size _ hd.1 hd.2 (D:=D)).2

/-- Actual reachable query buffers inherit the concrete circuit/CNF bound.
No arbitrary whole representation theorem is supplied as a hypothesis. -/
theorem reachable_concrete_query_bound (B D g : ℕ) (shape : Bool) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)
    (hg : ∀ scale seed, (K.program scale seed).gates≤g)
    {s : Config} (h : Reachable (keySize n r) r B m shape ext s) :
    s.query.length≤QuantumService.engineInputBound rows C D g :=
  reachable_query_bound (concrete_query_bound rows C H K service m ω D g ext hboundary hg) h

end QecReliability.OracleCost.WholeWrapperCandidate
