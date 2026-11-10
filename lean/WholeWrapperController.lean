import OracleCost.PrefixEngine
import OracleCost.EnginePhysical
import OracleCost.CachedRefinement

/-!
This is a first-order *macro* controller, not a
bit-machine implementation and not a total-complexity theorem. The existing
PrefixTransitions.Config/step is the ONLY pre traversal used.
The interpreter arguments are external interpretations, NEVER stored closures.
Query construction, external SAT execution, and endpoint acquisition have
separate charged interfaces. Their finite-machine refinements remain open.
-/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open RationalOutput

inductive Opcode where
  | beginCoefficient (good : Bool) (coefficient : ℕ)
  | base (repetition : ℕ)
  | cell (scale : ℕ)
  | select
  | median
  | store
  | finish
  deriving DecidableEq

/-- The continuation is a finite instruction list, not a function. Each true
base trial executes every scale; selection is AFTER the entire cell block. -/
def trialCode (q rep : ℕ) : List Opcode :=
  [.base rep] ++ (List.range (q+1)).map Opcode.cell ++ [.select]

def coefficientCode (q m : ℕ) (side : Bool) (j : ℕ) : List Opcode :=
  [.beginCoefficient side j] ++
    (List.range (2*m+1)).flatMap (trialCode q) ++ [.median,.store]

def program (q r m : ℕ) : List Opcode :=
  (List.range (r+1)).flatMap (coefficientCode q m true) ++
  (List.range (r+1)).flatMap (coefficientCode q m false) ++ [.finish]

def coefficientCodeLength (q m : ℕ) : ℕ := (2*m+1)*(q+3)+3

theorem trialCode_length (q rep : ℕ) : (trialCode q rep).length=q+3 := by
  simp [trialCode]

theorem flatMap_const_length {α β : Type*} (xs : List α) (f : α → List β)
    (L : ℕ) (h : ∀ x, (f x).length=L) : (xs.flatMap f).length=xs.length*L := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [h,ih,Nat.add_mul,Nat.add_comm]

theorem coefficientCode_length (q m : ℕ) (side : Bool) (j : ℕ) :
    (coefficientCode q m side j).length=coefficientCodeLength q m := by
  have h := flatMap_const_length (List.range (2*m+1)) (trialCode q) (q+3)
    (trialCode_length q)
  simp only [coefficientCode,List.length_append,List.length_cons,List.length_nil,
    h,List.length_range,coefficientCodeLength]
  omega

theorem program_length (q r m : ℕ) :
    (program q r m).length=2*(r+1)*coefficientCodeLength q m+1 := by
  have ht := flatMap_const_length (List.range (r+1))
    (coefficientCode q m true) _ (coefficientCode_length q m true)
  have hf := flatMap_const_length (List.range (r+1))
    (coefficientCode q m false) _ (coefficientCode_length q m false)
  simp only [program,List.length_append,List.length_cons,List.length_nil]
  rw [ht,hf]
  simp [List.length_range,Nat.mul_assoc,Nat.two_mul,Nat.add_assoc,Nat.add_mul]

/-- All constructor tags are fixed and finite; all indices live in registers.
`compile` and the endpoint phases are charged SUBROUTINE BOUNDARIES, not O(1)
claims. `invoke` is the sole external-SAT-call phase. -/
inductive PC where
  | fetch | «prefix» | compile | invoke | resume
  | reverseCells | selectScan | trialCommit
  | sortNext | insertScan | insertRestore | medianLookup
  | reverseGood | reverseBad | endpointZero | endpointOne
  | repair | reverseOutput | done | fault
  deriving DecidableEq

instance : Fintype PC := ⟨{.fetch,.prefix,.compile,.invoke,.resume,.reverseCells,
  .selectScan,.trialCommit,.sortNext,.insertScan,.insertRestore,.medianLookup,
  .reverseGood,.reverseBad,.endpointZero,.endpointOne,.repair,.reverseOutput,.done,.fault},
  by intro pc; cases pc <;> simp⟩

inductive ReturnTag where
  | base | «prefix»
  deriving DecidableEq

instance : Fintype ReturnTag := ⟨{.base,.prefix},by intro tag; cases tag <;> simp⟩

inductive RequestKey where
  | base (good : Bool) (coefficient repetition : ℕ)
  | cell (good : Bool) (coefficient repetition scale : ℕ) (pre : List Bool)
  deriving DecidableEq

structure BuiltQuery where
  bits : List Bool
  constructionTime : ℕ
  constructionSpace : ℕ

structure EndpointResult where
  value : Ratio
  time : ℕ
  space : ℕ

/-- NOT an existence theorem. The frontend must later be implemented by a
finite bit program with these observations; the exact contracts are separate.
Input seeds/circuit/rows belong to read-only input, addressed by these indices. -/
structure External where
  compileQuery : RequestKey → BuiltQuery
  sat : List Bool → SATReply
  endpoint : Bool → EndpointResult

abbrev Entry := ℕ × ℕ

def oneRatio : Ratio := ⟨1,1,by omega,by omega⟩
def emptyReply : SATReply := ⟨false,0,0⟩

/-- Decoded representation: only finite tags, natural/Boolean registers,
Boolean buffers, ratio records, finite lists, and the OLD pre Config. -/
structure Config where
  pc : PC := .fetch
  code : List Opcode := []
  good : Bool := true
  coefficient : ℕ := 0
  repetition : ℕ := 0
  scale : ℕ := 0
  nonempty : Bool := false
  returnTag : ReturnTag := .base
  request : RequestKey := .base true 0 0
  query : List Bool := []
  reply : Bool := false
  prefixState : PrefixTransitions.Config := ⟨.ret 0,[]⟩
  cellCalls : ℕ := 0
  trialCalls : ℕ := 0
  coefficientCalls : ℕ := 0
  cellsRev : List Entry := []
  pairSrc : List Entry := []
  pairDst : List Entry := []
  trialsRev : List Entry := []
  selected : ℕ := 0
  selectIndex : ℕ := 0
  scaleFactor : ℕ := 1
  sortTodo : List ℕ := []
  sorted : List ℕ := []
  insertValue : ℕ := 0
  insertLeftRev : List ℕ := []
  insertRight : List ℕ := []
  insertResult : List ℕ := []
  lookupRemaining : ℕ := 0
  goodRev : List Entry := []
  badRev : List Entry := []
  goodTable : List Entry := []
  badTable : List Entry := []
  repairGood : List Entry := []
  repairBad : List Entry := []
  endpoint0 : Ratio := oneRatio
  endpoint1 : Ratio := oneRatio
  previous : Ratio := oneRatio
  repairIndex : ℕ := 0
  outputRev : List Ratio := []
  output : List Ratio := []
  pairVisits : ℕ := 0
  ratioBuilds : ℕ := 0
  orderComparisons : ℕ := 0
  endpointTests : ℕ := 0
  maxAccumulatorDen : ℕ := 1

structure Edge where
  next : Config
  /- Every edge has one controller-dispatch step; all cost fields below are
  additional observations, not charged as a single physical instruction. -/
  calls : ℕ := 0
  oracleTime : ℕ := 0
  frontendTime : ℕ := 0
  endpointTime : ℕ := 0
  boundarySpace : ℕ := 0
  event : Option RequestKey := none

def localEdge (s : Config) : Option Edge := some ⟨s,0,0,0,0,0,none⟩

def initial (q r m : ℕ) : Config := { code := program q r m }

/-- A finite-control interpreter. List reversals, insertion-sort comparisons,
and median lookup are explicit loops. Nat/Ratio arithmetic is still macro
arithmetic and must be lowered with operand-bit costs, not unit costs. -/
def step (q r B m : ℕ) (shape : Bool) (ext : External) (s : Config) : Option Edge :=
  match s.pc with
  | .done | .fault => none
  | .fetch =>
    match s.code with
    | [] => localEdge { s with pc := .fault }
    | op::rest =>
      let t := { s with code := rest }
      match op with
      | .beginCoefficient side j => localEdge { t with
          good := side, coefficient := j,
          trialsRev := [], coefficientCalls := 0 }
      | .base rep => localEdge { t with
          pc := .compile, repetition := rep,
          returnTag := .base, request := .base s.good s.coefficient rep,
          cellsRev := [], trialCalls := 0, nonempty := false }
      | .cell scale =>
          if s.nonempty then localEdge { t with
            pc := .prefix, scale := scale,
            cellCalls := 0, prefixState := ⟨.enter q [] (4*B+1),[]⟩ }
          else localEdge t
      | .select =>
          if s.nonempty then localEdge { t with
            pc := .reverseCells,
            pairSrc := s.cellsRev, pairDst := [], cellsRev := [] }
          else localEdge { t with pc := .trialCommit, selected := 0 }
      | .median => localEdge { t with
          pc := .sortNext,
          sortTodo := s.trialsRev.map Prod.fst, sorted := [] }
      | .store =>
          if s.good then localEdge { t with goodRev := (s.selected,s.coefficientCalls)::s.goodRev }
          else localEdge { t with badRev := (s.selected,s.coefficientCalls)::s.badRev }
      | .finish => localEdge { t with
          pc := .reverseGood,
          pairSrc := s.goodRev, pairDst := [], goodRev := [] }
  | .prefix =>
      match s.prefixState.control with
      | .await _ pre _ => localEdge { s with
          pc := .compile, returnTag := .prefix,
          request := .cell s.good s.coefficient s.repetition s.scale pre }
      | _ =>
          match PrefixTransitions.step (fun _ => emptyReply) s.prefixState with
          | some e => localEdge { s with prefixState := e.next }
          | none =>
              match s.prefixState.control with
              | .ret count => localEdge { s with
                  pc := .fetch,
                  cellsRev := (count,s.cellCalls)::s.cellsRev,
                  trialCalls := s.trialCalls+s.cellCalls }
              | _ => localEdge { s with pc := .fault }
  | .compile =>
      let built := ext.compileQuery s.request
      some ⟨{ s with
        pc := .invoke, query := built.bits },0,0,
        built.constructionTime,0,built.constructionSpace,none⟩
  | .invoke =>
      let reply := ext.sat s.query
      some ⟨{ s with
        pc := .resume, reply := reply.value },1,reply.time,
        0,0,reply.workspace,some s.request⟩
  | .resume =>
      match s.returnTag with
      | .base => localEdge { s with
          pc := .fetch, nonempty := s.reply,
          trialCalls := 1, query := [] }
      | .prefix =>
          match PrefixTransitions.step (fun _ => ⟨s.reply,0,0⟩) s.prefixState with
          | some e => localEdge { s with
              pc := .prefix,
              prefixState := e.next, cellCalls := s.cellCalls+1, query := [] }
          | none => localEdge { s with pc := .fault }
  | .reverseCells =>
      match s.pairSrc with
      | [] => localEdge { s with
          pc := .selectScan,
          pairSrc := s.pairDst, pairDst := [], selectIndex := 0, scaleFactor := 1 }
      | x::xs => localEdge { s with pairSrc := xs, pairDst := x::s.pairDst }
  | .selectScan =>
      match s.pairSrc with
      | [] => localEdge { s with pc := .trialCommit, selected := 1 }
      | x::xs =>
          if x.1≤4*B then localEdge { s with
            pc := .trialCommit,
            selected := max 1 (s.scaleFactor*x.1), pairSrc := [] }
          else localEdge { s with
            pairSrc := xs,
            selectIndex := s.selectIndex+1, scaleFactor := 2*s.scaleFactor }
  | .trialCommit => localEdge { s with
      pc := .fetch,
      trialsRev := (s.selected,s.trialCalls)::s.trialsRev,
      coefficientCalls := s.coefficientCalls+s.trialCalls }
  | .sortNext =>
      match s.sortTodo with
      | [] => localEdge { s with
          pc := .medianLookup,
          insertRight := s.sorted, lookupRemaining := m }
      | x::xs => localEdge { s with
          pc := .insertScan, sortTodo := xs,
          insertValue := x, insertLeftRev := [], insertRight := s.sorted }
  | .insertScan =>
      match s.insertRight with
      | [] => localEdge { s with pc := .insertRestore, insertResult := [s.insertValue] }
      | y::ys =>
          if s.insertValue≤y then localEdge { s with
            pc := .insertRestore,
            insertResult := s.insertValue::s.insertRight }
          else localEdge { s with insertRight := ys, insertLeftRev := y::s.insertLeftRev }
  | .insertRestore =>
      match s.insertLeftRev with
      | [] => localEdge { s with
          pc := .sortNext, sorted := s.insertResult,
          insertRight := [], insertResult := [] }
      | y::ys => localEdge { s with insertLeftRev := ys, insertResult := y::s.insertResult }
  | .medianLookup =>
      match s.insertRight with
      | [] => localEdge { s with pc := .fault }
      | x::xs =>
          if s.lookupRemaining=0 then localEdge { s with
            pc := .fetch,
            selected := x, insertRight := [], sortTodo := [], sorted := [], trialsRev := [] }
          else localEdge { s with insertRight := xs, lookupRemaining := s.lookupRemaining-1 }
  | .reverseGood =>
      match s.pairSrc with
      | [] => localEdge { s with
          pc := .reverseBad, goodTable := s.pairDst,
          pairSrc := s.badRev, pairDst := [], badRev := [] }
      | x::xs => localEdge { s with pairSrc := xs, pairDst := x::s.pairDst }
  | .reverseBad =>
      match s.pairSrc with
      | [] => localEdge { s with pc := .endpointZero, badTable := s.pairDst, pairDst := [] }
      | x::xs => localEdge { s with pairSrc := xs, pairDst := x::s.pairDst }
  | .endpointZero =>
      let e := ext.endpoint false
      some ⟨{ s with pc := .endpointOne, endpoint0 := e.value },0,0,0,e.time,e.space,none⟩
  | .endpointOne =>
      let e := ext.endpoint true
      some ⟨{ s with
        pc := .repair, endpoint1 := e.value, previous := s.endpoint0,
        repairGood := s.goodTable, repairBad := s.badTable, repairIndex := 0,
        outputRev := [], maxAccumulatorDen := s.endpoint0.den },0,0,0,e.time,e.space,none⟩
  | .repair =>
      match s.repairGood,s.repairBad with
      | [],[] => localEdge { s with pc := .reverseOutput, output := [] }
      | g::gs,b::bs =>
          let e := LinearRepair.sourceEntry r s.endpoint0 s.endpoint1 s.repairIndex g b
          let current := if s.repairIndex=0 then e else Ratio.lesser s.previous e
          let out := if shape then Ratio.greater s.endpoint1 current else e
          localEdge { s with
            repairGood := gs, repairBad := bs,
            repairIndex := s.repairIndex+1, previous := current, outputRev := out::s.outputRev,
            pairVisits := s.pairVisits+1,
            ratioBuilds := s.ratioBuilds+(if s.repairIndex=0 ∨ s.repairIndex=r then 0 else 1),
            orderComparisons := s.orderComparisons+(if s.repairIndex=0 then 0 else 1)+(if shape then 1 else 0),
            endpointTests := s.endpointTests+(if s.repairIndex=0 then 1 else 2),
            maxAccumulatorDen := max s.maxAccumulatorDen
              (max s.previous.den (max e.den (max current.den out.den))) }
      | _,_ => localEdge { s with pc := .fault }
  | .reverseOutput =>
      match s.outputRev with
      | [] => localEdge { s with pc := .done }
      | x::xs => localEdge { s with outputRev := xs, output := x::s.output }

/-- The single SAT boundary is syntactically isolated from all postprocessing. -/
theorem calls_zero_outside_invoke (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (edge : Edge) (hpc : s.pc≠.invoke)
    (h : step q r B m shape ext s=some edge) : edge.calls=0 := by
  cases hp : s.pc <;> simp only [step,hp] at h
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at h; subst edge; rfl)
    | split at h

/-- The native pre transition at Await consumes only the current reply.
This is why an intercepted request can resume the SAME checked pre machine. -/
theorem prefix_await_reply (oracle : List Bool → SATReply) (depth cap : ℕ)
    (pre : List Bool) (stack : List PrefixTransitions.Frame) :
    PrefixTransitions.step (fun _ => oracle pre) ⟨.await depth pre cap,stack⟩=
      PrefixTransitions.step oracle ⟨.await depth pre cap,stack⟩ := by
  rfl

/-- Time/space measurements remain ghost edge data, not retained runtime
registers. Erasing those two reply fields changes no next pre configuration. -/
theorem prefix_next_erase_charge (reply : SATReply) (state : PrefixTransitions.Config) :
    (PrefixTransitions.step (fun _ => ⟨reply.value,0,0⟩) state).map
      PrefixTransitions.Edge.next =
    (PrefixTransitions.step (fun _ => reply) state).map PrefixTransitions.Edge.next := by
  rcases state with ⟨control,stack⟩
  cases control with
  | enter => rfl
  | await => rfl
  | ret count => cases stack with
    | nil => rfl
    | cons frame stack => cases frame <;> rfl

/-- Existing halting/call-count result, imported rather than reimplemented. -/
theorem native_prefix_halts (q cap : ℕ) (oracle : List Bool → SATReply) :
    ∃ result, PrefixTransitions.run q oracle cap=some result ∧
      result.final=⟨.ret (PrefixMachine.execute q oracle [] cap).control.count,[]⟩ ∧
      result.calls=(PrefixMachine.execute q oracle [] cap).control.calls ∧
      result.serviceTime=(PrefixMachine.execute q oracle [] cap).control.oracleTime ∧
      result.steps≤5*result.calls+1 :=
  PrefixTransitions.run_spec q oracle cap

structure Totals where
  dispatches : ℕ := 0
  calls : ℕ := 0
  oracleTime : ℕ := 0
  frontendTime : ℕ := 0
  endpointTime : ℕ := 0
  boundaryPeak : ℕ := 0

def Totals.cons (edge : Edge) (rest : Totals) : Totals :=
  ⟨rest.dispatches+1,edge.calls+rest.calls,edge.oracleTime+rest.oracleTime,
    edge.frontendTime+rest.frontendTime,edge.endpointTime+rest.endpointTime,
    max edge.boundarySpace rest.boundaryPeak⟩

/-- Trace/event data are proof-only; Config contains no retained query history. -/
inductive Trace (q r B m : ℕ) (shape : Bool) (ext : External) :
    Config → Totals → List RequestKey → Config → Prop
  | nil (s) : Trace q r B m shape ext s {} [] s
  | cons {s edge t totals events} (he : step q r B m shape ext s=some edge)
      (tail : Trace q r B m shape ext edge.next totals events t) :
      Trace q r B m shape ext s (Totals.cons edge totals)
        (edge.event.toList++events) t

/-- Fuel is ONLY a partial interpreter definition. No use of this definition
below asserts that a guessed bound is sufficient. -/
def drive (q r B m : ℕ) (shape : Bool) (ext : External) : ℕ → Config → Option Config
  | 0,_ => none
  | fuel+1,s =>
      match step q r B m shape ext s with
      | none => some s
      | some edge => drive q r B m shape ext fuel edge.next

def cacheWidth (q B : ℕ) : ℕ := (2^q*(4*B+1)).size+1

def prefixCallCap (q B : ℕ) : ℕ := 1+2*q*(4*B+1)
def trialCallCap (q B : ℕ) : ℕ := 1+(q+1)*prefixCallCap q B

def totalCallCap (q r B m : ℕ) : ℕ := 2*(r+1)*(2*m+1)*trialCallCap q B

/-- A deliberately generous POLYNOMIAL candidate control-dispatch bound.
Its sufficiency is an explicit open controller theorem, not an assumption
silently folded into a theorem called total complexity. -/
def dispatchBound (q r B m : ℕ) : ℕ :=
  let k := 2*(r+1)
  let R := 2*m+1
  (program q r m).length + k*R*(8*(q+1)*prefixCallCap q B+8*q+20) +
    k*(2*R^2+5*R+m+5)+10*(r+1)+10

/-- Exact result fields required for equality with the source cache/repair.
The target is supplied independently; this is not a definition by execution. -/
def HasOutput (s : Config) (good bad : List Entry) (target : LinearRepair.Result) : Prop :=
  s.pc=.done ∧ s.goodTable=good ∧ s.badTable=bad ∧ s.output=target.values ∧
    s.pairVisits=target.pairVisits ∧ s.ratioBuilds=target.ratioBuilds ∧
    s.orderComparisons=target.orderComparisons ∧ s.endpointTests=target.endpointTests ∧
    s.maxAccumulatorDen=target.maxAccumulatorDen

end QecReliability.OracleCost.WholeWrapperCandidate
