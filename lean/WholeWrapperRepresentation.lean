import WholeWrapperController

/-! Representation bound CONDITIONAL on explicit register/list
invariants. Reachability preservation of those invariants is still open.
This is not a proof of a native heap or tape-space bound. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

private def boolWord (b : Bool) : ℕ := if b then 1 else 0

private def pcWord : PC → ℕ
  | .fetch => 0 | .prefix => 1 | .compile => 2 | .invoke => 3 | .resume => 4
  | .reverseCells => 5 | .selectScan => 6 | .trialCommit => 7
  | .sortNext => 8 | .insertScan => 9 | .insertRestore => 10 | .medianLookup => 11
  | .reverseGood => 12 | .reverseBad => 13 | .endpointZero => 14 | .endpointOne => 15
  | .repair => 16 | .reverseOutput => 17 | .done => 18 | .fault => 19

private def opcodeWords : Opcode → List ℕ
  | .beginCoefficient side j => [0,boolWord side,j]
  | .base rep => [1,rep,0]
  | .cell scale => [2,scale,0]
  | .select => [3,0,0] | .median => [4,0,0] | .store => [5,0,0] | .finish => [6,0,0]

private def requestWords : RequestKey → List ℕ
  | .base side j rep => [0,boolWord side,j,rep,0]
  | .cell side j rep scale _ => [1,boolWord side,j,rep,scale]

private def requestPrefix : RequestKey → List Bool
  | .base _ _ _ => []
  | .cell _ _ _ _ pre => pre

private def entryWords (xs : List Entry) : List ℕ := xs.flatMap (fun x => [x.1,x.2])
private def ratioWords (xs : List RationalOutput.Ratio) : List ℕ :=
  xs.flatMap (fun x => [x.num,x.den])

/-- Field lengths are encoded separately, so table boundaries are not erased.
All proof fields in Ratio are intentionally erased; every data field remains. -/
def configFields (s : Config) : List (List ℕ) :=
  [[pcWord s.pc,boolWord s.good,s.coefficient,s.repetition,s.scale,boolWord s.nonempty,
    (match s.returnTag with | .base => 0 | .prefix => 1),boolWord s.reply,
    s.cellCalls,s.trialCalls,s.coefficientCalls,s.selected,s.selectIndex,s.scaleFactor,
    s.insertValue,s.lookupRemaining,s.repairIndex,s.pairVisits,s.ratioBuilds,
    s.orderComparisons,s.endpointTests,s.maxAccumulatorDen],
   s.code.flatMap opcodeWords,requestWords s.request,
   (requestPrefix s.request).map boolWord,
   entryWords s.cellsRev,entryWords s.pairSrc,entryWords s.pairDst,
   entryWords s.trialsRev,s.sortTodo,s.sorted,s.insertLeftRev,s.insertRight,s.insertResult,
   entryWords s.goodRev,entryWords s.badRev,entryWords s.goodTable,entryWords s.badTable,
   entryWords s.repairGood,entryWords s.repairBad,
   ratioWords [s.endpoint0,s.endpoint1,s.previous],ratioWords s.outputRev,ratioWords s.output]

@[simp] theorem configFields_length (s : Config) : (configFields s).length=22 := by
  rfl

def fieldBits (xs : List ℕ) : List Bool :=
  QueryCodec.natHeader xs.length ++ xs.flatMap QueryCodec.natHeader

def fieldsBits (xs : List (List ℕ)) : List Bool :=
  QueryCodec.natHeader xs.length ++ xs.flatMap fieldBits

/-- The current serialized SAT query is retained while the engine runs. The
request prefix, prefix stack, opcode continuation, and all table headers are
also represented. No previous-query history is present. -/
def representedBits (s : Config) : List Bool :=
  fieldsBits (configFields s) ++
    QueryCodec.natHeader s.query.length ++ s.query ++
    PrefixTransitions.configBits s.prefixState

private theorem headerSum_bound (xs : List ℕ) (V : ℕ)
    (h : ∀ x∈xs, x≤V) :
    (xs.flatMap QueryCodec.natHeader).length≤xs.length*(2*V.size+1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := Nat.size_le_size (h x (by simp))
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.flatMap_cons,List.length_append,QueryCodec.natHeader_length,
        List.length_cons]
      nlinarith

theorem fieldBits_bound (xs : List ℕ) (L V : ℕ) (hl : xs.length≤L)
    (hv : ∀ x∈xs, x≤V) :
    (fieldBits xs).length≤2*L.size+1+L*(2*V.size+1) := by
  have hh := Nat.size_le_size hl
  have hs := (headerSum_bound xs V hv).trans (Nat.mul_le_mul_right _ hl)
  simp only [fieldBits,List.length_append,QueryCodec.natHeader_length]
  omega

private theorem fieldsSum_bound (xs : List (List ℕ)) (L V : ℕ)
    (hl : ∀ field∈xs, field.length≤L)
    (hv : ∀ field∈xs, ∀ x∈field, x≤V) :
    (xs.flatMap fieldBits).length≤xs.length*(2*L.size+1+L*(2*V.size+1)) := by
  induction xs with
  | nil => simp
  | cons field xs ih =>
      have hf := fieldBits_bound field L V (hl field (by simp)) (hv field (by simp))
      have ht := ih (fun f hf => hl f (by simp [hf]))
        (fun f hf => hv f (by simp [hf]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      nlinarith

theorem fieldsBits_bound (xs : List (List ℕ)) (K L V : ℕ)
    (hk : xs.length≤K) (hl : ∀ field∈xs, field.length≤L)
    (hv : ∀ field∈xs, ∀ x∈field, x≤V) :
    (fieldsBits xs).length≤2*K.size+1+K*(2*L.size+1+L*(2*V.size+1)) := by
  have hh := Nat.size_le_size hk
  have hs := (fieldsSum_bound xs L V hl hv).trans (Nat.mul_le_mul_right _ hk)
  simp only [fieldsBits,List.length_append,QueryCodec.natHeader_length]
  omega

/-- Explicit invariant, not a proved invariant of reachable wrapper states. -/
structure RepresentationInvariant (q B Q K L V : ℕ) (s : Config) : Prop where
  fields : (configFields s).length≤K
  fieldLengths : ∀ f∈configFields s, f.length≤L
  values : ∀ f∈configFields s, ∀ x∈f, x≤V
  query : s.query.length≤Q
  «prefix» : PrefixTransitions.Valid q (4*B+1) s.prefixState

/-- Conditional bit bound with no suppression of length headers or indices. -/
theorem representedBits_bound (q B Q K L V : ℕ) (s : Config)
    (h : RepresentationInvariant q B Q K L V s) :
    (representedBits s).length≤
      2*K.size+1+K*(2*L.size+1+L*(2*V.size+1))+
      (2*Q.size+1)+Q+PrefixTransitions.configBitBound q (4*B+1) := by
  have hf := fieldsBits_bound (configFields s) K L V h.fields h.fieldLengths h.values
  have hquery := h.query
  have hq := Nat.size_le_size h.query
  have hp := PrefixTransitions.configBits_length h.prefix
  simp only [representedBits,List.length_append,QueryCodec.natHeader_length]
  omega

end QecReliability.OracleCost.WholeWrapperCandidate
