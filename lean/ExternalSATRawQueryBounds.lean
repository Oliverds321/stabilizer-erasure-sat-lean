import ExternalSATRawQueryLowering

/-! Explicit resource envelopes for the actual raw-query controller's measured
source budget. Output length is bounded separately; it is NOT used as a substitute
for a visited-space proof. The resource convention is dimension plus binary input. -/
namespace QecReliability.ExternalSATBridge.RawQueryBounds

open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT

def extent (q : SATRequest) : ℕ := q.varCount + (QueryCodec.encode q).length

theorem code_succ_le {v : ℕ} (l : PrefixCNF.Literal v) :
    Encoding.literalCode (⟨l.1, l.2⟩ : SAT.Literal (Fin v)) + 1 ≤ 2 * v := by
  have h := Encoding.literalCode_lt (⟨l.1, l.2⟩ : SAT.Literal (Fin v))
  omega

theorem fields_length_le {v : ℕ} (c : List (PrefixCNF.Literal v)) :
    (RawClauseParser.fields c).length ≤ c.length * (2 * v) := by
  induction c with
  | nil => simp [RawClauseParser.fields]
  | cons l c ih =>
    have hl := code_succ_le l
    simp only [RawClauseParser.fields, List.flatMap_cons, List.length_append,
      Encoding.length_encodeNat, List.length_cons] at ih ⊢
    nlinarith

theorem rawClause_length_le {v : ℕ} (c : List (PrefixCNF.Literal v)) (hw : c.length ≤ 3) :
    (RawClauseParser.rawClause c).length ≤ 2 + 6 * v := by
  have h := fields_length_le c
  have hm := Nat.mul_le_mul_right (2 * v) hw
  simp only [RawClauseParser.rawClause, List.length_append, QueryCodec.word_length]
  nlinarith

theorem output_length_le {v : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width 3 F) :
    (RawBodyParser.output F).length ≤ F.length * (2 + 6 * v) := by
  induction F with
  | nil => simp [RawBodyParser.output]
  | cons c F ih =>
    have hc := rawClause_length_le c (hw c (by simp))
    have ht := ih (fun d hd => hw d (by simp [hd]))
    simp only [RawBodyParser.output, List.flatMap_cons, List.length_append,
      List.length_cons] at ht ⊢
    nlinarith

def literalBudget (v : ℕ) : ℕ :=
  14 * (v.size + 1) + 15 + 32 * (2 * v) * (v.size + 2) + 3 * (2 * v)

theorem literalCost_le {v : ℕ} (l : PrefixCNF.Literal v) :
    RawClauseParser.literalCost l ≤ literalBudget v := by
  have hc := code_succ_le l
  have hm := Nat.mul_le_mul_right (32 * (v.size + 2)) hc
  dsimp only [RawClauseParser.literalCost, RawLiteralEmitter.timeBound,
    RetainedLiteral.timeBound, literalBudget]
  nlinarith

theorem fieldCost_le {v : ℕ} (c : List (PrefixCNF.Literal v)) :
    RawClauseParser.fieldCost c ≤ c.length * literalBudget v := by
  induction c with
  | nil => simp [RawClauseParser.fieldCost]
  | cons l c ih =>
    have hl := literalCost_le l
    simp only [RawClauseParser.fieldCost, List.map_cons, List.sum_cons,
      List.length_cons] at ih ⊢
    nlinarith

theorem loopBound_le {v : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width 3 F) :
    RawBodyParser.loopBound F ≤ 1 + F.length * (13 + 3 * literalBudget v) := by
  induction F with
  | nil => simp [RawBodyParser.loopBound]
  | cons c F ih =>
    have hc := fieldCost_le c
    have hm := Nat.mul_le_mul_right (literalBudget v) (hw c (by simp))
    have ht := ih (fun d hd => hw d (by simp [hd]))
    simp only [RawBodyParser.loopBound, List.map_cons, List.sum_cons,
      List.length_cons] at ht ⊢
    nlinarith

/-- Every encoded clause carries two arity cells, including empty clauses. -/
theorem clauses_le_body (k : ℕ) (F : QueryCodec.PlainFormula) :
    F.length ≤ (QueryCodec.body k F).length := by
  induction F with
  | nil => simp [QueryCodec.body]
  | cons c F ih =>
    simp only [QueryCodec.body, List.flatMap_cons, List.length_append,
      QueryCodec.clause, QueryCodec.word_length, QueryCodec.literals_length,
      List.length_cons] at ih ⊢
    omega

theorem headers_le_binary (q : SATRequest) :
    q.varCount.size ≤ (QueryCodec.encode q).length ∧
      q.formula.length.size ≤ (QueryCodec.encode q).length := by
  simp only [QueryCodec.encode, List.length_append, QueryCodec.natHeader_length]
  omega

theorem clauses_le_binary (q : SATRequest) :
    q.formula.length ≤ (QueryCodec.encode q).length := by
  have h := clauses_le_body q.varCount.size (QueryCodec.plain q.formula)
  simp only [QueryCodec.plain, List.length_map] at h
  simp only [QueryCodec.encode, List.length_append, QueryCodec.plain, List.length_map]
  omega

theorem query_sizes (q : SATRequest) :
    q.varCount ≤ extent q ∧ q.varCount.size ≤ extent q ∧
      q.formula.length.size ≤ extent q ∧ q.formula.length ≤ extent q := by
  have hh := headers_le_binary q
  have hm := clauses_le_binary q
  dsimp only [extent]
  omega

theorem literalBudget_polynomial (q : SATRequest) :
    literalBudget q.varCount ≤ 256 * (extent q + 1) ^ 2 := by
  obtain ⟨hv, hs, _, _⟩ := query_sizes q
  have hm := Nat.mul_le_mul (by omega : 2 * q.varCount ≤ 2 * extent q)
    (by omega : q.varCount.size + 2 ≤ extent q + 2)
  dsimp only [literalBudget]
  nlinarith

theorem preparation_polynomial (q : SATRequest) :
    QueryPreparation.timeBound q.varCount q.formula.length ≤ 256 * (extent q + 1) ^ 2 := by
  obtain ⟨_, hv, hm, _⟩ := query_sizes q
  have hs := Nat.mul_le_mul hv hv
  dsimp only [QueryPreparation.timeBound, WidthPreparation.timeBound]
  nlinarith

theorem output_length_polynomial (q : SATRequest) :
    (RawBodyParser.output q.formula).length ≤ 8 * (extent q + 1) ^ 2 := by
  have h := output_length_le q.formula q.width
  obtain ⟨hv, _, _, hm⟩ := query_sizes q
  have hp := Nat.mul_le_mul hm (by omega : 2 + 6 * q.varCount ≤ 2 + 6 * extent q)
  nlinarith

theorem timeBound_polynomial (q : SATRequest) :
    RawQueryLowering.timeBound q ≤ 4096 * (extent q + 1) ^ 3 := by
  have hprep := preparation_polynomial q
  have hout := output_length_polynomial q
  have hbudget := literalBudget_polynomial q
  have hlo := loopBound_le q.formula q.width
  have hm := (query_sizes q).2.2.2
  have hpos : 1 ≤ extent q + 1 := by omega
  have hone2 : 1 ≤ (extent q + 1) ^ 2 := Nat.succ_le_of_lt (by positivity)
  have hone3 : 1 ≤ (extent q + 1) ^ 3 := Nat.succ_le_of_lt (by positivity)
  have hpow : (extent q + 1) ^ 2 ≤ (extent q + 1) ^ 3 := by
    calc
      (extent q + 1) ^ 2 = (extent q + 1) ^ 2 * 1 := by omega
      _ ≤ (extent q + 1) ^ 2 * (extent q + 1) := Nat.mul_le_mul_left _ hpos
      _ = (extent q + 1) ^ 3 := by ring
  have hclause : 13 + 3 * literalBudget q.varCount ≤ 800 * (extent q + 1) ^ 2 := by
    omega
  have hprod := Nat.mul_le_mul (by omega : q.formula.length ≤ extent q + 1) hclause
  have hloop : RawBodyParser.loopBound q.formula ≤ 1 + 800 * (extent q + 1) ^ 3 := by
    nlinarith
  dsimp only [RawQueryLowering.timeBound]
  omega

end QecReliability.ExternalSATBridge.RawQueryBounds
