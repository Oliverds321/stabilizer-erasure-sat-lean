import ExternalSATDFSOutputOrder
import ExternalSATClauseMatchSemantics
import ExternalSATCanonicalRawController

/-! Exact byte endpoint for the concrete canonical controller. This proves no
SAT-engine witness or resource theorem beyond the imported controller. -/
namespace QecReliability.ExternalSATBridge.CanonicalBytes

open OAI.Algorithms.SubexponentialSAT
open CandidateClauseEmitter (slots)

def rawClauses {v : ℕ} (F : PrefixCNF.Formula v) : List (List ℕ) :=
  F.map ClauseMatchSemantics.literalCodes

def entry (codes : List ℕ) : List Bool :=
  true :: Encoding.frame (Encoding.encodeList Encoding.encodeNat codes)

def entries (cs : List (List ℕ)) : List Bool := cs.flatMap entry

theorem occurs_native {v : ℕ} (F : PrefixCNF.Formula v) (codes : List ℕ)
    (hc : codes.length ≤ 3) :
    CandidateVisit.occurs (slots codes) (rawClauses F) =
      F.any (CanonicalEnumeration.clauseMatches codes) := by
  induction F with
  | nil => rfl
  | cons cl F ih =>
    simpa only [CandidateVisit.occurs, rawClauses, List.map_cons, List.any_cons,
      ClauseMatchSemantics.actual_matches codes hc cl] using
      congrArg (fun b => CanonicalEnumeration.clauseMatches codes cl || b) ih

theorem entry_slots (codes : List ℕ) (hc : codes.length ≤ 3) :
    CandidateClauseEmitter.entry (slots codes) = entry codes := by
  rw [CandidateClauseEmitter.entry, CandidateClauseEmitter.payload_slots codes hc]
  rfl

/-- The accumulated output is reversed physically; only matched entries are
prepended, with exactly the same Boolean predicate as the accepted selector. -/
theorem run_selected_entries {v : ℕ} (F : PrefixCNF.Formula v)
    (cs : List (List ℕ)) (hw : ∀ c ∈ cs, c.length ≤ 3) (out : List Bool) :
    DFSOutputOrder.run (rawClauses F) cs out =
      (entries (cs.filter (fun c => F.any (CanonicalEnumeration.clauseMatches c)))).reverse ++ out := by
  induction cs generalizing out with
  | nil => simp [DFSOutputOrder.run, entries]
  | cons c cs ih =>
    have hc := hw c (by simp)
    have ht : ∀ d ∈ cs, d.length ≤ 3 := fun d hd => hw d (by simp [hd])
    change DFSOutputOrder.run (rawClauses F) cs
      (CandidateVisit.output (slots c) (rawClauses F) out) = _
    rw [ih ht, CandidateVisit.output, occurs_native F c hc, entry_slots c hc]
    cases hm : F.any (CanonicalEnumeration.clauseMatches c) <;>
      simp [hm, entries, List.reverse_append, List.append_assoc]

theorem entries_terminated (cs : List (List ℕ)) :
    entries cs ++ [false] = Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simpa only [entries, List.flatMap_cons, entry, List.cons_append, List.append_assoc,
      Encoding.encodeList] using congrArg (fun tail => true :: (Encoding.frame
        (Encoding.encodeList Encoding.encodeNat c) ++ tail)) ih

theorem accumulator_eq {v : ℕ} (F : PrefixCNF.Formula v) :
    CanonicalRawController.accumulator v (rawClauses F) =
      (Encoding.encodeNat v ++ entries (CanonicalEnumeration.selected F)).reverse := by
  have horder := DFSOutputOrder.canonical_output_order (2 * v) (rawClauses F)
    (Encoding.encodeNat v).reverse
  have hwidth : ∀ c ∈ CanonicalEnumeration.candidates 3 0 (2 * v), c.length ≤ 3 := by
    intro c hc
    exact ((CanonicalEnumeration.mem_candidates 3 0 (2 * v) c).mp hc).1
  rw [run_selected_entries F _ hwidth] at horder
  simpa only [CanonicalRawController.accumulator, slots, CanonicalEnumeration.selected,
    List.reverse_append] using horder

/-- Literal equality with the actual external encodeCNF bytes, including all
empty cases. Duplicate clauses/literals are normalized by the real selector. -/
theorem output_eq {v : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width 3 F) :
    CanonicalRawController.output v (rawClauses F) =
      Encoding.encodeCNF (FormulaBridge.formula F) := by
  rw [CanonicalRawController.output, accumulator_eq, List.reverse_reverse,
    List.append_assoc, entries_terminated]
  exact CanonicalEnumeration.encoded_eq F hw

end QecReliability.ExternalSATBridge.CanonicalBytes
