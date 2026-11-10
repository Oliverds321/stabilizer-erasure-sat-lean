import ExternalSATRawClauseMatcher
import ExternalSATCandidateClauseEmitter
import ExternalSATCanonicalEnumeration

/-! Semantic endpoint for the ACTUAL clause matcher. Real unary field comparisons
and presence flags agree with finite-set equality, including empty and repeated
clauses/literals. No new runtime operation is introduced here. -/
namespace QecReliability.ExternalSATBridge.ClauseMatchSemantics

open OAI.Algorithms.SubexponentialSAT
open CandidateClauseEmitter (slots)

@[simp] theorem encodeNat_eq_iff (n m : ℕ) :
    Encoding.encodeNat n = Encoding.encodeNat m ↔ n = m := Encoding.encodeNat_injective.eq_iff

theorem slot_occurs (codes : List ℕ) (hc : codes.length ≤ 3) (n : ℕ) :
    (∃ i : Fin 3, Encoding.encodeNat n = slots codes i) ↔ n ∈ codes := by
  cases codes with
  | nil => simp [slots, Fin.exists_fin_succ, CandidateClauseEmitter.encodeNat_ne_nil]
  | cons a cs =>
    cases cs with
    | nil => simp [slots, Fin.exists_fin_succ, CandidateClauseEmitter.encodeNat_ne_nil]
    | cons b cs =>
      cases cs with
      | nil => simp [slots, Fin.exists_fin_succ, CandidateClauseEmitter.encodeNat_ne_nil]
      | cons c cs =>
        cases cs with
        | nil => simp [slots, Fin.exists_fin_succ, CandidateClauseEmitter.encodeNat_ne_nil]
        | cons d ds => simp only [List.length_cons] at hc; omega

theorem slot_value (codes : List ℕ) (hc : codes.length ≤ 3) (i : Fin 3)
    (hne : slots codes i ≠ []) :
    ∃ n, n ∈ codes ∧ Encoding.encodeNat n = slots codes i := by
  cases codes with
  | nil => fin_cases i <;> simp [slots] at hne
  | cons a cs =>
    cases cs with
    | nil => fin_cases i <;> simp_all [slots]
    | cons b cs =>
      cases cs with
      | nil => fin_cases i <;> simp_all [slots]
      | cons c cs =>
        cases cs with
        | nil => fin_cases i <;> simp_all [slots]
        | cons d ds => simp only [List.length_cons] at hc; omega

theorem presence_check (word : List Bool) (bit : Bool) :
    (word.isEmpty || bit) = true ↔ (word ≠ [] → bit = true) := by
  cases word <;> simp

theorem bool_not_true (b : Bool) : (!b) = true ↔ b = false := by
  cases b <;> decide

theorem bool_not_false (b : Bool) : (!b) = false ↔ b = true := by
  cases b <;> decide

theorem bool_ne_false (b : Bool) : (b ≠ false) ↔ b = true := by
  cases b <;> decide

theorem no_foreign (candidate : Fin 3 → List Bool) (raw : List ℕ) :
    (!(raw.any (fun n => !(decide (Encoding.encodeNat n = candidate 0) ||
      decide (Encoding.encodeNat n = candidate 1) || decide (Encoding.encodeNat n = candidate 2))))) = true ↔
    ∀ n ∈ raw, ∃ i : Fin 3, Encoding.encodeNat n = candidate i := by
  simp only [bool_not_true, List.any_eq_false, bool_ne_false,
    Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h n hn
    rcases h n hn with (h0 | h1) | h2
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
  · intro h n hn
    obtain ⟨i, hi⟩ := h n hn
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi

theorem result_true_iff (candidate : Fin 3 → List Bool) (raw : List ℕ) :
    RawClauseMatcher.clauseResult candidate raw = true ↔
      (∀ n ∈ raw, ∃ i : Fin 3, Encoding.encodeNat n = candidate i) ∧
      (∀ i : Fin 3, candidate i ≠ [] → ∃ n ∈ raw, Encoding.encodeNat n = candidate i) := by
  rw [RawClauseMatcher.clauseResult_eq]
  simp only [Bool.and_eq_true, presence_check, no_foreign,
    List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hf, h0⟩, h1⟩, h2⟩
    refine ⟨hf, ?_⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rintro ⟨hf, hs⟩
    exact ⟨⟨⟨hf, hs 0⟩, hs 1⟩, hs 2⟩

/-- Both directions of set equality are checked by physical flags. Candidate
slots may contain duplicates here; sortedness is needed only for canonical order. -/
theorem result_eq_set (codes raw : List ℕ) (hc : codes.length ≤ 3) :
    RawClauseMatcher.clauseResult (slots codes) raw = true ↔ raw.toFinset = codes.toFinset := by
  rw [result_true_iff]
  constructor
  · rintro ⟨hforeign, hseen⟩
    apply Finset.ext
    intro n
    simp only [List.mem_toFinset]
    constructor
    · intro hn
      exact (slot_occurs codes hc n).mp (hforeign n hn)
    · intro hn
      obtain ⟨i, hi⟩ := (slot_occurs codes hc n).mpr hn
      have hne : slots codes i ≠ [] := by
        rw [← hi]
        exact CandidateClauseEmitter.encodeNat_ne_nil n
      obtain ⟨m, hm, he⟩ := hseen i hne
      have heq : m = n := Encoding.encodeNat_injective (he.trans hi.symm)
      simpa only [heq] using hm
  · intro heq
    have hm (n : ℕ) : n ∈ raw ↔ n ∈ codes := by
      simpa only [List.mem_toFinset] using Finset.ext_iff.mp heq n
    constructor
    · intro n hn
      exact (slot_occurs codes hc n).mpr ((hm n).mp hn)
    · intro i hi
      obtain ⟨n, hn, he⟩ := slot_value codes hc i hi
      exact ⟨n, (hm n).mpr hn, he⟩

def literalCodes {v : ℕ} (cl : List (PrefixCNF.Literal v)) : List ℕ :=
  cl.map (fun l => Encoding.literalCode (FormulaBridge.literal l))

theorem literalCodes_set {v : ℕ} (cl : List (PrefixCNF.Literal v)) :
    (literalCodes cl).toFinset = (FormulaBridge.clause cl).image Encoding.literalCode := by
  apply Finset.ext
  intro n
  constructor
  · intro hn
    obtain ⟨l, hl, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
    exact Finset.mem_image.mpr ⟨FormulaBridge.literal l,
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, rfl⟩), he⟩
  · intro hn
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hn
    obtain ⟨native, hn, hnl⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨native, hn,
      (congrArg Encoding.literalCode hnl).trans he⟩)

/-- The actual matcher's Boolean is exactly the selector predicate used by the
accepted canonical byte-equivalence theorem, not merely a similar specification. -/
theorem actual_matches {v : ℕ} (codes : List ℕ) (hc : codes.length ≤ 3)
    (cl : List (PrefixCNF.Literal v)) :
    RawClauseMatcher.clauseResult (slots codes) (literalCodes cl) =
      CanonicalEnumeration.clauseMatches codes cl := by
  apply Bool.eq_iff_iff.mpr
  rw [result_eq_set codes (literalCodes cl) hc, CanonicalEnumeration.clauseMatches,
    decide_eq_true_eq, literalCodes_set]
  exact eq_comm

theorem actual_matches_canonical {v : ℕ} (codes : List ℕ) (hc : codes.length ≤ 3)
    (hs : codes.Pairwise (· < ·)) (cl : List (PrefixCNF.Literal v)) :
    RawClauseMatcher.clauseResult (slots codes) (literalCodes cl) = true ↔
      codes = Encoding.clauseNumbers (FormulaBridge.clause cl) := by
  rw [actual_matches codes hc cl]
  exact CanonicalEnumeration.clauseMatches_iff codes cl hs

end QecReliability.ExternalSATBridge.ClauseMatchSemantics
