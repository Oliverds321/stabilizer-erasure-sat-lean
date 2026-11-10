import ExternalSATFormulaBridge
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

/-! Dimension-aware canonical enumeration, not yet a measured stack program.
Depth is the fixed clause-width bound. Traversal is lexicographic prefix order;
it includes the empty candidate and does not remove tautological clauses. -/
namespace QecReliability.ExternalSATBridge.CanonicalEnumeration

open OAI.Algorithms.SubexponentialSAT

def candidates : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | k + 1, lo, upper => [] ::
      ((List.range upper).filter (fun a => decide (lo ≤ a))).flatMap
        (fun a => (candidates k (a + 1) upper).map (List.cons a))

theorem mem_cons_candidates (k lo upper a : ℕ) (as : List ℕ) :
    a :: as ∈ candidates (k + 1) lo upper ↔
      lo ≤ a ∧ a < upper ∧ as ∈ candidates k (a + 1) upper := by
  simp [candidates, and_assoc, and_left_comm, and_comm]

/-- The executable trie visits precisely the increasing bounded candidates. -/
theorem mem_candidates (k lo upper : ℕ) (c : List ℕ) :
    c ∈ candidates k lo upper ↔ c.length ≤ k ∧ c.Pairwise (· < ·) ∧
      ∀ a ∈ c, lo ≤ a ∧ a < upper := by
  induction k generalizing lo c with
  | zero =>
    cases c <;> simp [candidates]
  | succ k ih =>
    cases c with
    | nil => simp [candidates]
    | cons a as =>
      rw [mem_cons_candidates, ih]
      constructor
      · rintro ⟨hlo, hu, hlen, hp, hb⟩
        refine ⟨by simpa using Nat.succ_le_succ hlen,
          List.pairwise_cons.mpr ⟨?_, hp⟩, ?_⟩
        · intro b hm
          have := (hb b hm).1
          omega
        · intro b hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact ⟨hlo, hu⟩
          · have := hb b hm
            exact ⟨by omega, this.2⟩
      · rintro ⟨hlen, hp, hb⟩
        obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
        have ha := hb a (by simp)
        refine ⟨ha.1, ha.2, by simpa using hlen, htail, ?_⟩
        intro b hm
        have hgreater := hhead b hm
        have hbound := hb b (by simp [hm])
        exact ⟨by omega, hbound.2⟩

theorem candidates_sorted (k lo upper : ℕ) :
    (candidates k lo upper).Pairwise (· < ·) := by
  induction k generalizing lo with
  | zero => simp [candidates]
  | succ k ih =>
    rw [candidates, List.pairwise_cons]
    constructor
    · intro c hc
      obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨as, has, rfl⟩ := List.mem_map.mp hc
      exact List.Lex.nil
    · apply List.pairwise_flatMap.mpr
      constructor
      · intro a ha
        exact (ih (a + 1)).map (List.cons a) (fun _ _ h => List.Lex.cons h)
      · apply (List.pairwise_lt_range.filter (fun a => decide (lo ≤ a))).imp
        intro a b hab x hx y hy
        obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hy
        exact List.Lex.rel hab

theorem flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (bound : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ bound) :
    (l.flatMap f).length ≤ l.length * bound := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    calc
      (f a).length + (as.flatMap f).length ≤ bound + as.length * bound := Nat.add_le_add ha ht
      _ = (as.length + 1) * bound := by ring

/-- A polynomial number of candidates at fixed width; no exponential-in-v
truth assignment enumeration is hidden in this construction. -/
theorem candidates_length (k lo upper : ℕ) :
    (candidates k lo upper).length ≤ (upper + 1) ^ k := by
  induction k generalizing lo with
  | zero => simp [candidates]
  | succ k ih =>
    have h := flatMap_length_le
      ((List.range upper).filter (fun a => decide (lo ≤ a)))
      (fun a => (candidates k (a + 1) upper).map (List.cons a)) ((upper + 1) ^ k)
      (by intro a ha; simpa using ih (a + 1))
    have hcount : ((List.range upper).filter (fun a => decide (lo ≤ a))).length ≤ upper := by
      simpa using List.length_filter_le (fun a => decide (lo ≤ a)) (List.range upper)
    have hpow : 1 ≤ (upper + 1) ^ k := Nat.succ_le_of_lt (by positivity)
    simp only [candidates, List.length_cons]
    calc
      _ ≤ upper * (upper + 1) ^ k + 1 := by
        exact Nat.add_le_add_right (h.trans (Nat.mul_le_mul_right _ hcount)) 1
      _ ≤ (upper + 1) ^ (k + 1) := by rw [pow_succ]; nlinarith

/-- Occurrence filtering after canonical candidate generation. The predicate
uses actual external clause representations; measured matching is still pending. -/
def normalized {v : ℕ} (F : PrefixCNF.Formula v) : List (List ℕ) :=
  (candidates 3 0 (2 * v)).filter
    (fun c => decide (c ∈ (FormulaBridge.formula F).image Encoding.clauseNumbers))

theorem normalized_eq {v : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width 3 F) :
    normalized F = Encoding.cnfNumbers (FormulaBridge.formula F) := by
  apply List.SortedLT.eq_of_mem_iff
    ((candidates_sorted 3 0 (2 * v)).filter _).sortedLT
    (Finset.sortedLT_sort _)
  intro c
  simp only [normalized, List.mem_filter, decide_eq_true_eq, Encoding.cnfNumbers,
    Finset.mem_sort]
  constructor
  · exact fun h => h.2
  · intro hc
    refine ⟨(mem_candidates 3 0 (2 * v) c).mpr ?_, hc⟩
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨?_, (Finset.sortedLT_sort _).pairwise, ?_⟩
    · rw [Encoding.length_clauseNumbers]
      exact FormulaBridge.formula_width F hw C hC
    · intro a ha
      exact ⟨Nat.zero_le _, Encoding.mem_clauseNumbers_lt ha⟩

theorem normalized_length {v : ℕ} (F : PrefixCNF.Formula v) :
    (normalized F).length ≤ (2 * v + 1) ^ 3 := by
  exact (List.length_filter_le _ _).trans (candidates_length 3 0 (2 * v))

/-- Sorting-free clause matcher. Set construction deduplicates at most three
native literals; no canonical sorting function occurs in this predicate. -/
def clauseMatches {v : ℕ} (c : List ℕ) (cl : List (PrefixCNF.Literal v)) : Bool :=
  decide (c.toFinset = (FormulaBridge.clause cl).image Encoding.literalCode)

theorem clauseMatches_iff {v : ℕ} (c : List ℕ) (cl : List (PrefixCNF.Literal v))
    (hs : c.Pairwise (· < ·)) :
    clauseMatches c cl = true ↔ c = Encoding.clauseNumbers (FormulaBridge.clause cl) := by
  rw [clauseMatches, decide_eq_true_eq]
  constructor
  · intro h
    apply List.SortedLT.eq_of_mem_iff hs.sortedLT (Finset.sortedLT_sort _)
    intro a
    simpa [Encoding.clauseNumbers] using Finset.ext_iff.mp h a
  · rintro rfl
    simp [Encoding.clauseNumbers]

/-- The executable candidate selector uses only finite-set equality against
original clauses. Traversal need not retain the entire candidate list when it
is later lowered to a streaming controller. -/
def selected {v : ℕ} (F : PrefixCNF.Formula v) : List (List ℕ) :=
  (candidates 3 0 (2 * v)).filter (fun c => F.any (clauseMatches c))

theorem selected_eq_normalized {v : ℕ} (F : PrefixCNF.Formula v) :
    selected F = normalized F := by
  apply List.SortedLT.eq_of_mem_iff
    ((candidates_sorted 3 0 (2 * v)).filter _).sortedLT
    ((candidates_sorted 3 0 (2 * v)).filter _).sortedLT
  intro c
  simp only [selected, normalized, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hm⟩
    obtain ⟨cl, hcl, hmatch⟩ := List.any_eq_true.mp hm
    have he := (clauseMatches_iff c cl ((mem_candidates 3 0 (2 * v) c).mp hc).2.1).mp hmatch
    refine ⟨hc, Finset.mem_image.mpr ⟨FormulaBridge.clause cl, ?_, he.symm⟩⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨cl, hcl, rfl⟩)
  · rintro ⟨hc, hm⟩
    obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hm
    obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hC)
    refine ⟨hc, List.any_eq_true.mpr ⟨cl, hcl, ?_⟩⟩
    exact (clauseMatches_iff c cl ((mem_candidates 3 0 (2 * v) c).mp hc).2.1).mpr he.symm

theorem selected_eq {v : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width 3 F) :
    selected F = Encoding.cnfNumbers (FormulaBridge.formula F) :=
  (selected_eq_normalized F).trans (normalized_eq F hw)

theorem selected_length {v : ℕ} (F : PrefixCNF.Formula v) :
    (selected F).length ≤ (2 * v + 1) ^ 3 := by
  rw [selected_eq_normalized]
  exact normalized_length F

def encoded {v : ℕ} (F : PrefixCNF.Formula v) : List Bool :=
  Encoding.encodeNat v ++ Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (selected F)

/-- Literal byte identity with the genuine external encoding, not merely
satisfiability equivalence. Establishes the target for measured lowering. -/
theorem encoded_eq {v : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width 3 F) :
    encoded F = Encoding.encodeCNF (FormulaBridge.formula F) := by
  simp only [encoded, selected_eq F hw, Encoding.encodeCNF, Encoding.encodeCNFBody]

end QecReliability.ExternalSATBridge.CanonicalEnumeration
