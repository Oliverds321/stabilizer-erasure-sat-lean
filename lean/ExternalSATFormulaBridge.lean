import QecReliability.PrefixCNF
import OAI.Algorithms.SubexponentialSAT.Encoding

/-! Actual native-to-external SAT syntax correspondence on the common toolchain.
Finite-set deduplication preserves decision SAT, including empty clauses/formulas.
No counting equivalence, measured preprocessing, or engine existence is claimed. -/
namespace QecReliability.ExternalSATBridge.FormulaBridge

open OAI.Algorithms.SubexponentialSAT

def literal {v : ℕ} (l : PrefixCNF.Literal v) : SAT.Literal (Fin v) :=
  ⟨l.1, l.2⟩

def clause {v : ℕ} (c : List (PrefixCNF.Literal v)) : SAT.Clause (Fin v) :=
  (c.map literal).toFinset

def formula {v : ℕ} (F : PrefixCNF.Formula v) : SAT.CNF (Fin v) :=
  (F.map clause).toFinset

@[simp] theorem literal_eval {v : ℕ} (l : PrefixCNF.Literal v) (a : Fin v → Bool) :
    (literal l).eval a = (a l.1 == l.2) := rfl

@[simp] theorem clause_eval {v : ℕ} (c : List (PrefixCNF.Literal v)) (a : Fin v → Bool) :
    (clause c).eval a = PrefixCNF.evalClause c a := by
  apply Bool.eq_iff_iff.mpr
  rw [SAT.Clause.eval_eq_true]
  constructor
  · rintro ⟨l, hl, he⟩
    obtain ⟨native, hnative, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hl)
    rw [← heq] at he
    exact List.any_eq_true.mpr ⟨native, hnative, he⟩
  · intro h
    obtain ⟨l, hl, he⟩ := List.any_eq_true.mp h
    exact ⟨literal l, List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, rfl⟩), he⟩

@[simp] theorem formula_eval {v : ℕ} (F : PrefixCNF.Formula v) (a : Fin v → Bool) :
    (formula F).eval a = PrefixCNF.eval F a := by
  apply Bool.eq_iff_iff.mpr
  rw [SAT.CNF.eval_eq_true]
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro c hc
    have he := h (clause c) (List.mem_toFinset.mpr (List.mem_map.mpr ⟨c, hc, rfl⟩))
    rwa [clause_eval] at he
  · intro h C hC
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hC)
    rw [clause_eval]
    exact List.all_eq_true.mp h c hc

theorem satisfiable_iff {v : ℕ} (F : PrefixCNF.Formula v) :
    SAT.Satisfiable (formula F) ↔ ∃ a, PrefixCNF.eval F a = true := by
  simp [SAT.Satisfiable]

theorem clause_card_le {v : ℕ} (c : List (PrefixCNF.Literal v)) :
    (clause c).card ≤ c.length := by
  simpa [clause] using List.toFinset_card_le (c.map literal)

theorem formula_card_le {v : ℕ} (F : PrefixCNF.Formula v) :
    (formula F).card ≤ F.length := by
  simpa [formula] using List.toFinset_card_le (F.map clause)

theorem formula_width {v k : ℕ} (F : PrefixCNF.Formula v) (hw : PrefixCNF.Width k F) :
    ∀ C ∈ formula F, C.card ≤ k := by
  intro C hC
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hC)
  exact (clause_card_le c).trans (hw c hc)

@[simp] theorem literal_code {v : ℕ} (l : PrefixCNF.Literal v) :
    Encoding.literalCode (literal l) = 2 * l.1.val + if l.2 then 1 else 0 := rfl

/-- Canonical clause candidates have bounded width and range. The canonical
ordering itself remains the actual external Encoding definition. -/
theorem canonical_clause_bounds {v k : ℕ} (F : PrefixCNF.Formula v)
    (hw : PrefixCNF.Width k F) (c : List ℕ)
    (hc : c ∈ Encoding.cnfNumbers (formula F)) :
    c.length ≤ k ∧ ∀ a ∈ c, a < 2 * v := by
  have hc' : c ∈ (formula F).image Encoding.clauseNumbers := by
    simpa [Encoding.cnfNumbers] using hc
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hc'
  constructor
  · rw [Encoding.length_clauseNumbers]
    exact formula_width F hw C hC
  · intro a ha
    exact Encoding.mem_clauseNumbers_lt ha

@[simp] theorem empty_formula {v : ℕ} : formula ([] : PrefixCNF.Formula v) = ∅ := by
  simp [formula]

@[simp] theorem empty_clause {v : ℕ} : clause ([] : List (PrefixCNF.Literal v)) = ∅ := by
  simp [clause]

end QecReliability.ExternalSATBridge.FormulaBridge
