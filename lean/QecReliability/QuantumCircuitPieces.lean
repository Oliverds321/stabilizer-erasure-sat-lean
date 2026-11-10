import QecReliability.SparseCircuits

/-! Actual binary symplectic pairing and erasure support are connected to concrete
circuits/CNFs. Sparse row-space assembly and population counting remain separate. -/

namespace QecReliability.SharedCircuit
open PrefixCNF
open scoped BigOperators

def wiredPauli {n v : ℕ} (a : BitModels v) (x z : Fin n → Fin v) : Binary.Pauli n :=
  (fun i => boolBit (a (x i)), fun i => boolBit (a (z i)))

def pairingPairs {n v : ℕ} (x z x' z' : Fin n → Fin v) : List (Fin v × Fin v) :=
  List.ofFn (fun i => (x i, z' i)) ++ List.ofFn (fun i => (z i, x' i))

theorem pairingPairs_length {n v : ℕ} (x z x' z' : Fin n → Fin v) :
    (pairingPairs x z x' z').length = 2 * n := by simp [pairingPairs, Nat.two_mul]

/-- The parity-of-products output is exactly the binary symplectic pairing. -/
theorem pairingCircuit_correct {n v : ℕ} (a : BitModels v) (x z x' z' : Fin n → Fin v) :
    boolBit ((productParityCircuit (pairingPairs x z x' z')).run a
      (Fin.last (v + 2 * (pairingPairs x z x' z').length))) =
      Binary.symplectic n (wiredPauli a x z) (wiredPauli a x' z') := by
  rw [productParityCircuit_correct, productParityValue_sum, Binary.symplectic_apply]
  simp [pairingPairs, List.map_ofFn, List.sum_ofFn, wiredPauli, Finset.sum_add_distrib]

theorem pairing_cnf_exists {n v : ℕ} (a : BitModels v) (x z x' z' : Fin n → Fin v) :
    (∃ u, PrefixCNF.eval
      ((productParityCircuit (pairingPairs x z x' z')).asserted
        (Fin.last (v + 2 * (pairingPairs x z x' z').length))) (Fin.append a u) = true) ↔
      Binary.symplectic n (wiredPauli a x z) (wiredPauli a x' z') = 1 := by
  rw [Circuit.asserted_exists, ← pairingCircuit_correct, boolBit_eq_one]

theorem pairing_cnf_clause_bound {n v : ℕ} (x z x' z' : Fin n → Fin v) :
    ((productParityCircuit (pairingPairs x z x' z')).asserted
      (Fin.last (v + 2 * (pairingPairs x z x' z').length))).length ≤ 16 * n + 5 := by
  have h := Circuit.asserted_length (productParityCircuit (pairingPairs x z x' z'))
    (Fin.last (v + 2 * (pairingPairs x z x' z').length))
  have hlen := pairingPairs_length x z x' z'
  omega

def supportPairs {n v : ℕ} (x z e : Fin n → Fin v) : List (Fin v × Fin v) :=
  List.ofFn (fun i => (x i, e i)) ++ List.ofFn (fun i => (z i, e i))

def wiredErasures {n v : ℕ} (a : BitModels v) (e : Fin n → Fin v) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a (e i) = true)

theorem support_cnf_condition {n v : ℕ} (a : BitModels v) (x z e : Fin n → Fin v) :
    PrefixCNF.eval (supportClauses (supportPairs x z e)) a = true ↔
      ∀ i, (a (x i) = true → a (e i) = true) ∧ (a (z i) = true → a (e i) = true) := by
  rw [supportClauses_correct]
  constructor
  · intro h i
    constructor
    · exact h (x i, e i) (List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    · exact h (z i, e i) (List.mem_append.mpr (Or.inr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  · intro h xe hxe hx
    rcases List.mem_append.mp hxe with hxe | hxe
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxe
      exact (h i).1 hx
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxe
      exact (h i).2 hx

/-- Both Pauli coordinates vanish off the flagged erasure set, with exactly two clauses per qubit. -/
theorem support_cnf_correct {n v : ℕ} (a : BitModels v) (x z e : Fin n → Fin v) :
    PrefixCNF.eval (supportClauses (supportPairs x z e)) a = true ↔
      wiredPauli a x z ∈ Binary.supported (wiredErasures a e) := by
  rw [support_cnf_condition, Binary.mem_supported]
  simp only [wiredErasures, Finset.mem_filter, Finset.mem_univ, true_and, wiredPauli, boolBit_eq_zero]
  apply forall_congr'
  intro i
  cases a (e i) <;> cases a (x i) <;> cases a (z i) <;> simp

theorem support_cnf_length {n v : ℕ} (x z e : Fin n → Fin v) :
    (supportClauses (supportPairs x z e)).length = 2 * n := by
  simp [supportClauses_length, supportPairs, Nat.two_mul]

def rowFormula {v : ℕ} (row : List (Fin v)) : Formula (v + (row.length + 1)) :=
  (parityCircuit row).constrained (Fin.last (v + row.length)) false

/-- A supplied sparse incidence row becomes an exact F₂ parity-zero constraint. -/
theorem rowFormula_correct {v : ℕ} (row : List (Fin v)) (a : BitModels v) :
    (∃ u, PrefixCNF.eval (rowFormula row) (Fin.append a u) = true) ↔
      (row.map (fun i => boolBit (a i))).sum = 0 := by
  rw [rowFormula, Circuit.constrained_exists, parity_zero_iff]

theorem rowFormula_width {v : ℕ} (row : List (Fin v)) : Width 3 (rowFormula row) :=
  Circuit.constrained_width _ _ _

theorem rowFormula_length {v : ℕ} (row : List (Fin v)) :
    (rowFormula row).length ≤ 4 * row.length + 5 := by
  have h := Circuit.constrained_length (parityCircuit row) (Fin.last (v + row.length)) false
  unfold rowFormula
  omega

/-- Aggregate clause budget of the row blocks after discarding empty rows; not a disjoint-auxiliary assembly theorem. -/
theorem sparse_row_clause_budget {v : ℕ} (rows : List (List (Fin v))) :
    ((nonemptyRows rows).map (fun row => (rowFormula row).length)).sum ≤ 9 * incidences rows := by
  induction rows with
  | nil => simp [nonemptyRows, incidences]
  | cons row rows ih =>
    cases row with
    | nil => simpa [nonemptyRows, incidences] using ih
    | cons x xs =>
      have h := rowFormula_length (x :: xs)
      simp only [nonemptyRows, List.filter_cons, List.isEmpty_cons, Bool.not_false, ↓reduceIte,
        List.map_cons, List.sum_cons, List.length_cons, incidences] at *
      omega

end QecReliability.SharedCircuit
