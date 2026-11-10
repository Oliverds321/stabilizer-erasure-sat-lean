import QecReliability.CNFBlocks

/-! Sparse Pauli rows, their actual linear span, and an assembled normalizer CNF. -/

namespace QecReliability.SharedCircuit
open PrefixCNF

abbrev PauliCoord (n : ℕ) := Sum (Fin n) (Fin n)

def coordPauli {n : ℕ} : PauliCoord n → Binary.Pauli n :=
  Sum.elim Binary.xUnit Binary.zUnit

def decodeRow {n : ℕ} (row : List (PauliCoord n)) : Binary.Pauli n :=
  (row.map coordPauli).sum

def rowSpace {n : ℕ} (rows : List (List (PauliCoord n))) : Submodule Binary.Bit (Binary.Pauli n) :=
  Submodule.span Binary.Bit {x | x ∈ rows.map decodeRow}

def rowIncidences {n : ℕ} (rows : List (List (PauliCoord n))) : ℕ :=
  (rows.map List.length).sum

def rowWires {n v : ℕ} (x z : Fin n → Fin v) (row : List (PauliCoord n)) : List (Fin v) :=
  row.map (Sum.elim z x)

theorem rowWires_length {n v : ℕ} (x z : Fin n → Fin v) (row : List (PauliCoord n)) :
    (rowWires x z row).length = row.length := by simp [rowWires]

theorem rowWires_incidences {n v : ℕ} (x z : Fin n → Fin v)
    (rows : List (List (PauliCoord n))) :
    incidences (rows.map (rowWires x z)) = rowIncidences rows := by
  simp [incidences, rowIncidences, List.map_map, Function.comp_def, rowWires_length]

theorem row_pairing {n v : ℕ} (a : BitModels v) (x z : Fin n → Fin v)
    (row : List (PauliCoord n)) :
    ((rowWires x z row).map (fun i => boolBit (a i))).sum =
      Binary.symplectic n (decodeRow row) (wiredPauli a x z) := by
  induction row with
  | nil => simp [rowWires, decodeRow]
  | cons c row ih =>
    simp only [rowWires, List.map_cons, List.sum_cons, decodeRow, map_add, LinearMap.add_apply] at *
    rw [← ih]
    congr 1
    cases c with
    | inl i =>
      change boolBit (a (z i)) = Binary.symplectic n (Binary.xUnit i) (wiredPauli a x z)
      rw [(Binary.symplectic_symm n).eq]
      simp [wiredPauli]
    | inr i =>
      change boolBit (a (x i)) = Binary.symplectic n (Binary.zUnit i) (wiredPauli a x z)
      rw [(Binary.symplectic_symm n).eq]
      simp [wiredPauli]

theorem mem_normalizer_rows {n : ℕ} (rows : List (List (PauliCoord n)))
    (z : Binary.Pauli n) :
    z ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ↔
      ∀ row ∈ rows, Binary.symplectic n (decodeRow row) z = 0 := by
  constructor
  · intro h row hr
    exact h _ (Submodule.subset_span (List.mem_map.mpr ⟨row, hr, rfl⟩))
  · intro h s hs
    change Binary.symplectic n s z = 0
    refine Submodule.span_induction (fun y hy => ?_) ?_
      (fun y y' _ _ hy hy' => ?_) (fun c y _ hy => ?_) hs
    · obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hy
      exact h row hr
    · simp
    · simp [map_add, LinearMap.add_apply, hy, hy']
    · simp [map_smul, hy]

def rowBlock {v : ℕ} (row : List (Fin v)) : Block v :=
  Block.constrained (parityCircuit row) (Fin.last (v + row.length)) false

def normalizerBlock {n v : ℕ} (rows : List (List (PauliCoord n)))
    (x z : Fin n → Fin v) : Block v :=
  Block.merge ((nonemptyRows (rows.map (rowWires x z))).map rowBlock)

theorem normalizerBlock_correct {n v : ℕ} (rows : List (List (PauliCoord n)))
    (x z : Fin n → Fin v) (a : BitModels v) :
    (normalizerBlock rows x z).Accepts a ↔
      wiredPauli a x z ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) := by
  rw [normalizerBlock, Block.merge_accepts, mem_normalizer_rows]
  simp only [List.forall_mem_map]
  have he : ∀ row : List (Fin v), (rowBlock row).Accepts a ↔ parityValue a row = false := by
    intro row
    exact (Circuit.constrained_exists (parityCircuit row) _ false a).trans
      (by rw [parityCircuit_correct])
  simp_rw [he]
  rw [nonemptyRows_constraints]
  simp only [List.forall_mem_map]
  apply forall_congr'
  intro row
  apply imp_congr_right
  intro _
  rw [← row_pairing a x z row, ← parityValue_sum, boolBit_eq_zero]

theorem normalizerBlock_deterministic {n v : ℕ} (rows : List (List (PauliCoord n)))
    (x z : Fin n → Fin v) : (normalizerBlock rows x z).Deterministic := by
  apply Block.merge_deterministic
  intro B hB
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hB
  exact Block.constrained_deterministic _ _ _

theorem normalizerBlock_width {n v : ℕ} (rows : List (List (PauliCoord n)))
    (x z : Fin n → Fin v) : Width 3 (normalizerBlock rows x z).formula := by
  apply Block.merge_width
  intro B hB
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hB
  exact Circuit.constrained_width _ _ _

theorem normalizerBlock_aux {n v : ℕ} (rows : List (List (PauliCoord n)))
    (x z : Fin n → Fin v) : (normalizerBlock rows x z).aux ≤ 2 * rowIncidences rows := by
  unfold normalizerBlock
  rw [Block.merge_aux, List.map_map]
  change ((nonemptyRows (rows.map (rowWires x z))).map (fun row => row.length + 1)).sum ≤ _
  simpa [rowWires_incidences] using parity_blocks_gate_bound (rows.map (rowWires x z))

theorem normalizerBlock_length {n v : ℕ} (rows : List (List (PauliCoord n)))
    (x z : Fin n → Fin v) : (normalizerBlock rows x z).formula.length ≤ 9 * rowIncidences rows := by
  unfold normalizerBlock
  rw [Block.merge_length, List.map_map]
  change ((nonemptyRows (rows.map (rowWires x z))).map (fun row => (rowFormula row).length)).sum ≤ _
  simpa [rowWires_incidences] using sparse_row_clause_budget (rows.map (rowWires x z))

end QecReliability.SharedCircuit
