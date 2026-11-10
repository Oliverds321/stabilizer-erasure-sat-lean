import SatCosetWeight

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step B: from a GF(2) system with explicit kernel generators to a CSS code

Generic part. Data: a finite coordinate type `G`, equations `eqs r : List G` with right-hand
sides `rhs r`, and a list `gens` of explicit generators of the homogeneous solutions. Qubits are
`Option G × Fin (m + 1)` (identified with `Fin n` by an equivalence `e`): every coordinate of the
augmented system `[H | s]` (the extra coordinate is `none`) is repeated `m + 1` times.

* X rows: each kernel generator on copy `0`; the "star" pairs `X_(g,0) X_(g,k)`.
* Z rows: each augmented equation `[H_r | s_r]`, on all copies.

Results (`G1`, `G2`):
* every solution `x` of `H x = s` gives a logical operator `logicalOf e x ∈ N \ S` of weight
  `wt x + 1`;
* every `P ∈ N \ S` has weight `≥ m + 1`, or there is a solution `x` with `wt x + 1 ≤ wt P`.

Then the instance attached to a CNF (`reduce`), its correctness theorems, and size bounds.
-/

namespace QecReliability.SatReduction

open scoped BigOperators
open Finset
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecPhysical.Stabilizer.EnumeratorExample (pauliWeight rowSpace_isotropic_of)
open QecPhysical.Stabilizer.Uncorrectable

attribute [local instance 2000] instBEqOfDecidableEq

/-! ## Counting lemmas -/

theorem sum_ite_eq_count {α : Type} [DecidableEq α] (a : α) (B : List α) :
    (B.map (fun b => if a = b then 1 else 0)).sum = B.count a := by
  induction B with
  | nil => simp
  | cons b B ihB =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, beq_iff_eq, ihB]
    by_cases h : a = b
    · subst h; simp; omega
    · simp [h, Ne.symm h]

theorem count_sum_swap {α : Type} [DecidableEq α] (A B : List α) :
    (A.map (fun a => B.count a)).sum = (B.map (fun b => A.count b)).sum := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, beq_iff_eq]
    rw [ih, List.sum_map_add, sum_ite_eq_count]
    omega

theorem sum_map_zero {α : Type} (l : List α) : (l.map (fun _ => (0 : Bit))).sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem cast_list_sum {α : Type} (l : List α) (f : α → ℕ) :
    ((l.map f).sum : Bit) = (l.map (fun a => (f a : Bit))).sum := by
  rw [Nat.cast_list_sum, List.map_map]
  rfl

section Generic

variable {G R : Type} [Fintype G] [DecidableEq G]
variable {m n : ℕ} (e : Option G × Fin (m + 1) ≃ Fin n)

/-- A row with an `X` on each listed qubit. -/
def xRowQ (l : List (Option G × Fin (m + 1))) : List (PauliCoord n) :=
  l.map (fun q => Sum.inl (e q))

/-- A row with a `Z` on each listed qubit. -/
def zRowQ (l : List (Option G × Fin (m + 1))) : List (PauliCoord n) :=
  l.map (fun q => Sum.inr (e q))

theorem pair_xRowQ (l : List (Option G × Fin (m + 1))) (z : Pauli n) :
    symplectic n (decodeRow (xRowQ e l)) z = (l.map (fun q => z.2 (e q))).sum := by
  induction l with
  | nil => simp [xRowQ, decodeRow]
  | cons q l ih =>
    simp only [xRowQ, decodeRow, List.map_cons, List.sum_cons, map_add, LinearMap.add_apply]
      at ih ⊢
    rw [ih]
    congr 1
    simp [coordPauli, symplectic_apply, xUnit, Pi.single_apply]

theorem pair_zRowQ (l : List (Option G × Fin (m + 1))) (z : Pauli n) :
    symplectic n (decodeRow (zRowQ e l)) z = (l.map (fun q => z.1 (e q))).sum := by
  induction l with
  | nil => simp [zRowQ, decodeRow]
  | cons q l ih =>
    simp only [zRowQ, decodeRow, List.map_cons, List.sum_cons, map_add, LinearMap.add_apply]
      at ih ⊢
    rw [ih]
    congr 1
    simp [coordPauli, symplectic_apply, zUnit, Pi.single_apply]

theorem decodeRow_xRowQ (l : List (Option G × Fin (m + 1))) :
    decodeRow (xRowQ e l) = (fun i => ((l.count (e.symm i) : ℕ) : Bit), 0) := by
  induction l with
  | nil => simp [xRowQ, decodeRow]; rfl
  | cons q l ih =>
    simp only [xRowQ, decodeRow, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    apply Prod.ext
    · funext i
      simp only [Prod.fst_add, Pi.add_apply, List.count_cons, beq_iff_eq, Nat.cast_add]
      by_cases h : e q = i
      · subst h; simp [coordPauli, xUnit, add_comm]
      · have h' : q ≠ e.symm i := fun h'' => h (by rw [h'', Equiv.apply_symm_apply])
        simp [coordPauli, xUnit, Pi.single_apply, Ne.symm h, h']
    · simp [coordPauli, xUnit]

theorem decodeRow_zRowQ (l : List (Option G × Fin (m + 1))) :
    decodeRow (zRowQ e l) = (0, fun i => ((l.count (e.symm i) : ℕ) : Bit)) := by
  induction l with
  | nil => simp [zRowQ, decodeRow]; rfl
  | cons q l ih =>
    simp only [zRowQ, decodeRow, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    apply Prod.ext
    · simp [coordPauli, zUnit]
    · funext i
      simp only [Prod.snd_add, Pi.add_apply, List.count_cons, beq_iff_eq, Nat.cast_add]
      by_cases h : e q = i
      · subst h; simp [coordPauli, zUnit, add_comm]
      · have h' : q ≠ e.symm i := fun h'' => h (by rw [h'', Equiv.apply_symm_apply])
        simp [coordPauli, zUnit, Pi.single_apply, Ne.symm h, h']

/-- Repeat each listed coordinate on all `m + 1` copies. -/
def blowup (l : List (Option G)) : List (Option G × Fin (m + 1)) :=
  l.flatMap (fun g => (List.finRange (m + 1)).map (fun k => (g, k)))

theorem sum_blowup (l : List (Option G)) (f : Option G × Fin (m + 1) → Bit) :
    ((blowup (m := m) l).map f).sum = (l.map (fun g => ∑ k, f (g, k))).sum := by
  induction l with
  | nil => simp [blowup]
  | cons g l ih =>
    simp only [blowup, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih, Fin.sum_univ_def, List.map_map]
    rfl

theorem count_map_fst_pair (g : Option G) (q : Option G × Fin (m + 1)) :
    ((List.finRange (m + 1)).map (fun k => (g, k))).count q = if q.1 = g then 1 else 0 := by
  rcases q with ⟨g', k⟩
  by_cases h : g' = g
  · subst h
    simp only [ite_true]
    rw [List.count_map_of_injective _ _ (fun a b hab => (Prod.mk.inj hab).2)]
    exact List.count_finRange k
  · simp only [h, ite_false]
    apply List.count_eq_zero_of_not_mem
    simp only [List.mem_map, List.mem_finRange, true_and, not_exists]
    intro k' hk'
    exact h (congrArg Prod.fst hk').symm

theorem count_blowup (l : List (Option G)) (g : Option G) (k : Fin (m + 1)) :
    (blowup (m := m) l).count (g, k) = l.count g := by
  induction l with
  | nil => simp [blowup]
  | cons g' l ih =>
    simp only [blowup, List.flatMap_cons, List.count_append, List.count_cons, beq_iff_eq] at ih ⊢
    rw [ih, count_map_fst_pair]
    by_cases h : g' = g
    · subst h; simp; omega
    · simp [h, Ne.symm h]

/-- `∑_k #(g, k) = #g` after projecting to the first component. -/
theorem sum_count_pair (l : List (Option G × Fin (m + 1))) (g : Option G) :
    ∑ k : Fin (m + 1), l.count (g, k) = (l.map Prod.fst).count g := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.count_cons, beq_iff_eq, List.map_cons, Finset.sum_add_distrib, ih]
    congr 1
    rcases q with ⟨g', k'⟩
    by_cases h : g' = g
    · subst h
      simp only [Prod.mk.injEq, true_and, ite_true]
      rw [Finset.sum_ite_eq]
      simp
    · simp [h]

variable (eqs : R → List G) (rhs : R → Bit) (gens : List (List G)) (allR : List R)
  (allG : List G)

/-- The augmented equation `[H_r | s_r]` as a list of coordinates of `Option G`. -/
def zList (r : R) : List (Option G) := (eqs r).map some ++ (if rhs r = 1 then [none] else [])

def genRow (gen : List G) : List (PauliCoord n) := xRowQ e (gen.map (fun g => (some g, 0)))

def starRow (g : Option G) (k : Fin (m + 1)) : List (PauliCoord n) := xRowQ e [(g, 0), (g, k)]

def zRow (r : R) : List (PauliCoord n) := zRowQ e (blowup (zList eqs rhs r))

def allOpt : List (Option G) := none :: allG.map some

/-- **The check rows of the code.** -/
def codeRows : List (List (PauliCoord n)) :=
  gens.map (genRow e) ++ (allOpt allG).flatMap (fun g => (List.finRange (m + 1)).map (starRow e g)) ++
    allR.map (zRow e eqs rhs)

theorem mem_codeRows {row : List (PauliCoord n)} :
    row ∈ codeRows e eqs rhs gens allR allG ↔
      (∃ gen ∈ gens, genRow e gen = row) ∨ (∃ g ∈ allOpt allG, ∃ k, starRow e g k = row) ∨
        (∃ r ∈ allR, zRow e eqs rhs r = row) := by
  simp only [codeRows, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange,
    true_and]
  exact or_assoc

theorem count_zList_some (r : R) (g : G) : (zList eqs rhs r).count (some g) = (eqs r).count g := by
  unfold zList
  rw [List.count_append, List.count_map_of_injective _ _ (Option.some_injective G)]
  split_ifs <;> simp

theorem count_genRow_list (gen : List G) (q : Option G × Fin (m + 1)) :
    (gen.map (fun g => (some g, (0 : Fin (m + 1))))).count q =
      if q.2 = 0 then q.1.elim 0 (fun g => gen.count g) else 0 := by
  rcases q with ⟨g', k⟩
  rcases g' with _ | g
  · simp only [Option.elim]
    split_ifs <;>
    · apply List.count_eq_zero_of_not_mem
      simp
  · by_cases hk : k = 0
    · subst hk
      simp only [ite_true, Option.elim]
      exact List.count_map_of_injective gen (fun g => ((some g : Option G), (0 : Fin (m + 1))))
        (by intro a b hab; simpa using hab) g
    · simp only [hk, ite_false]
      apply List.count_eq_zero_of_not_mem
      simp only [List.mem_map, not_exists, not_and]
      intro a _ ha
      exact hk (congrArg Prod.snd ha).symm

/-- The fold of `v` over the copies of `g`. -/
def fold (v : Fin n → Bit) (g : Option G) : Bit := ∑ k, v (e (g, k))

theorem fold_count (l : List (Option G × Fin (m + 1))) :
    fold e (fun i => ((l.count (e.symm i) : ℕ) : Bit)) =
      fun g => (((l.map Prod.fst).count g : ℕ) : Bit) := by
  funext g
  unfold fold
  simp only [Equiv.symm_apply_apply]
  rw [← Nat.cast_sum, sum_count_pair]

theorem fold_zero : fold e (0 : Fin n → Bit) = fun _ => 0 := by
  funext g
  simp [fold]

/-- Coordinate `(g, k)` of `∑_q v_q · (star row of q)`. -/
theorem star_sum (v : Fin n → Bit) (g : Option G) (k : Fin (m + 1)) :
    (∑ q : Option G × Fin (m + 1),
      v (e q) * ((([(q.1, (0 : Fin (m + 1))), (q.1, q.2)].count (g, k) : ℕ)) : Bit)) =
        (if k = 0 then fold e v g else 0) + v (e (g, k)) := by
  have hc : ∀ q : Option G × Fin (m + 1),
      ((([(q.1, (0 : Fin (m + 1))), (q.1, q.2)].count (g, k) : ℕ)) : Bit) =
        (if q = (g, k) then 1 else 0) + (if (q.1, (0 : Fin (m + 1))) = (g, k) then 1 else 0) := by
    intro q
    simp only [List.count_cons, List.count_nil, beq_iff_eq, zero_add, Prod.mk.eta]
    push_cast
    ring
  simp only [hc, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rw [add_comm]
  congr 1
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl, Fintype.sum_prod_type]
    unfold fold
    rw [Finset.sum_eq_single g]
    · simp
    · intro g' _ hg'
      simp [hg']
    · simp
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro h
    exact hk (congrArg Prod.snd h).symm

theorem zList_sum (r : R) (y : Option G → Bit) :
    ((zList eqs rhs r).map y).sum = ((eqs r).map (fun g => y (some g))).sum +
      (if rhs r = 1 then y none else 0) := by
  unfold zList
  rw [List.map_append, List.sum_append, List.map_map]
  split_ifs <;> simp [Function.comp_def]

/-- **Normalizer of the code.** -/
theorem mem_N (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR) (P : Pauli n) :
    P ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)) ↔
      (∀ gen ∈ gens, (gen.map (fun g => P.2 (e (some g, 0)))).sum = 0) ∧
        (∀ g k, P.2 (e (g, 0)) + P.2 (e (g, k)) = 0) ∧
          (∀ r, ((zList eqs rhs r).map (fold e P.1)).sum = 0) := by
  have hg' : ∀ g, g ∈ allOpt allG := by
    intro g; rcases g with _ | g
    · simp [allOpt]
    · simp [allOpt, hG g]
  rw [mem_normalizer_rows]
  constructor
  · intro h
    refine ⟨fun gen hgen => ?_, fun g k => ?_, fun r => ?_⟩
    · have := h (genRow e gen) ((mem_codeRows e eqs rhs gens allR allG).2
        (Or.inl ⟨gen, hgen, rfl⟩))
      rw [genRow, pair_xRowQ, List.map_map] at this
      exact this
    · have := h (starRow e g k) ((mem_codeRows e eqs rhs gens allR allG).2
        (Or.inr (Or.inl ⟨g, hg' g, k, rfl⟩)))
      rw [starRow, pair_xRowQ] at this
      simpa using this
    · have := h (zRow e eqs rhs r) ((mem_codeRows e eqs rhs gens allR allG).2
        (Or.inr (Or.inr ⟨r, hR r, rfl⟩)))
      rw [zRow, pair_zRowQ, sum_blowup] at this
      exact this
  · rintro ⟨h1, h2, h3⟩ row hrow
    rcases (mem_codeRows e eqs rhs gens allR allG).1 hrow with
      ⟨gen, hgen, rfl⟩ | ⟨g, -, k, rfl⟩ | ⟨r, -, rfl⟩
    · rw [genRow, pair_xRowQ, List.map_map]; exact h1 gen hgen
    · rw [starRow, pair_xRowQ]; simpa using h2 g k
    · rw [zRow, pair_zRowQ, sum_blowup]; exact h3 r

/-- **The rows commute.** -/
theorem codeRows_isotropic (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR)
    (hgen : ∀ gen ∈ gens, ∀ r, ((eqs r).map (listVec gen)).sum = 0) :
    rowSpace (codeRows e eqs rhs gens allR allG) ≤
      normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)) := by
  -- the pairing of a kernel generator with an augmented equation
  have hgz : ∀ gen ∈ gens, ∀ r,
      (gen.map (fun g => (((zList eqs rhs r).count (some g) : ℕ) : Bit))).sum = 0 := by
    intro gen hg r
    have := hgen gen hg r
    unfold listVec at this
    simp only [count_zList_some]
    rw [← cast_list_sum, count_sum_swap, cast_list_sum]
    exact this
  apply Submodule.span_le.2
  intro x hx
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hx
  rw [SetLike.mem_coe, mem_N e eqs rhs gens allR allG hG hR]
  rcases (mem_codeRows e eqs rhs gens allR allG).1 hrow with
    ⟨gen, hgen', rfl⟩ | ⟨g, -, k, rfl⟩ | ⟨r', -, rfl⟩
  · rw [genRow, decodeRow_xRowQ]
    refine ⟨fun _ _ => by simp, fun _ _ => by simp, fun r => ?_⟩
    rw [fold_count, List.map_map]
    have hm : (Prod.fst ∘ fun g => ((some g : Option G), (0 : Fin (m + 1)))) = some := rfl
    rw [hm, ← cast_list_sum, count_sum_swap, List.map_map, cast_list_sum]
    exact hgz gen hgen' r
  · rw [starRow, decodeRow_xRowQ]
    refine ⟨fun _ _ => by simp, fun _ _ => by simp, fun r => ?_⟩
    rw [fold_count]
    rw [← cast_list_sum, count_sum_swap]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Nat.cast_add]
    exact bit_add_self _
  · rw [zRow, decodeRow_zRowQ]
    refine ⟨fun gen hg => ?_, fun g k => ?_, fun _ => by rw [fold_zero]; exact sum_map_zero _⟩
    · simp only [Equiv.symm_apply_apply, count_blowup]
      exact hgz gen hg r'
    · simp only [Equiv.symm_apply_apply, count_blowup]
      exact bit_add_self _

/-- The block-parity functional: total `X`-parity on the copies of the extra coordinate. -/
def blockPar : Pauli n →ₗ[Bit] Bit where
  toFun v := ∑ k, v.1 (e (none, k))
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

theorem blockPar_S (v : Pauli n) (hv : v ∈ rowSpace (codeRows e eqs rhs gens allR allG)) :
    blockPar e v = 0 := by
  have hle : rowSpace (codeRows e eqs rhs gens allR allG) ≤ LinearMap.ker (blockPar e) := by
    apply Submodule.span_le.2
    intro x hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hx
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    rcases (mem_codeRows e eqs rhs gens allR allG).1 hrow with
      ⟨gen, -, rfl⟩ | ⟨g, -, k, rfl⟩ | ⟨r', -, rfl⟩
    · simp only [blockPar, LinearMap.coe_mk, AddHom.coe_mk, genRow, decodeRow_xRowQ,
        Equiv.symm_apply_apply]
      rw [← Nat.cast_sum, sum_count_pair, List.map_map]
      have : (gen.map (Prod.fst ∘ fun g => (some g, (0 : Fin (m + 1))))).count none = 0 := by
        apply List.count_eq_zero_of_not_mem
        simp
      rw [this]; rfl
    · simp only [blockPar, LinearMap.coe_mk, AddHom.coe_mk, starRow, decodeRow_xRowQ,
        Equiv.symm_apply_apply]
      rw [← Nat.cast_sum, sum_count_pair]
      simp only [List.map_cons, List.map_nil, List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> simp <;> decide
    · simp [blockPar, zRow, decodeRow_zRowQ]
  exact hle hv

/-- `x` on copy `0` of every coordinate, with `1` on copy `0` of the extra coordinate. -/
def logicalOf (x : G → Bit) : Pauli n :=
  (fun i => if (e.symm i).2 = 0 then (e.symm i).1.elim 1 x else 0, 0)

theorem logicalOf_mem_N (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR) {x : G → Bit}
    (hx : ∀ r, ((eqs r).map x).sum = rhs r) :
    logicalOf e x ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)) := by
  rw [mem_N e eqs rhs gens allR allG hG hR]
  refine ⟨fun _ _ => by simp [logicalOf], fun _ _ => by simp [logicalOf], fun r => ?_⟩
  have hf : fold e (logicalOf e x).1 = fun g => g.elim 1 x := by
    funext g
    simp only [fold, logicalOf, Equiv.symm_apply_apply]
    rw [Finset.sum_ite_eq']
    simp
  rw [hf, zList_sum]
  simp only [Option.elim]
  rw [hx r]
  rcases bit_cases (rhs r) with h | h <;> rw [h] <;> decide

theorem logicalOf_not_mem (x : G → Bit) :
    logicalOf e x ∉ rowSpace (codeRows e eqs rhs gens allR allG) := by
  intro h
  have := blockPar_S e eqs rhs gens allR allG _ h
  simp only [blockPar, LinearMap.coe_mk, AddHom.coe_mk, logicalOf, Equiv.symm_apply_apply] at this
  rw [Finset.sum_ite_eq'] at this
  simp at this

/-- Weight of a vector on `G`. -/
def gwt (x : G → Bit) : ℕ := (univ.filter (fun g => x g ≠ 0)).card

theorem card_filter_comp (p : Fin n → Prop) [DecidablePred p] :
    (univ.filter p).card = ∑ q : Option G × Fin (m + 1), if p (e q) then 1 else 0 := by
  rw [Finset.card_filter]
  exact (Equiv.sum_comp e (fun i => if p i then 1 else 0)).symm

theorem pauliWeight_logicalOf (x : G → Bit) : pauliWeight (logicalOf e x) = gwt x + 1 := by
  unfold pauliWeight gwt
  rw [card_filter_comp e, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [logicalOf, Equiv.symm_apply_apply, Option.elim]
  have h1 : ∀ v : Bit, (∑ k : Fin (m + 1), if (if k = 0 then v else 0) ≠ 0 ∨ (0 : Bit) ≠ 0
      then 1 else 0) = if v ≠ 0 then 1 else 0 := by
    intro v
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · simp
    · intro k _ hk; simp [hk]
    · simp
  simp only [Pi.zero_apply, h1]
  simp
  ring

/-- **G1.** A solution of `H x = s` gives a logical operator of weight `wt x + 1`. -/
theorem logical_of_sol (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR) {x : G → Bit}
    (hx : ∀ r, ((eqs r).map x).sum = rhs r) :
    ∃ P ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)),
      P ∉ rowSpace (codeRows e eqs rhs gens allR allG) ∧ pauliWeight P = gwt x + 1 :=
  ⟨logicalOf e x, logicalOf_mem_N e eqs rhs gens allR allG hG hR hx,
    logicalOf_not_mem e eqs rhs gens allR allG x, pauliWeight_logicalOf e x⟩

/-- `x` on copy `0` (nothing on the extra coordinate), as a linear map. -/
def liftK : (G → Bit) →ₗ[Bit] Pauli n where
  toFun x := (fun i => if (e.symm i).2 = 0 then (e.symm i).1.elim 0 x else 0, 0)
  map_add' x y := by
    apply Prod.ext
    · funext i
      simp only [Prod.fst_add, Pi.add_apply]
      split_ifs
      · rcases (e.symm i).1 with _ | g <;> simp
      · simp
    · simp
  map_smul' c x := by
    apply Prod.ext
    · funext i
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      split_ifs
      · rcases (e.symm i).1 with _ | g <;> simp
      · simp
    · simp

theorem liftK_listVec (gen : List G) : liftK e (listVec gen) = decodeRow (genRow e gen) := by
  rw [genRow, decodeRow_xRowQ]
  apply Prod.ext
  · funext i
    simp only [liftK, LinearMap.coe_mk, AddHom.coe_mk]
    rw [count_genRow_list]
    split_ifs
    · rcases (e.symm i).1 with _ | g
      · simp
      · simp [listVec]
    · simp
  · rfl

theorem pauliWeight_ge_snd (P : Pauli n) :
    (univ.filter (fun i => P.2 i ≠ 0)).card ≤ pauliWeight P := by
  unfold pauliWeight
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr

theorem pauliWeight_ge_fst (P : Pauli n) :
    (univ.filter (fun i => P.1 i ≠ 0)).card ≤ pauliWeight P := by
  unfold pauliWeight
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inl

/-- **G2.** A logical operator has weight `≥ m + 1`, or yields a solution of `H x = s` of weight
at most its own weight minus one. -/
theorem sol_of_logical (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR)
    (hspan : ∀ x : G → Bit, (∀ r, ((eqs r).map x).sum = 0) →
      x ∈ Submodule.span Bit {v | v ∈ gens.map listVec})
    {P : Pauli n}
    (hPN : P ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)))
    (hPS : P ∉ rowSpace (codeRows e eqs rhs gens allR allG)) :
    m + 1 ≤ pauliWeight P ∨
      ∃ x : G → Bit, (∀ r, ((eqs r).map x).sum = rhs r) ∧ gwt x + 1 ≤ pauliWeight P := by
  set S := rowSpace (codeRows e eqs rhs gens allR allG)
  obtain ⟨h1, h2, h3⟩ := (mem_N e eqs rhs gens allR allG hG hR P).1 hPN
  have hsplit : P = (P.1, 0) + (0, P.2) := by simp
  by_cases hB : ((0 : Fin n → Bit), P.2) ∈ S
  · -- the X part is a logical operator
    have hA : (P.1, (0 : Fin n → Bit)) ∉ S := by
      intro hA
      exact hPS (hsplit ▸ S.add_mem hA hB)
    right
    set y := fold e P.1
    have hzr : ∀ r, ((eqs r).map (fun g => y (some g))).sum + (if rhs r = 1 then y none else 0) = 0 :=
      fun r => by rw [← zList_sum]; exact h3 r
    -- weight bound for the fold
    have hwt : ∀ x : G → Bit, x = (fun g => y (some g)) → y none ≠ 0 →
        gwt x + 1 ≤ pauliWeight P := by
      intro x hx hy
      refine le_trans ?_ (pauliWeight_ge_fst P)
      rw [card_filter_comp e, Fintype.sum_prod_type, Fintype.sum_option]
      have hge : ∀ g : Option G, (if y g ≠ 0 then 1 else 0) ≤
          ∑ k : Fin (m + 1), if P.1 (e (g, k)) ≠ 0 then 1 else 0 := by
        intro g
        split_ifs with hyg
        · obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hyg
          exact le_trans (by simp [hk]) (Finset.single_le_sum (f := fun k : Fin (m + 1) =>
            if P.1 (e (g, k)) ≠ 0 then 1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
        · exact Nat.zero_le _
      have := hge none
      rw [if_pos hy] at this
      have hs : gwt x ≤ ∑ g : G, ∑ k : Fin (m + 1), if P.1 (e (some g, k)) ≠ 0 then 1 else 0 := by
        unfold gwt
        rw [Finset.card_filter]
        apply Finset.sum_le_sum
        intro g _
        rw [hx]
        exact hge (some g)
      omega
    rcases bit_cases (y none) with hy0 | hy1
    · -- homogeneous: then the X part lies in the stabilizer, a contradiction
      exfalso
      apply hA
      set x : G → Bit := fun g => y (some g)
      have hxk : ∀ r, ((eqs r).map x).sum = 0 := by
        intro r; have := hzr r; rw [hy0] at this; simpa using this
      have hxS : liftK e x ∈ S := by
        have hmem := Submodule.apply_mem_span_image_of_mem_span (liftK e) (hspan x hxk)
        refine Submodule.span_le.2 ?_ hmem
        rintro _ ⟨v, hv, rfl⟩
        obtain ⟨gen, hgen, rfl⟩ := List.mem_map.1 hv
        rw [liftK_listVec]
        exact Submodule.subset_span (List.mem_map.2 ⟨genRow e gen,
          (mem_codeRows e eqs rhs gens allR allG).2 (Or.inl ⟨gen, hgen, rfl⟩), rfl⟩)
      have hstar : ∀ g k, decodeRow (starRow (n := n) e g k) ∈ S := by
        intro g k
        have hg' : g ∈ allOpt allG := by
          rcases g with _ | g
          · simp [allOpt]
          · simp [allOpt, hG g]
        exact Submodule.subset_span (List.mem_map.2 ⟨starRow e g k,
          (mem_codeRows e eqs rhs gens allR allG).2 (Or.inr (Or.inl ⟨g, hg', k, rfl⟩)), rfl⟩)
      have hdecomp : (P.1, (0 : Fin n → Bit)) = liftK e x +
          ∑ q : Option G × Fin (m + 1), P.1 (e q) • decodeRow (starRow (n := n) e q.1 q.2) := by
        apply Prod.ext
        · funext i
          obtain ⟨q, rfl⟩ := e.surjective i
          rcases q with ⟨g, k⟩
          rw [Prod.fst_add, Prod.fst_sum, Pi.add_apply, Finset.sum_apply]
          simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, starRow, decodeRow_xRowQ,
            Equiv.symm_apply_apply]
          rw [star_sum]
          simp only [liftK, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]
          by_cases hk : k = 0
          · subst hk
            simp only [ite_true]
            rcases g with _ | g
            · simp only [Option.elim]
              change P.1 (e (none, 0)) = 0 + (y none + P.1 (e (none, 0)))
              rw [hy0]; simp
            · simp only [Option.elim]
              change P.1 (e (some g, 0)) = y (some g) + (y (some g) + P.1 (e (some g, 0)))
              rw [← add_assoc, bit_add_self, zero_add]
          · simp [hk]
        · rw [Prod.snd_add, Prod.snd_sum]
          simp [liftK, starRow, decodeRow_xRowQ]
      rw [hdecomp]
      exact S.add_mem hxS (S.sum_mem (fun q _ => S.smul_mem _ (hstar q.1 q.2)))
    · refine ⟨fun g => y (some g), fun r => ?_, hwt _ rfl (by rw [hy1]; decide)⟩
      have := hzr r
      rw [hy1] at this
      rcases bit_cases (rhs r) with h | h
      · simpa [h] using this
      · rw [h] at this ⊢
        rw [if_pos rfl] at this
        have hh : ∀ a : Bit, a + 1 = 0 → a = 1 := by decide
        exact hh _ this
  · -- the Z part is a logical operator: constant on the copies, hence heavy
    left
    have hz : P.2 ≠ 0 := by
      intro h0
      apply hB
      rw [h0]
      exact S.zero_mem
    obtain ⟨i, hi⟩ : ∃ i, P.2 i ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hz (funext hne)
    obtain ⟨⟨g, k0⟩, rfl⟩ := e.surjective i
    have hconst : ∀ k, P.2 (e (g, k)) = P.2 (e (g, 0)) := by
      intro k
      have := h2 g k
      have hh : ∀ a b : Bit, a + b = 0 → b = a := by decide
      exact hh _ _ this
    have hall : ∀ k, P.2 (e (g, k)) ≠ 0 := by
      intro k; rw [hconst k]; rw [← hconst k0]; exact hi
    refine le_trans ?_ (pauliWeight_ge_snd P)
    have : (univ.image (fun k : Fin (m + 1) => e (g, k))) ⊆ univ.filter (fun i => P.2 i ≠ 0) := by
      intro i hi'
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hi'
      simp [hall k]
    refine le_trans ?_ (Finset.card_le_card this)
    rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj (e.injective hab)).2)]
    simp

end Generic

/-- A stabilizer group with a logical operator has a distance. -/
theorem exists_isDistance_of_logical {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (h : ∃ x ∈ normalizer (symplectic n) S, x ∉ S) :
    ∃ d, IsDistance S d := by
  classical
  have hex : ∃ w, ∃ x ∈ normalizer (symplectic n) S, x ∉ S ∧ pauliWeight x = w := by
    obtain ⟨x, hxN, hxS⟩ := h
    exact ⟨_, x, hxN, hxS, rfl⟩
  refine ⟨Nat.find hex, (isDistance_iff_minWeight S hS _).2 ⟨Nat.find_spec hex, ?_⟩⟩
  intro x hxN hxS
  exact Nat.find_min' hex ⟨x, hxN, hxS, rfl⟩

/-! ## The code of a normalized formula -/

namespace Formula

variable (F : Formula)

/-- All equations, as a list. -/
def allRow : List F.Row :=
  (List.finRange F.N).map Sum.inl ++ ((List.finRange F.M).map (fun c => Sum.inr (Sum.inl c)) ++
    (F.allOcc.map (fun o => Sum.inr (Sum.inr (Sum.inl o))) ++
      F.allOcc.map (fun o => Sum.inr (Sum.inr (Sum.inr o)))))

theorem mem_allRow (r : F.Row) : r ∈ F.allRow := by
  rcases r with i | c | o | o <;> simp [allRow, F.mem_allOcc]

/-- All coordinates, as a list. -/
def allCoord : List F.Coord :=
  (List.finRange F.N).map F.cP ++ ((List.finRange F.N).map F.cN ++ (F.allOcc.map F.cS ++
    (F.allOcc.map F.cW ++ F.allOcc.map F.cC)))

theorem mem_allCoord (g : F.Coord) : g ∈ F.allCoord := by
  rcases g with i | i | o | o | o <;> simp [allCoord, F.mem_allOcc]

/-- Each coordinate is repeated `mm + 1 = N + K + 2` times. -/
def mm : ℕ := F.N + F.K + 1

/-- Number of coordinates `2N + 3K`. -/
def ncoord : ℕ := F.N + (F.N + (F.K + (F.K + F.K)))

/-- Number of qubits `(2N + 3K + 1)(N + K + 2)`. -/
def nq : ℕ := (F.ncoord + 1) * (F.mm + 1)

/-- The threshold `N + K + 1`. -/
def thr : ℕ := F.N + F.K + 1

def occEquiv : F.Occ ≃ Fin F.K := finSigmaFinEquiv

def coordEquiv : F.Coord ≃ Fin F.ncoord :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr F.occEquiv ((Equiv.sumCongr F.occEquiv F.occEquiv).trans finSumFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv

/-- The qubit numbering. -/
def qEquiv : Option F.Coord × Fin (F.mm + 1) ≃ Fin F.nq :=
  (Equiv.prodCongr ((Equiv.optionCongr F.coordEquiv).trans (finSuccEquiv F.ncoord).symm)
    (Equiv.refl _)).trans finProdFinEquiv

/-- **The check rows of the code of `F`.** -/
def rows : List (List (PauliCoord F.nq)) :=
  codeRows F.qEquiv F.eqList F.eqRhs F.kerGens F.allRow F.allCoord

theorem rows_isotropic :
    rowSpace F.rows ≤ normalizer (symplectic F.nq) (rowSpace F.rows) :=
  codeRows_isotropic F.qEquiv F.eqList F.eqRhs F.kerGens F.allRow F.allCoord F.mem_allCoord
    F.mem_allRow (fun gen hg => F.kerGens_ker gen hg)

theorem sol_or_heavy {P : Pauli F.nq}
    (hN : P ∈ normalizer (symplectic F.nq) (rowSpace F.rows)) (hS : P ∉ rowSpace F.rows) :
    F.mm + 1 ≤ pauliWeight P ∨ ∃ x, F.IsSol x ∧ F.wt x + 1 ≤ pauliWeight P :=
  sol_of_logical F.qEquiv F.eqList F.eqRhs F.kerGens F.allRow F.allCoord F.mem_allCoord
    F.mem_allRow (fun _ hx => F.ker_mem_span hx) hN hS

/-- Every logical operator has weight `≥ N + K + 1`. -/
theorem logical_weight_ge {P : Pauli F.nq}
    (hN : P ∈ normalizer (symplectic F.nq) (rowSpace F.rows)) (hS : P ∉ rowSpace F.rows) :
    F.thr ≤ pauliWeight P := by
  rcases F.sol_or_heavy hN hS with h | ⟨x, hx, hw⟩
  · unfold thr; unfold mm at h; omega
  · have := F.wt_ge hx
    unfold thr; omega

/-- **Satisfiable iff there is an uncorrectable erased set of size `≤ N + K + 1`.** -/
theorem sat_iff_small :
    (∃ a, F.Sat a) ↔ ∃ E : Finset (Fin F.nq), E.card ≤ F.thr ∧
      0 < ambiguity (symplectic F.nq) (rowSpace F.rows) (supported E) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨x, hx, hw, -⟩ := F.sat_sol ha
    obtain ⟨P, hN, hS, hP⟩ := logical_of_sol F.qEquiv F.eqList F.eqRhs F.kerGens F.allRow
      F.allCoord F.mem_allCoord F.mem_allRow hx
    refine ⟨pauliSupport P, ?_, (uncorrectable_iff_logical _ F.rows_isotropic _).2
      ⟨P, hN, mem_supported_pauliSupport P, hS⟩⟩
    rw [card_pauliSupport, hP]
    change F.wt x + 1 ≤ F.thr
    unfold thr; omega
  · rintro ⟨E, hE, hpos⟩
    obtain ⟨P, hN, hPE, hS⟩ := (uncorrectable_iff_logical _ F.rows_isotropic E).1 hpos
    have hwP := pauliWeight_le_card hPE
    rcases F.sol_or_heavy hN hS with h | ⟨x, hx, hw⟩
    · exfalso; unfold thr at hE; unfold mm at h; omega
    · refine ⟨F.assignOf x, ?_⟩
      by_contra hns
      have := F.wt_of_unsat hx hns
      unfold thr at hE; omega

/-- **The distance decides satisfiability.** -/
theorem isDistance_le_iff {d : ℕ} (hd : IsDistance (rowSpace F.rows) d) :
    d ≤ F.thr ↔ ∃ a, F.Sat a := by
  obtain ⟨⟨x0, hx0N, hx0S, hx0w⟩, hlow⟩ := (isDistance_iff_minWeight _ F.rows_isotropic d).1 hd
  constructor
  · intro hle
    exact F.sat_iff_small.2 ⟨pauliSupport x0, by rw [card_pauliSupport, hx0w]; exact hle,
      (uncorrectable_iff_logical _ F.rows_isotropic _).2
        ⟨x0, hx0N, mem_supported_pauliSupport x0, hx0S⟩⟩
  · intro hsat
    obtain ⟨E, hE, hpos⟩ := F.sat_iff_small.1 hsat
    obtain ⟨P, hN, hPE, hS⟩ := (uncorrectable_iff_logical _ F.rows_isotropic E).1 hpos
    exact le_trans (hlow P hN hS) (le_trans (pauliWeight_le_card hPE) hE)

theorem isDistance_eq_of_sat {d : ℕ} (hd : IsDistance (rowSpace F.rows) d)
    (hsat : ∃ a, F.Sat a) : d = F.thr := by
  obtain ⟨⟨x0, hx0N, hx0S, hx0w⟩, -⟩ := (isDistance_iff_minWeight _ F.rows_isotropic d).1 hd
  have h1 := (F.isDistance_le_iff hd).2 hsat
  have h2 := F.logical_weight_ge hx0N hx0S
  omega

/-- With no empty clause the code has a logical qubit, hence a distance. -/
theorem exists_isDistance (hpos : ∀ c, 0 < F.len c) : ∃ d, IsDistance (rowSpace F.rows) d := by
  obtain ⟨x, hx⟩ := F.exists_sol hpos
  obtain ⟨P, hN, hS, -⟩ := logical_of_sol F.qEquiv F.eqList F.eqRhs F.kerGens F.allRow
    F.allCoord F.mem_allCoord F.mem_allRow hx
  exact exists_isDistance_of_logical _ F.rows_isotropic ⟨P, hN, hS⟩

end Formula

/-! ## The reduction from `Std.Sat.CNF Nat` -/

/-- An instance of the distance problem: `n` qubits, check rows, a threshold. -/
structure Instance where
  n : ℕ
  rows : List (List (PauliCoord n))
  thr : ℕ

/-- **The reduction.** `reduce φ` is the code of `formulaOf φ` (a formula with an empty clause is
first replaced by `x₀ ∧ ¬x₀`), with threshold `N + K + 1`. -/
def reduce (φ : Std.Sat.CNF Nat) : Instance :=
  ⟨(formulaOf φ).nq, (formulaOf φ).rows, (formulaOf φ).thr⟩

theorem reduce_isotropic (φ : Std.Sat.CNF Nat) :
    rowSpace (reduce φ).rows ≤ normalizer (symplectic (reduce φ).n) (rowSpace (reduce φ).rows) :=
  (formulaOf φ).rows_isotropic

/-- **Correctness, erasure form.** -/
theorem reduce_correct (φ : Std.Sat.CNF Nat) :
    (∃ a, φ.Sat a) ↔ ∃ E : Finset (Fin (reduce φ).n), E.card ≤ (reduce φ).thr ∧
      0 < ambiguity (symplectic (reduce φ).n) (rowSpace (reduce φ).rows) (supported E) := by
  rw [cnf_sat_iff]
  exact (formulaOf φ).sat_iff_small

/-- **Correctness, distance form.** -/
theorem reduce_isDistance_le_iff (φ : Std.Sat.CNF Nat) {d : ℕ}
    (hd : IsDistance (rowSpace (reduce φ).rows) d) : d ≤ (reduce φ).thr ↔ ∃ a, φ.Sat a := by
  rw [cnf_sat_iff]
  exact (formulaOf φ).isDistance_le_iff hd

theorem reduce_isDistance_eq (φ : Std.Sat.CNF Nat) {d : ℕ}
    (hd : IsDistance (rowSpace (reduce φ).rows) d) (hsat : ∃ a, φ.Sat a) : d = (reduce φ).thr :=
  (formulaOf φ).isDistance_eq_of_sat hd ((cnf_sat_iff φ).1 hsat)

/-- **The code always has a distance** (at least one logical qubit). -/
theorem reduce_exists_isDistance (φ : Std.Sat.CNF Nat) :
    ∃ d, IsDistance (rowSpace (reduce φ).rows) d :=
  (formulaOf φ).exists_isDistance (formulaOf_len_pos φ)

/-! ## Size bounds -/

theorem sum_map_le_mul {α : Type} (l : List α) (f : α → ℕ) (b : ℕ) (h : ∀ a ∈ l, f a ≤ b) :
    (l.map f).sum ≤ l.length * b := by
  have := List.sum_le_card_nsmul (l.map f) b (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact h a ha)
  simpa using this

namespace Formula

variable (F : Formula)

theorem length_allOcc : F.allOcc.length = F.K := by
  unfold allOcc K
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_finRange]
  rw [← Fin.sum_univ_def]

theorem length_occPart (i : Fin F.N) : (F.occPart i).length ≤ 2 * F.K := by
  unfold occPart K
  rw [List.length_flatMap, Finset.mul_sum]
  simp only [List.length_flatMap]
  rw [← Fin.sum_univ_def]
  apply Finset.sum_le_sum
  intro c _
  rw [← Fin.sum_univ_def]
  calc (∑ j : Fin (F.len c), (if F.var ⟨c, j⟩ = i then [F.cW ⟨c, j⟩, F.cC ⟨c, j⟩] else []).length)
      ≤ ∑ _j : Fin (F.len c), 2 := Finset.sum_le_sum (fun j _ => by split_ifs <;> simp)
    _ = 2 * F.len c := by simp [mul_comm]

theorem length_eqList_le (r : F.Row) : (F.eqList r).length ≤ F.K + 3 := by
  rcases r with i | c | o | o
  · simp [eqList]
  · simp only [eqList, List.length_map, List.length_finRange]
    have : F.len c ≤ F.K := by
      unfold K
      exact Finset.single_le_sum (f := F.len) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · simp [eqList]
  · simp [eqList]

theorem length_allRow : F.allRow.length = F.N + (F.M + (F.K + F.K)) := by
  simp [allRow, length_allOcc]

theorem length_allCoord : F.allCoord.length = F.ncoord := by
  simp [allCoord, length_allOcc, ncoord]

/-- **Number of nonzero entries of the check rows.** -/
theorem rowIncidences_rows_le :
    rowIncidences F.rows ≤ F.N * (2 + 2 * F.K) + 4 * F.K +
      ((F.ncoord + 1) * (F.mm + 1)) * 2 + (F.N + (F.M + (F.K + F.K))) * ((F.K + 4) * (F.mm + 1)) := by
  unfold rows codeRows rowIncidences
  simp only [List.map_append, List.sum_append, List.map_map]
  have hA : (F.kerGens.map (List.length ∘ genRow F.qEquiv)).sum ≤
      F.N * (2 + 2 * F.K) + 4 * F.K := by
    simp only [kerGens, List.map_append, List.sum_append, List.map_map]
    have h1 := sum_map_le_mul (List.finRange F.N) (List.length ∘ F.genP) (2 + 2 * F.K) (by
      intro i _
      simp only [Function.comp_apply, genP, List.length_append, List.length_cons, List.length_nil]
      have := F.length_occPart i
      omega)
    have h2 := sum_map_le_mul F.allOcc (List.length ∘ F.genD) 4 (by intro o _; simp [genD])
    rw [List.length_finRange] at h1
    rw [length_allOcc] at h2
    have he : (List.finRange F.N).map ((List.length ∘ genRow F.qEquiv) ∘ F.genP) =
        (List.finRange F.N).map (List.length ∘ F.genP) :=
      List.map_congr_left (fun i _ => by simp [genRow, xRowQ])
    have hf : F.allOcc.map ((List.length ∘ genRow F.qEquiv) ∘ F.genD) =
        F.allOcc.map (List.length ∘ F.genD) :=
      List.map_congr_left (fun o _ => by simp [genRow, xRowQ])
    rw [he, hf]
    omega
  have hB : (((allOpt F.allCoord).flatMap (fun g => (List.finRange (F.mm + 1)).map
      (starRow F.qEquiv g))).map List.length).sum ≤ ((F.ncoord + 1) * (F.mm + 1)) * 2 := by
    have h1 := sum_map_le_mul ((allOpt F.allCoord).flatMap (fun g => (List.finRange (F.mm + 1)).map
      (starRow F.qEquiv g))) List.length 2 (by
        intro row hrow
        obtain ⟨g, -, hg⟩ := List.mem_flatMap.1 hrow
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
        simp [starRow, xRowQ])
    have h2 : ((allOpt F.allCoord).flatMap (fun g => (List.finRange (F.mm + 1)).map
        (starRow F.qEquiv g))).length = (F.ncoord + 1) * (F.mm + 1) := by
      rw [List.length_flatMap]
      simp only [List.length_map, List.length_finRange]
      rw [List.map_const', List.sum_replicate, smul_eq_mul]
      simp [allOpt, length_allCoord]
    rw [h2] at h1
    exact h1
  have hC : (F.allRow.map (List.length ∘ zRow F.qEquiv F.eqList F.eqRhs)).sum ≤
      (F.N + (F.M + (F.K + F.K))) * ((F.K + 4) * (F.mm + 1)) := by
    have h1 := sum_map_le_mul F.allRow (List.length ∘ zRow F.qEquiv F.eqList F.eqRhs)
      ((F.K + 4) * (F.mm + 1)) (by
        intro r _
        simp only [Function.comp_apply, zRow, zRowQ, List.length_map, blowup, List.length_flatMap,
          List.length_finRange]
        rw [List.map_const', List.sum_replicate, smul_eq_mul]
        apply Nat.mul_le_mul_right
        unfold zList
        rw [List.length_append, List.length_map]
        have := F.length_eqList_le r
        split_ifs <;> simp <;> omega)
    rw [length_allRow] at h1
    exact h1
  omega

/-- Number of qubits. -/
theorem nq_eq : F.nq = (2 * F.N + 3 * F.K + 1) * (F.N + F.K + 2) := by
  unfold nq ncoord mm; ring

theorem arith_bound (N K M : ℕ) (hM : M ≤ K) :
    N * (2 + 2 * K) + 4 * K + (N + (N + (K + (K + K))) + 1) * (N + K + 1 + 1) * 2 +
      (N + (M + (K + K))) * ((K + 4) * (N + K + 1 + 1)) ≤ 12 * (N + K + 2) ^ 3 := by
  set s := N + K + 2 with hs
  have e1 : N * (2 + 2 * K) ≤ s * (2 * s) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : (N + (N + (K + (K + K))) + 1) * (N + K + 1 + 1) * 2 ≤ (3 * s) * s * 2 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  have e3 : (N + (M + (K + K))) * ((K + 4) * (N + K + 1 + 1)) ≤ (3 * s) * ((2 * s) * s) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
  have hs2 : 2 ≤ s := by omega
  have e4 : 4 * K ≤ 2 * s * s := by nlinarith
  have e5 : 8 * s * s ≤ 4 * s * s * s := by nlinarith
  nlinarith

/-- **Polynomial bounds** for a formula with `M ≤ K` (no empty clause): at most
`3 (N + K + 2)^2` qubits and `12 (N + K + 2)^3` nonzero entries. -/
theorem size_bounds (hM : F.M ≤ F.K) :
    F.nq ≤ 3 * (F.N + F.K + 2) ^ 2 ∧ rowIncidences F.rows ≤ 12 * (F.N + F.K + 2) ^ 3 := by
  constructor
  · rw [nq_eq]
    have : 2 * F.N + 3 * F.K + 1 ≤ 3 * (F.N + F.K + 2) := by omega
    calc (2 * F.N + 3 * F.K + 1) * (F.N + F.K + 2) ≤ (3 * (F.N + F.K + 2)) * (F.N + F.K + 2) :=
          Nat.mul_le_mul_right _ this
      _ = 3 * (F.N + F.K + 2) ^ 2 := by ring
  · have hr := F.rowIncidences_rows_le
    unfold ncoord mm at hr
    exact le_trans hr (arith_bound _ _ _ hM)

end Formula

/-- **Size of the reduction** in terms of the input: with `V = 1 + (largest variable index)` and
`L = number of literal occurrences` of `φ`, at most `3 (V + L + 4)^2` qubits and
`12 (V + L + 4)^3` nonzero entries. -/
theorem reduce_size (φ : Std.Sat.CNF Nat) :
    (reduce φ).n ≤ 3 * (varBound φ.clauses.toList + litCount φ.clauses.toList + 4) ^ 2 ∧
      rowIncidences (reduce φ).rows ≤
        12 * (varBound φ.clauses.toList + litCount φ.clauses.toList + 4) ^ 3 := by
  obtain ⟨hN, hK, hM⟩ := formulaOf_size φ
  obtain ⟨h1, h2⟩ := (formulaOf φ).size_bounds hM
  have hle : (formulaOf φ).N + (formulaOf φ).K + 2 ≤
      varBound φ.clauses.toList + litCount φ.clauses.toList + 4 := by omega
  refine ⟨le_trans h1 ?_, le_trans h2 ?_⟩
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle 2)
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle 3)

/-- The exact number of qubits and the threshold. -/
theorem reduce_n_thr (φ : Std.Sat.CNF Nat) :
    (reduce φ).n = (2 * (formulaOf φ).N + 3 * (formulaOf φ).K + 1) *
        ((formulaOf φ).N + (formulaOf φ).K + 2) ∧
      (reduce φ).thr = (formulaOf φ).N + (formulaOf φ).K + 1 :=
  ⟨(formulaOf φ).nq_eq, rfl⟩

end QecReliability.SatReduction

#print axioms QecReliability.SatReduction.reduce_isotropic
#print axioms QecReliability.SatReduction.reduce_correct
#print axioms QecReliability.SatReduction.reduce_isDistance_le_iff
#print axioms QecReliability.SatReduction.reduce_isDistance_eq
#print axioms QecReliability.SatReduction.reduce_exists_isDistance
#print axioms QecReliability.SatReduction.reduce_size
#print axioms QecReliability.SatReduction.reduce_n_thr
#print axioms QecReliability.SatReduction.logical_of_sol
#print axioms QecReliability.SatReduction.sol_of_logical
#print axioms QecReliability.SatReduction.codeRows_isotropic
