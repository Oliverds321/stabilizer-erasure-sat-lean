import EnumeratorExample
import HybridEstimator

set_option autoImplicit false

/-!
# Exact coefficient tables from a verified executable enumeration

For check rows `rows` on `n` qubits, the exact Bernstein tables of the paper's computed section,

    f_j = (1 / C(n,j)) Σ_{|E|=j} 2^{-d_E},       u_j = #{|E| = j : d_E > 0} / C(n,j),

are produced by an executable function and proved equal to the definitions.

* Specification (slow): `layerScoreSum rows j : ℚ = Σ_{|E|=j} (1/2)^{ambiguityRank rows E}` and
  `layerUncCount rows j`, over `Finset.univ : Finset (Finset (Fin n))`; tied to
  `erasureScore` / `uncorrectable` of `rowSpace rows` for arbitrary rows.
* Fast: one pass over the bitmasks `e < 2^n`, an `Array ℕ` accumulator, and a GF(2) elimination
  `rankB` on rows stored as natural-number bitmasks (column `i` = bit `i`, X part in bits
  `0..n-1`, Z part in bits `n..2n-1`). `rankB` is proved equal to the verified
  `BinaryElimination.rank`, and `ambFast` to `ambiguityRank`.
* `scoreNat_eq_slow`, `uncNat_eq_slow`: fast = slow (no `implemented_by`).
* `fRat_spec`, `uRat_spec`: the printed fractions are `layerAverage id (erasureScore S) j` and
  `layerFraction S j`.
-/

namespace QecPhysical.Stabilizer.ExactTable

open scoped BigOperators
open Finset
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecReliability.BinaryElimination

/-! ## Bitmask rows -/

/-- The row of `Row k` with coordinate `i` equal to bit `i` of `x`. -/
def toRow (k x : ℕ) : Row k := fun i => if x.testBit i.val then 1 else 0

theorem toRow_zero (k : ℕ) : toRow k 0 = 0 := by
  funext i
  simp [toRow]

theorem toRow_xor (k a b : ℕ) : toRow k (a ^^^ b) = toRow k a + toRow k b := by
  funext i
  simp only [toRow, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i.val <;> cases b.testBit i.val <;> decide

theorem toRow_shift (k x : ℕ) : toRow k (x >>> 1) = tailMap k (toRow (k + 1) x) := by
  funext i
  simp only [toRow, tailMap, LinearMap.coe_mk, AddHom.coe_mk, Nat.testBit_shiftRight,
    Fin.val_succ, Nat.add_comm 1]

theorem toRow_clear (k x p : ℕ) :
    toRow k ((if x.testBit 0 then x ^^^ p else x) >>> 1) =
      clearTail (toRow (k + 1) p) (toRow (k + 1) x) := by
  funext i
  simp only [toRow, clearTail, LinearMap.coe_mk, AddHom.coe_mk, Nat.testBit_shiftRight,
    Fin.val_succ, Nat.add_comm 1]
  rcases Bool.eq_false_or_eq_true (x.testBit 0) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (x.testBit (i.val + 1)) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (p.testBit (i.val + 1)) with h2 | h2 <;>
  simp [h0, h1, h2, Nat.testBit_xor]

/-- GF(2) elimination on bitmask rows, column by column (same pivoting as `rank`), dropping
rows that become zero. -/
def rankB : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | k + 1, rows =>
    match rows.find? (fun x => x.testBit 0) with
    | none => rankB k ((rows.map (· >>> 1)).filter (fun x => x != 0))
    | some p =>
      rankB k ((rows.map (fun x => (if x.testBit 0 then x ^^^ p else x) >>> 1)).filter
        (fun x => x != 0)) + 1

theorem find_map_toRow (k : ℕ) (xs : List ℕ) :
    (xs.map (toRow (k + 1))).find? (fun x => decide (x 0 ≠ 0)) =
      (xs.find? (fun x => x.testBit 0)).map (toRow (k + 1)) := by
  have h : ((fun x : Row (k + 1) => decide (x 0 ≠ 0)) ∘ toRow (k + 1)) = (fun x => x.testBit 0) := by
    funext x
    simp only [Function.comp, toRow]
    rcases Bool.eq_false_or_eq_true (x.testBit 0) with h0 | h0 <;> simp [h0]
  rw [List.find?_map, h]

theorem rank_filter_zero (k : ℕ) (L : List ℕ) :
    rank k ((L.filter (fun x => x != 0)).map (toRow k)) = rank k (L.map (toRow k)) := by
  rw [rank_correct, rank_correct]
  have h : spanRows ((L.filter (fun x => x != 0)).map (toRow k)) = spanRows (L.map (toRow k)) := by
    unfold spanRows
    apply le_antisymm
    · apply Submodule.span_mono
      intro v hv
      simp only [Set.mem_setOf_eq, List.mem_map, List.mem_filter] at hv ⊢
      obtain ⟨x, ⟨hx, _⟩, rfl⟩ := hv
      exact ⟨x, hx, rfl⟩
    · apply Submodule.span_le.mpr
      intro v hv
      simp only [Set.mem_setOf_eq, List.mem_map] at hv
      obtain ⟨x, hx, rfl⟩ := hv
      by_cases h0 : x = 0
      · subst h0
        rw [toRow_zero]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span (List.mem_map.mpr
          ⟨x, List.mem_filter.mpr ⟨hx, by simpa using h0⟩, rfl⟩)
  rw [h]

/-- **The bitmask elimination computes the verified rank.** -/
theorem rankB_eq : ∀ (k : ℕ) (xs : List ℕ), rankB k xs = rank k (xs.map (toRow k))
  | 0, _ => by simp [rankB, rank]
  | k + 1, xs => by
    simp only [rankB, rank]
    rw [find_map_toRow]
    cases h : xs.find? (fun x => x.testBit 0) with
    | none =>
      simp only [Option.map_none]
      rw [rankB_eq k, rank_filter_zero, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x _
      simp only [Function.comp, cacheRow_eq, toRow_shift]
    | some p =>
      simp only [Option.map_some]
      rw [rankB_eq k, rank_filter_zero, List.map_map, List.map_map]
      congr 2
      apply List.map_congr_left
      intro x _
      simp only [Function.comp, cacheRow_eq, toRow_clear]

/-! ## Rows as bitmasks -/

variable {n : ℕ}

/-- Column of a sparse coordinate: `Xi ↦ i`, `Zi ↦ n + i`. -/
def coordIdx : PauliCoord n → ℕ
  | .inl i => i.val
  | .inr i => n + i.val

/-- A sparse row as a bitmask (duplicate entries cancel, as in `decodeRow`). -/
def rowBits (row : List (PauliCoord n)) : ℕ := row.foldr (fun c acc => 2 ^ coordIdx c ^^^ acc) 0

theorem flatten_castAdd (x : Pauli n) (j : Fin n) : flatten n x (Fin.castAdd n j) = x.1 j := by
  change Fin.addCases x.1 x.2 (Fin.castAdd n j) = x.1 j
  exact Fin.addCases_left j

theorem flatten_natAdd (x : Pauli n) (j : Fin n) : flatten n x (Fin.natAdd n j) = x.2 j := by
  change Fin.addCases x.1 x.2 (Fin.natAdd n j) = x.2 j
  exact Fin.addCases_right j

theorem toRow_coord (c : PauliCoord n) :
    toRow (n + n) (2 ^ coordIdx c) = flatten n (coordPauli c) := by
  funext idx
  refine Fin.addCases (fun j => ?_) (fun j => ?_) idx
  · rw [flatten_castAdd]
    cases c with
    | inl i =>
      simp only [toRow, coordIdx, Nat.testBit_two_pow, Fin.coe_castAdd, coordPauli, Sum.elim_inl,
        xUnit, Pi.single_apply]
      by_cases h : j = i
      · subst h; simp
      · have : i.val ≠ j.val := fun h' => h (Fin.ext h'.symm)
        simp [h, this]
    | inr i =>
      simp only [toRow, coordIdx, Nat.testBit_two_pow, Fin.coe_castAdd, coordPauli, Sum.elim_inr,
        zUnit]
      have : n + i.val ≠ j.val := by omega
      simp [this]
  · rw [flatten_natAdd]
    cases c with
    | inl i =>
      simp only [toRow, coordIdx, Nat.testBit_two_pow, Fin.coe_natAdd, coordPauli, Sum.elim_inl,
        xUnit]
      have : i.val ≠ n + j.val := by omega
      simp [this]
    | inr i =>
      simp only [toRow, coordIdx, Nat.testBit_two_pow, Fin.coe_natAdd, coordPauli, Sum.elim_inr,
        zUnit, Pi.single_apply]
      by_cases h : j = i
      · subst h; simp
      · have h' : ¬ (i.val = j.val) := fun h' => h (Fin.ext h'.symm)
        simp [h, h']

theorem toRow_rowBits (row : List (PauliCoord n)) :
    toRow (n + n) (rowBits row) = flatten n (decodeRow row) := by
  induction row with
  | nil =>
    simp only [rowBits, List.foldr_nil, toRow_zero, decodeRow, List.map_nil, List.sum_nil, map_zero]
  | cons c r ih =>
    have h1 : rowBits (c :: r) = 2 ^ coordIdx c ^^^ rowBits r := rfl
    have h2 : decodeRow (c :: r) = coordPauli c + decodeRow r := by
      simp [decodeRow]
    rw [h1, h2, toRow_xor, toRow_coord, ih, map_add]

/-- Erased-set bitmask `e` (bit `i` = qubit `i`) as a finset. -/
def maskSet (n e : ℕ) : Finset (Fin n) := univ.filter (fun i => e.testBit i.val)

/-- Both columns of every erased qubit. -/
def colMask (n e : ℕ) : ℕ := e ||| (e <<< n)

/-- Complement within `n` qubits. -/
def compl (n e : ℕ) : ℕ := (2 ^ n - 1) ^^^ e

theorem mem_maskSet (e : ℕ) (i : Fin n) : i ∈ maskSet n e ↔ e.testBit i.val = true := by
  simp [maskSet]

theorem maskSet_compl (e : ℕ) : maskSet n (compl n e) = (maskSet n e)ᶜ := by
  ext i
  simp [maskSet, compl, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]

theorem compl_lt {e : ℕ} (he : e < 2 ^ n) : compl n e < 2 ^ n :=
  Nat.xor_lt_two_pow (Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos) he

theorem toRow_and_colMask (x e : ℕ) (he : e < 2 ^ n) (v : Pauli n)
    (hv : toRow (n + n) x = flatten n v) :
    toRow (n + n) (x &&& colMask n e) = flatten n (mask n (maskSet n e) v) := by
  funext idx
  refine Fin.addCases (fun j => ?_) (fun j => ?_) idx
  · have hvj := congrFun hv (Fin.castAdd n j)
    rw [flatten_castAdd] at hvj
    rw [flatten_castAdd]
    simp only [mask, LinearMap.coe_mk, AddHom.coe_mk, mem_maskSet, ← hvj]
    simp only [toRow, colMask, Fin.coe_castAdd, Nat.testBit_and, Nat.testBit_or,
      Nat.testBit_shiftLeft]
    have hj : ¬ (j.val ≥ n) := by omega
    simp only [hj, decide_false, Bool.false_and, Bool.or_false]
    rcases Bool.eq_false_or_eq_true (x.testBit j.val) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (e.testBit j.val) with h2 | h2 <;> simp [h1, h2]
  · have hvj := congrFun hv (Fin.natAdd n j)
    rw [flatten_natAdd] at hvj
    rw [flatten_natAdd]
    simp only [mask, LinearMap.coe_mk, AddHom.coe_mk, mem_maskSet, ← hvj]
    simp only [toRow, colMask, Fin.coe_natAdd, Nat.testBit_and, Nat.testBit_or,
      Nat.testBit_shiftLeft]
    have hlt : e < 2 ^ (n + j.val) := lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hj : n + j.val ≥ n := by omega
    rw [Nat.testBit_lt_two_pow hlt, show n + j.val - n = j.val by omega]
    simp only [hj, decide_true, Bool.true_and, Bool.false_or]
    rcases Bool.eq_false_or_eq_true (x.testBit (n + j.val)) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (e.testBit j.val) with h2 | h2 <;> simp [h1, h2]

/-- All rows as bitmasks. -/
def rowsBits (rows : List (List (PauliCoord n))) : List ℕ := rows.map rowBits

/-- Fast erasure ambiguity of the erased set with bitmask `e`; `s` is the rank of all rows. -/
def ambFast (n : ℕ) (rb : List ℕ) (s e : ℕ) : ℕ :=
  (2 * (maskSet n e).card - rankB (n + n) (rb.map (· &&& colMask n e))) -
    (s - rankB (n + n) (rb.map (· &&& colMask n (compl n e))))

theorem restricted_bits (rows : List (List (PauliCoord n))) {e : ℕ} (he : e < 2 ^ n) :
    ((rowsBits rows).map (· &&& colMask n e)).map (toRow (n + n)) =
      restrictedRows rows (maskSet n e) := by
  unfold rowsBits restrictedRows
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro row _
  simp only [Function.comp, cacheRow_eq]
  exact toRow_and_colMask _ _ he _ (toRow_rowBits row)

/-- **The fast ambiguity is `ambiguityRank`** (hence the erasure ambiguity `d_E`). -/
theorem ambFast_eq (rows : List (List (PauliCoord n))) {e : ℕ} (he : e < 2 ^ n) :
    ambFast n (rowsBits rows) (rankB (n + n) (rowsBits rows)) e = ambiguityRank rows (maskSet n e) := by
  unfold ambFast ambiguityRank restrictedRank sparseRank
  rw [rankB_eq, rankB_eq, rankB_eq, restricted_bits rows he, restricted_bits rows (compl_lt he),
    maskSet_compl]
  have h3 : (rowsBits rows).map (toRow (n + n)) = decodedRows rows := by
    unfold rowsBits decodedRows
    rw [List.map_map]
    apply List.map_congr_left
    intro row _
    simp only [Function.comp, cacheRow_eq]
    exact toRow_rowBits row
  rw [h3]

/-! ## Enumeration of erased sets by bitmasks -/

theorem maskSet_inj {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : maskSet n a = maskSet n b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := congrArg (fun s => (⟨i, hi⟩ : Fin n) ∈ s) h
    simp only [mem_maskSet, eq_iff_iff] at this
    exact Bool.eq_iff_iff.mpr this
  · have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]

theorem sum_range_maskSet {M : Type*} [AddCommMonoid M] (F : Finset (Fin n) → M) :
    ∑ e ∈ range (2 ^ n), F (maskSet n e) = ∑ E : Finset (Fin n), F E := by
  have hinj : ∀ a ha b hb, (fun e (_ : e ∈ range (2 ^ n)) => maskSet n e) a ha =
      (fun e (_ : e ∈ range (2 ^ n)) => maskSet n e) b hb → a = b :=
    fun a ha b hb h => maskSet_inj (mem_range.mp ha) (mem_range.mp hb) h
  refine Finset.sum_bij (fun e _ => maskSet n e) (fun _ _ => mem_univ _) hinj ?_ (fun _ _ => rfl)
  intro E hE
  obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le (s := range (2 ^ n))
    (t := (univ : Finset (Finset (Fin n)))) (fun e _ => maskSet n e) (fun _ _ => mem_univ _)
    (fun a b ha hb h => hinj a ha b hb h)
    (by simp [Finset.card_univ, Fintype.card_finset]) E hE
  exact ⟨a, ha, h.symm⟩

/-! ## The accumulator loop -/

/-- Processes `e, e+1, …, e+k-1`; `info` is evaluated once per `e`, then every entry `i` of the
accumulator is increased by `contrib (info e) i`. Tail recursive. -/
def accLoop (info : ℕ → ℕ × ℕ) (contrib : ℕ × ℕ → ℕ → ℕ) : ℕ → ℕ → Array ℕ → Array ℕ
  | _, 0, acc => acc
  | e, k + 1, acc =>
    match info e with
    | (j, d) => accLoop info contrib (e + 1) k (acc.mapIdx (fun i v => v + contrib (j, d) i))

theorem accLoop_get (info : ℕ → ℕ × ℕ) (contrib : ℕ × ℕ → ℕ → ℕ) :
    ∀ (k e : ℕ) (acc : Array ℕ) (i : ℕ),
      (accLoop info contrib e k acc)[i]? =
        acc[i]?.map (· + ∑ t ∈ range k, contrib (info (e + t)) i)
  | 0, e, acc, i => by
    simp [accLoop]
  | k + 1, e, acc, i => by
    have hrec := accLoop_get info contrib k (e + 1)
    rcases hinfo : info e with ⟨j, d⟩
    simp only [accLoop, hinfo, hrec, Array.getElem?_mapIdx, Option.map_map]
    congr 1
    funext v
    simp only [Function.comp, Finset.sum_range_succ', add_zero, hinfo]
    have : ∀ t, e + 1 + t = e + (t + 1) := fun t => by omega
    simp only [this]
    ring

/-! ## The table -/

/-- Contribution of one erased set with `(|E|, d_E) = jd` to the accumulator: index `|E|`
receives `2^{2n - d_E}`, index `n + 1 + |E|` receives `[d_E > 0]`. -/
def contribFn (n : ℕ) (jd : ℕ × ℕ) (i : ℕ) : ℕ :=
  if i = jd.1 then 2 ^ (2 * n - jd.2) else if i = n + 1 + jd.1 then (if 0 < jd.2 then 1 else 0)
  else 0

/-- One pass over all `2^n` erased sets. -/
def exactAcc (rows : List (List (PauliCoord n))) : Array ℕ :=
  let rb := rowsBits rows
  let s := rankB (n + n) rb
  accLoop (fun e => ((maskSet n e).card, ambFast n rb s e)) (contribFn n) 0 (2 ^ n)
    (Array.replicate (2 * (n + 1)) 0)

/-- `Σ_{|E|=j} 2^{2n - d_E}` (fast). -/
def scoreNat (rows : List (List (PauliCoord n))) (j : ℕ) : ℕ := ((exactAcc rows)[j]?).getD 0

/-- `#{|E| = j : d_E > 0}` (fast). -/
def uncNat (rows : List (List (PauliCoord n))) (j : ℕ) : ℕ :=
  ((exactAcc rows)[n + 1 + j]?).getD 0

/-- Specification: `Σ_{|E|=j} (1/2)^{d_E}` over `Finset.univ`. -/
def layerScoreSum (rows : List (List (PauliCoord n))) (j : ℕ) : ℚ :=
  ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j), (1 / 2 : ℚ) ^ ambiguityRank rows E

/-- Specification: number of uncorrectable erased sets of size `j`. -/
def layerUncCount (rows : List (List (PauliCoord n))) (j : ℕ) : ℕ :=
  (univ.filter (fun E : Finset (Fin n) => E.card = j ∧ 0 < ambiguityRank rows E)).card

theorem exactAcc_get (rows : List (List (PauliCoord n))) {i : ℕ} (hi : i < 2 * (n + 1)) :
    (exactAcc rows)[i]?.getD 0 = ∑ E : Finset (Fin n),
      contribFn n (E.card, ambiguityRank rows E) i := by
  unfold exactAcc
  rw [accLoop_get, Array.getElem?_replicate, if_pos (by simpa using hi)]
  simp only [Option.map_some, Option.getD_some, zero_add]
  rw [← sum_range_maskSet (fun E => contribFn n (E.card, ambiguityRank rows E) i)]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [ambFast_eq rows (by simpa using he)]

theorem scoreNat_eq (rows : List (List (PauliCoord n))) {j : ℕ} (hj : j ≤ n) :
    scoreNat rows j = ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j),
      2 ^ (2 * n - ambiguityRank rows E) := by
  unfold scoreNat
  rw [exactAcc_get rows (by omega), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  unfold contribFn
  by_cases h : E.card = j
  · simp [h]
  · have h1 : ¬ j = E.card := fun h' => h h'.symm
    have h2 : ¬ j = n + 1 + E.card := by omega
    simp [h, h1, h2]

theorem uncNat_eq (rows : List (List (PauliCoord n))) {j : ℕ} (hj : j ≤ n) :
    uncNat rows j = layerUncCount rows j := by
  unfold uncNat layerUncCount
  rw [exactAcc_get rows (by omega), Finset.card_filter]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  unfold contribFn
  dsimp only
  have hE : E.card ≤ n := by simpa using E.card_le_univ
  have h1 : ¬ n + 1 + j = E.card := by omega
  rw [if_neg h1]
  by_cases h : E.card = j
  · rw [if_pos (by omega : n + 1 + j = n + 1 + E.card)]
    by_cases hd : 0 < ambiguityRank rows E <;> simp [h, hd]
  · rw [if_neg (by omega : ¬ n + 1 + j = n + 1 + E.card)]
    simp [h]

theorem ambiguityRank_le (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    ambiguityRank rows E ≤ 2 * n := by
  have hE : E.card ≤ n := by simpa using E.card_le_univ
  unfold ambiguityRank
  omega

/-- **Fast = slow (score).** -/
theorem scoreNat_eq_slow (rows : List (List (PauliCoord n))) {j : ℕ} (hj : j ≤ n) :
    (scoreNat rows j : ℚ) / 2 ^ (2 * n) = layerScoreSum rows j := by
  rw [scoreNat_eq rows hj, layerScoreSum, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  have hle := ambiguityRank_le rows E
  have hpow : (2 : ℚ) ^ (2 * n) = 2 ^ (2 * n - ambiguityRank rows E) * 2 ^ ambiguityRank rows E := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hpow, Nat.cast_pow, Nat.cast_ofNat, one_div_pow]
  field_simp

/-- **Fast = slow (count).** -/
theorem uncNat_eq_slow (rows : List (List (PauliCoord n))) {j : ℕ} (hj : j ≤ n) :
    uncNat rows j = layerUncCount rows j := uncNat_eq rows hj

/-- **Specification (score), for arbitrary rows.** -/
theorem layerScoreSum_spec (rows : List (List (PauliCoord n))) (j : ℕ) :
    (layerScoreSum rows j : ℝ) =
      ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j), erasureScore (rowSpace rows) E := by
  rw [layerScoreSum, Rat.cast_sum]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  rw [EnumeratorExample.erasureScore_eq_rank]
  push_cast
  rw [one_div_pow, one_div]

/-- **Specification (count), for arbitrary rows.** -/
theorem layerUncCount_spec (rows : List (List (PauliCoord n))) (j : ℕ) :
    (layerUncCount rows j : ℝ) = ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j),
      Uncorrectable.uncorrectable (rowSpace rows) E := by
  unfold layerUncCount
  rw [← Finset.filter_filter, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  unfold Uncorrectable.uncorrectable
  rw [EnumeratorExample.ambiguity_eq_rank]
  split_ifs <;> simp

/-! ## The printed fractions -/

/-- Printed `f_j`: the average of `2^{-d_E}` over `|E| = j`. -/
def fRat (rows : List (List (PauliCoord n))) (j : ℕ) : ℚ :=
  (scoreNat rows j : ℚ) / (2 ^ (2 * n) * (n.choose j : ℚ))

/-- Printed `u_j`: the fraction of uncorrectable erased sets of size `j`. -/
def uRat (rows : List (List (PauliCoord n))) (j : ℕ) : ℚ :=
  (uncNat rows j : ℚ) / (n.choose j : ℚ)

/-- **`f_j` is the Bernstein fidelity coefficient** `layerAverage id (erasureScore S) j`. -/
theorem fRat_spec (rows : List (List (PauliCoord n))) (j : Fin (n + 1)) :
    (fRat rows j.val : ℝ) =
      layerAverage (id : Causes n → Finset (Fin n)) (erasureScore (rowSpace rows)) j := by
  rw [Uncorrectable.layerAverage_id_eq, ← layerScoreSum_spec,
    ← scoreNat_eq_slow rows (Nat.lt_succ_iff.mp j.isLt), fRat]
  push_cast
  rw [div_div]

/-- **`u_j` is the layer fraction of uncorrectable sets** `layerFraction S j`. -/
theorem uRat_spec (rows : List (List (PauliCoord n))) (j : Fin (n + 1)) :
    (uRat rows j.val : ℝ) = Uncorrectable.layerFraction (rowSpace rows) j := by
  rw [Uncorrectable.layerFraction, Uncorrectable.layerAverage_id_eq, ← layerUncCount_spec,
    ← uncNat_eq_slow rows (Nat.lt_succ_iff.mp j.isLt), uRat]
  push_cast
  rfl

/-- Read `f_j` off a computed accumulator (so that one enumeration serves all `j`). -/
def fOfAcc (n : ℕ) (acc : Array ℕ) (j : ℕ) : ℚ :=
  ((acc[j]?).getD 0 : ℚ) / (2 ^ (2 * n) * (n.choose j : ℚ))

def uOfAcc (n : ℕ) (acc : Array ℕ) (j : ℕ) : ℚ := ((acc[n + 1 + j]?).getD 0 : ℚ) / (n.choose j : ℚ)

theorem fRat_eq_ofAcc (rows : List (List (PauliCoord n))) (j : ℕ) :
    fRat rows j = fOfAcc n (exactAcc rows) j := rfl

theorem uRat_eq_ofAcc (rows : List (List (PauliCoord n))) (j : ℕ) :
    uRat rows j = uOfAcc n (exactAcc rows) j := rfl

/-- Sanity check on the three-qubit repetition code (kernel evaluation of the fast path). -/
example : uncNat EnumeratorExample.rowsR 1 = 3 ∧ scoreNat EnumeratorExample.rowsR 1 = 96 := by
  decide +kernel

end QecPhysical.Stabilizer.ExactTable

#print axioms QecPhysical.Stabilizer.ExactTable.rankB_eq
#print axioms QecPhysical.Stabilizer.ExactTable.ambFast_eq
#print axioms QecPhysical.Stabilizer.ExactTable.sum_range_maskSet
#print axioms QecPhysical.Stabilizer.ExactTable.accLoop_get
#print axioms QecPhysical.Stabilizer.ExactTable.scoreNat_eq_slow
#print axioms QecPhysical.Stabilizer.ExactTable.uncNat_eq_slow
#print axioms QecPhysical.Stabilizer.ExactTable.layerScoreSum_spec
#print axioms QecPhysical.Stabilizer.ExactTable.layerUncCount_spec
#print axioms QecPhysical.Stabilizer.ExactTable.fRat_spec
#print axioms QecPhysical.Stabilizer.ExactTable.uRat_spec
