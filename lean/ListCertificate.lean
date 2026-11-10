import CompletenessFormula
import HybridSymmetry

set_option autoImplicit false

/-!
# A verified combiner for list certificates

Computable checks with soundness theorems, combined with `certFormula_unsat`:

1. `isotropyB rows` ⇒ the rows span an isotropic space (`isotropyB_sound`).
2. Uncorrectability: `certOK rows M x z` checks a certificate `x ∈ N ∩ supported M`,
   `z ∈ N`, `⟪x, z⟫ = 1` (sparse vectors), hence `0 < ambiguity` (`certOK_sound`);
   `uncorrectableB` decides it through a fast verified rank (`rankL`, proved equal to the
   verified `BinaryElimination.rank`), `ambRankL_eq`.
3. Symmetry: `preservesB rows p` (injective, every permuted row in the row space by a rank
   test) ⇒ `permuteSub (toPerm p) (rowSpace rows) = rowSpace rows`; the whole generated group
   preserves the code (`group_preserves`); `closedB` (with an image-index table) ⇒ the list is
   closed under the generated group (`group_closed`); `repsB` (orbit words) ⇒ the
   representatives meet every orbit (`repsB_sound`).
4. Case splits: `coversB` ⇒ every set satisfies some leaf (`coversB_sound`).
5. `complete_symmetric`, `complete_plain`: from the checks and the unsatisfiability of the
   leaf formulas, every uncorrectable set of size `≤ L` contains a listed set.
6. `distance_of_complete`, `layer_exact`, `leading_layer_sum`: the distance, the exact list of
   minimum-size uncorrectable sets, and the exact leading layer sum by exponent counts.
-/

namespace QecPhysical.Stabilizer.ListCertificate

open Std.Sat
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecReliability.BinaryElimination
open QecPhysical.Stabilizer QecPhysical.Stabilizer.Uncorrectable
open QecPhysical.Stabilizer.Completeness

/-! ## 0. A fast verified rank -/

def enc (m : ℕ) (x : Row m) : List Bool := List.ofFn (fun i => bb (x i))

def xorL (a b : List Bool) : List Bool := List.zipWith (· ^^ ·) a b

/-- Gaussian elimination on rows stored as lists of booleans; same recursion as `rank`. -/
def rankL : ℕ → List (List Bool) → ℕ
  | 0, _ => 0
  | m + 1, rows =>
    match rows.find? (fun x => x.headD false) with
    | none => rankL m (rows.map List.tail)
    | some p => rankL m (rows.map (fun x => if x.headD false then xorL x.tail p.tail else x.tail)) + 1

theorem enc_succ {m : ℕ} (x : Row (m + 1)) : enc (m + 1) x = bb (x 0) :: enc m (tailMap m x) := by
  simp [enc, List.ofFn_succ, tailMap]

theorem enc_add {m : ℕ} (x y : Row m) : enc m (x + y) = xorL (enc m x) (enc m y) := by
  induction m with
  | zero => simp [enc, xorL]
  | succ m ih =>
    rw [enc_succ, enc_succ, enc_succ, map_add, ih]
    simp [xorL, bb_add]

theorem bb_eq_decide (b : Bit) : bb b = decide (b ≠ 0) := by revert b; decide

theorem enc_clearTail {m : ℕ} (p x : Row (m + 1)) (hp : p 0 ≠ 0) :
    enc m (clearTail p x) =
      if bb (x 0) then xorL (enc m (tailMap m x)) (enc m (tailMap m p)) else enc m (tailMap m x) := by
  have hp1 : p 0 = 1 := by revert hp; generalize p 0 = b; revert b; decide
  have hx : x 0 = 0 ∨ x 0 = 1 := by generalize x 0 = b; revert b; decide
  rcases hx with hx | hx
  · have : clearTail p x = tailMap m x := by
      funext i; simp [clearTail, tailMap, hx]
    rw [this, hx]; simp
  · have : clearTail p x = tailMap m x + tailMap m p := by
      funext i
      simp only [clearTail, tailMap, LinearMap.coe_mk, AddHom.coe_mk, hx, one_mul, Pi.add_apply]
      generalize x i.succ = a; generalize p i.succ = b; revert a b; decide
    rw [this, enc_add, hx]; simp

theorem rank_eq_rankL : ∀ (m : ℕ) (rows : List (Row m)), rank m rows = rankL m (rows.map (enc m))
  | 0, _ => by simp [rank, rankL]
  | m + 1, rows => by
    have hpred : ((fun x : List Bool => x.headD false) ∘ enc (m + 1)) =
        fun x : Row (m + 1) => decide (x 0 ≠ 0) := by
      funext x; simp [enc_succ, bb_eq_decide]
    rw [rank, rankL, List.find?_map, hpred]
    cases hf : rows.find? (fun x => decide (x 0 ≠ 0)) with
    | none =>
      simp only [Option.map_none]
      rw [rank_eq_rankL m]
      congr 1
      simp [List.map_map, Function.comp_def, enc_succ]
    | some p =>
      have hp : p 0 ≠ 0 := by simpa using List.find?_some hf
      simp only [Option.map_some]
      rw [rank_eq_rankL m]
      congr 2
      simp only [List.map_map, Function.comp_def, cacheRow_eq, enc_succ, List.headD_cons,
        List.tail_cons]
      congr 1
      funext x
      rw [enc_clearTail p x hp]

/-- Dense encoding of a sparse row restricted by `memb`: coordinate `i < n` is
`memb i && odd (count of .inl i)`, coordinate `n + i` is `memb i && odd (count of .inr i)`. -/
def encS {n : ℕ} (memb : Fin n → Bool) (row : List (PauliCoord n)) : List Bool :=
  List.ofFn (fun c : Fin (n + n) => Fin.addCases (motive := fun _ => Bool)
    (fun i => memb i && (row.countP (fun c => decide (c = Sum.inl i)) % 2 == 1))
    (fun i => memb i && (row.countP (fun c => decide (c = Sum.inr i)) % 2 == 1)) c)

theorem bb_natCast (k : ℕ) : bb (k : Bit) = (k % 2 == 1) := by
  rw [← ZMod.natCast_mod k 2]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> decide

theorem decodeRow_fst_count {n : ℕ} (row : List (PauliCoord n)) (i : Fin n) :
    (decodeRow row).1 i = ((row.countP (fun c => decide (c = Sum.inl i)) : ℕ) : Bit) := by
  induction row with
  | nil => simp [decodeRow]
  | cons c row ih =>
    have hd : decodeRow (c :: row) = coordPauli c + decodeRow row := by simp [decodeRow]
    rw [hd, Prod.fst_add, Pi.add_apply, ih, List.countP_cons]
    push_cast
    cases c with
    | inl j =>
      by_cases h : j = i
      · subst h; simp [coordPauli, xUnit]; ring
      · simp [coordPauli, xUnit, Pi.single_apply, Ne.symm h, h]
    | inr j => simp [coordPauli, zUnit]

theorem decodeRow_snd_count {n : ℕ} (row : List (PauliCoord n)) (i : Fin n) :
    (decodeRow row).2 i = ((row.countP (fun c => decide (c = Sum.inr i)) : ℕ) : Bit) := by
  induction row with
  | nil => simp [decodeRow]
  | cons c row ih =>
    have hd : decodeRow (c :: row) = coordPauli c + decodeRow row := by simp [decodeRow]
    rw [hd, Prod.snd_add, Pi.add_apply, ih, List.countP_cons]
    push_cast
    cases c with
    | inl j => simp [coordPauli, xUnit]
    | inr j =>
      by_cases h : j = i
      · subst h; simp [coordPauli, zUnit]; ring
      · simp [coordPauli, zUnit, Pi.single_apply, Ne.symm h, h]

theorem flatten_left {n : ℕ} (x : Pauli n) (i : Fin n) : flatten n x (Fin.castAdd n i) = x.1 i := by
  change Fin.addCases x.1 x.2 (Fin.castAdd n i) = x.1 i
  exact Fin.addCases_left i
theorem flatten_right {n : ℕ} (x : Pauli n) (i : Fin n) : flatten n x (Fin.natAdd n i) = x.2 i := by
  change Fin.addCases x.1 x.2 (Fin.natAdd n i) = x.2 i
  exact Fin.addCases_right i

theorem encS_eq {n : ℕ} (E : Finset (Fin n)) (memb : Fin n → Bool)
    (hm : ∀ i, memb i = decide (i ∈ E)) (row : List (PauliCoord n)) :
    encS memb row = enc (n + n) (cacheRow (flatten n (mask n E (decodeRow row)))) := by
  unfold enc encS
  congr 1
  funext c
  rw [cacheRow_eq]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) c
  · rw [Fin.addCases_left, flatten_left]
    by_cases h : i ∈ E
    · simp [mask, h, hm, decodeRow_fst_count, bb_natCast]
    · simp [mask, h, hm]
  · rw [Fin.addCases_right, flatten_right]
    by_cases h : i ∈ E
    · simp [mask, h, hm, decodeRow_snd_count, bb_natCast]
    · simp [mask, h, hm]

theorem mask_univ {n : ℕ} (x : Pauli n) : mask n Finset.univ x = x := by
  apply Prod.ext <;> funext i <;> simp [mask]

def sparseRankL {n : ℕ} (rows : List (List (PauliCoord n))) : ℕ :=
  rankL (n + n) (rows.map (encS (fun _ => true)))

def restrictedRankL {n : ℕ} (rows : List (List (PauliCoord n))) (memb : Fin n → Bool) : ℕ :=
  rankL (n + n) (rows.map (encS memb))

/-- The ambiguity exponent through the fast rank (sparse encoding, no dense closures). -/
def ambRankL {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) : ℕ :=
  (2 * E.card - restrictedRankL rows (fun i => decide (i ∈ E))) -
    (sparseRankL rows - restrictedRankL rows (fun i => !decide (i ∈ E)))

theorem sparseRankL_eq_rank {n : ℕ} (rows : List (List (PauliCoord n))) :
    sparseRankL rows = sparseRank rows := by
  rw [sparseRankL, sparseRank, rank_eq_rankL]
  congr 1
  simp only [decodedRows, List.map_map]
  apply List.map_congr_left
  intro row _
  rw [Function.comp_apply, encS_eq Finset.univ _ (fun i => by simp), mask_univ]

theorem restrictedRankL_eq {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n))
    (memb : Fin n → Bool) (hm : ∀ i, memb i = decide (i ∈ E)) :
    restrictedRankL rows memb = restrictedRank rows E := by
  rw [restrictedRankL, restrictedRank, rank_eq_rankL]
  congr 1
  simp only [restrictedRows, List.map_map]
  apply List.map_congr_left
  intro row _
  rw [Function.comp_apply, encS_eq E memb hm]

theorem sparseRankL_eq {n : ℕ} (rows : List (List (PauliCoord n))) :
    sparseRankL rows = Module.finrank Bit (rowSpace rows) := by
  rw [sparseRankL_eq_rank, sparseRank_correct]

theorem ambRankL_eq {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    ambRankL rows E = ambiguity (symplectic n) (rowSpace rows) (supported E) := by
  rw [← ambiguityRank_correct, ambRankL, ambiguityRank, sparseRankL_eq_rank,
    restrictedRankL_eq rows E _ (fun i => rfl),
    restrictedRankL_eq rows Eᶜ _ (fun i => by simp)]

theorem ambRankL_le {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    ambRankL rows E ≤ 2 * n := by
  have := E.card_le_univ
  simp only [Fintype.card_fin] at this
  unfold ambRankL; omega

/-- **Check 2 (rank form).** -/
def uncorrectableB {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) : Bool :=
  decide (0 < ambRankL rows E)

theorem uncorrectableB_iff {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    uncorrectableB rows E = true ↔ 0 < ambiguity (symplectic n) (rowSpace rows) (supported E) := by
  simp [uncorrectableB, ambRankL_eq]

/-! ## 1. Sparse pairings and isotropy -/

def anti {n : ℕ} : PauliCoord n → PauliCoord n → Bit
  | .inl i, .inr j => if i = j then 1 else 0
  | .inr i, .inl j => if i = j then 1 else 0
  | _, _ => 0

/-- `⟪decodeRow r, decodeRow r'⟫` computed on the sparse lists. -/
def pairS {n : ℕ} (r r' : List (PauliCoord n)) : Bit := (r.map fun c => (r'.map (anti c)).sum).sum

theorem decodeRow_fst {n : ℕ} (r : List (PauliCoord n)) (i : Fin n) :
    (decodeRow r).1 i = (r.map fun c => (coordPauli c).1 i).sum := by
  induction r with
  | nil => simp [decodeRow]
  | cons c r ih =>
    have hd : decodeRow (c :: r) = coordPauli c + decodeRow r := by simp [decodeRow]
    rw [hd, Prod.fst_add, Pi.add_apply, ih]; simp

theorem decodeRow_snd {n : ℕ} (r : List (PauliCoord n)) (i : Fin n) :
    (decodeRow r).2 i = (r.map fun c => (coordPauli c).2 i).sum := by
  induction r with
  | nil => simp [decodeRow]
  | cons c r ih =>
    have hd : decodeRow (c :: r) = coordPauli c + decodeRow r := by simp [decodeRow]
    rw [hd, Prod.snd_add, Pi.add_apply, ih]; simp

theorem pairS_eq {n : ℕ} (r r' : List (PauliCoord n)) :
    pairS r r' = symplectic n (decodeRow r) (decodeRow r') := by
  rw [symplectic_decodeRow, pairS]
  congr 1
  apply List.map_congr_left
  intro c _
  cases c with
  | inl i =>
    simp only [Sum.elim_inl, decodeRow_snd]
    congr 1
    apply List.map_congr_left
    intro c' _
    cases c' with
    | inl j => simp [anti, coordPauli, xUnit]
    | inr j => simp [anti, coordPauli, zUnit, Pi.single_apply, eq_comm]
  | inr i =>
    simp only [Sum.elim_inr, decodeRow_fst]
    congr 1
    apply List.map_congr_left
    intro c' _
    cases c' with
    | inl j => simp [anti, coordPauli, xUnit, Pi.single_apply, eq_comm]
    | inr j => simp [anti, coordPauli, zUnit]

/-- `decodeRow v ∈ N(rowSpace rows)`. -/
def memNormB {n : ℕ} (rows : List (List (PauliCoord n))) (v : List (PauliCoord n)) : Bool :=
  rows.all fun r => decide (pairS r v = 0)

theorem memNormB_sound {n : ℕ} (rows : List (List (PauliCoord n))) (v : List (PauliCoord n))
    (h : memNormB rows v = true) :
    decodeRow v ∈ normalizer (symplectic n) (rowSpace rows) := by
  rw [mem_normalizer_rows]
  intro r hr
  have := List.all_eq_true.mp h r hr
  rw [← pairS_eq]; simpa using this

/-- **Check 1.** -/
def isotropyB {n : ℕ} (rows : List (List (PauliCoord n))) : Bool :=
  rows.all fun r => memNormB rows r

theorem isotropyB_sound {n : ℕ} (rows : List (List (PauliCoord n))) (h : isotropyB rows = true) :
    rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows) := by
  apply Submodule.span_le.2
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  exact memNormB_sound rows r (List.all_eq_true.mp h r hr)

/-! ## 2. Uncorrectability certificates -/

def coordQubit {n : ℕ} : PauliCoord n → Fin n
  | .inl i => i
  | .inr i => i

/-- `x` is supported on `M`, `x, z ∈ N`, `⟪x, z⟫ = 1`. -/
def certOK {n : ℕ} (rows : List (List (PauliCoord n))) (M : List (Fin n))
    (x z : List (PauliCoord n)) : Bool :=
  x.all (fun c => decide (coordQubit c ∈ M)) && memNormB rows x && memNormB rows z &&
    decide (pairS x z = 1)

theorem decodeRow_supported {n : ℕ} (M : List (Fin n)) (x : List (PauliCoord n))
    (h : ∀ c ∈ x, coordQubit c ∈ M) : decodeRow x ∈ supported M.toFinset := by
  intro i hi
  have hiM : i ∉ M := by simpa using hi
  rw [decodeRow_fst, decodeRow_snd]
  constructor
  · apply List.sum_eq_zero
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    have := h c hc
    cases c with
    | inl j =>
      have hj : j ≠ i := fun e => hiM (e ▸ this)
      simp [coordPauli, xUnit, Pi.single_apply, Ne.symm hj]
    | inr j => simp [coordPauli, zUnit]
  · apply List.sum_eq_zero
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    have := h c hc
    cases c with
    | inl j => simp [coordPauli, xUnit]
    | inr j =>
      have hj : j ≠ i := fun e => hiM (e ▸ this)
      simp [coordPauli, zUnit, Pi.single_apply, Ne.symm hj]

theorem certOK_sound {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (M : List (Fin n))
    (x z : List (PauliCoord n)) (h : certOK rows M x z = true) :
    0 < ambiguity (symplectic n) (rowSpace rows) (supported M.toFinset) := by
  simp only [certOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hsupp, hx⟩, hz⟩, hxz⟩ := h
  rw [pairS_eq] at hxz
  exact (uncorrectable_iff_certificate (rowSpace rows) hS _).mpr
    ⟨decodeRow x, ⟨memNormB_sound rows x hx, decodeRow_supported M x hsupp⟩,
      decodeRow z, memNormB_sound rows z hz, hxz⟩

/-- All listed sets pass their certificates (arrays aligned by index). -/
def allCertOK {n : ℕ} (rows : List (List (PauliCoord n))) (mins : Array (List (Fin n)))
    (xs zs : Array (List (PauliCoord n))) : Bool :=
  (List.range mins.size).all fun k =>
    match mins[k]?, xs[k]?, zs[k]? with
    | some M, some x, some z => certOK rows M x z
    | _, _, _ => false

theorem array_mem_get {α : Type} {a : Array α} {x : α} (h : x ∈ a.toList) :
    ∃ k, k < a.size ∧ a[k]? = some x := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  refine ⟨k, by simpa using hk, ?_⟩
  simp

theorem allCertOK_sound {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (mins : Array (List (Fin n)))
    (xs zs : Array (List (PauliCoord n))) (h : allCertOK rows mins xs zs = true) :
    ∀ M ∈ mins.toList, 0 < ambiguity (symplectic n) (rowSpace rows) (supported M.toFinset) := by
  intro M hM
  obtain ⟨k, hk, hMk⟩ := array_mem_get hM
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  rw [hMk] at this
  cases hx : xs[k]? <;> cases hz : zs[k]? <;> simp only [hx, hz] at this
  · exact absurd this (by simp)
  · exact absurd this (by simp)
  · exact absurd this (by simp)
  · exact certOK_sound rows hS M _ _ this

/-- Certificates with shared `z` vectors: `logs` are checked to lie in `N` once; set `k` uses
`x = xs[k]` and `z = logs[zi[k]]`. -/
def allCertOK2 {n : ℕ} (rows : List (List (PauliCoord n))) (mins : Array (List (Fin n)))
    (xs : Array (List (PauliCoord n))) (zi : Array ℕ) (logs : Array (List (PauliCoord n))) : Bool :=
  logs.toList.all (memNormB rows) && (List.range mins.size).all fun k =>
    match mins[k]?, xs[k]?, zi[k]? with
    | some M, some x, some j =>
      match logs[j]? with
      | some z => x.all (fun c => decide (coordQubit c ∈ M)) && memNormB rows x &&
          decide (pairS x z = 1)
      | none => false
    | _, _, _ => false

theorem allCertOK2_sound {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (mins : Array (List (Fin n)))
    (xs : Array (List (PauliCoord n))) (zi : Array ℕ) (logs : Array (List (PauliCoord n)))
    (h : allCertOK2 rows mins xs zi logs = true) :
    ∀ M ∈ mins.toList, 0 < ambiguity (symplectic n) (rowSpace rows) (supported M.toFinset) := by
  simp only [allCertOK2, Bool.and_eq_true] at h
  obtain ⟨hlogs, hsets⟩ := h
  intro M hM
  obtain ⟨k, hk, hMk⟩ := array_mem_get hM
  have := List.all_eq_true.mp hsets k (List.mem_range.mpr hk)
  rw [hMk] at this
  cases hx : xs[k]? with
  | none => simp [hx] at this
  | some x =>
    cases hj : zi[k]? with
    | none => simp [hx, hj] at this
    | some j =>
      simp only [hx, hj] at this
      cases hz : logs[j]? with
      | none => simp [hz] at this
      | some z =>
        simp only [hz] at this
        have hzmem : z ∈ logs.toList := by
          rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hz
        have hzN := List.all_eq_true.mp hlogs z hzmem
        apply certOK_sound rows hS M x z
        simp only [certOK, Bool.and_eq_true] at this ⊢
        exact ⟨⟨this.1, hzN⟩, this.2⟩

/-- Rank form of check 2 for a whole list. -/
def allUncB {n : ℕ} (rows : List (List (PauliCoord n))) (mins : List (List (Fin n))) : Bool :=
  mins.all fun M => uncorrectableB rows M.toFinset

/-- Check 2: certificates, or else the rank test. -/
def uncCheckB {n : ℕ} (rows : List (List (PauliCoord n))) (mins : Array (List (Fin n)))
    (xs : Array (List (PauliCoord n))) (zi : Array ℕ) (logs : Array (List (PauliCoord n))) : Bool :=
  allCertOK2 rows mins xs zi logs || allUncB rows mins.toList

theorem uncCheckB_sound {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (mins : Array (List (Fin n)))
    (xs : Array (List (PauliCoord n))) (zi : Array ℕ) (logs : Array (List (PauliCoord n)))
    (h : uncCheckB rows mins xs zi logs = true) :
    ∀ M ∈ mins.toList, 0 < ambiguity (symplectic n) (rowSpace rows) (supported M.toFinset) := by
  simp only [uncCheckB, Bool.or_eq_true] at h
  rcases h with h | h
  · exact allCertOK2_sound rows hS mins xs zi logs h
  · intro M hM
    exact (uncorrectableB_iff rows _).mp (List.all_eq_true.mp h M hM)

/-! ## 3. Symmetry -/

def injB {n : ℕ} (p : Fin n → Fin n) : Bool := decide (∀ i j, p i = p j → i = j)

theorem injB_sound {n : ℕ} {p : Fin n → Fin n} (h : injB p = true) : Function.Injective p := by
  intro i j hij
  have := of_decide_eq_true h
  exact this i j hij

noncomputable def toPerm {n : ℕ} (p : Fin n → Fin n) : Equiv.Perm (Fin n) :=
  if h : Function.Injective p then Equiv.ofBijective p (Finite.injective_iff_bijective.mp h) else 1

theorem toPerm_apply {n : ℕ} {p : Fin n → Fin n} (h : Function.Injective p) (i : Fin n) :
    toPerm p i = p i := by
  simp [toPerm, h]

def permRow {n : ℕ} (p : Fin n → Fin n) (r : List (PauliCoord n)) : List (PauliCoord n) :=
  r.map (Sum.map p p)

theorem permute_coordPauli {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : PauliCoord n) :
    permute σ (coordPauli c) = coordPauli (Sum.map σ σ c) := by
  cases c with
  | inl i =>
    apply Prod.ext <;> funext j
    · simp [coordPauli, xUnit, Pi.single_apply, Equiv.symm_apply_eq]
    · simp [coordPauli, xUnit]
  | inr i =>
    apply Prod.ext <;> funext j
    · simp [coordPauli, zUnit]
    · simp [coordPauli, zUnit, Pi.single_apply, Equiv.symm_apply_eq]

theorem permute_decodeRow {n : ℕ} (σ : Equiv.Perm (Fin n)) (r : List (PauliCoord n)) :
    permute σ (decodeRow r) = decodeRow (permRow σ r) := by
  induction r with
  | nil => simp [decodeRow, permRow]
  | cons c r ih =>
    have hd : ∀ (c : PauliCoord n) (r : List (PauliCoord n)),
        decodeRow (c :: r) = coordPauli c + decodeRow r := by intro c r; simp [decodeRow]
    simp only [permRow, List.map_cons] at ih ⊢
    rw [hd, hd, map_add, ih, permute_coordPauli]

/-- **Check 3a.** `p` is a permutation and maps every row into the row space (rank test). -/
def preservesB {n : ℕ} (rows : List (List (PauliCoord n))) (p : Fin n → Fin n) : Bool :=
  injB p && rows.all fun r => sparseRankL (rows ++ [permRow p r]) == sparseRankL rows

theorem rowSpace_le_append {n : ℕ} (rows extra : List (List (PauliCoord n))) :
    rowSpace rows ≤ rowSpace (rows ++ extra) := by
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_setOf_eq, List.map_append, List.mem_append] at hx ⊢
  exact Or.inl hx

theorem mem_of_rank_eq {n : ℕ} (rows : List (List (PauliCoord n))) (r : List (PauliCoord n))
    (h : sparseRankL (rows ++ [r]) = sparseRankL rows) : decodeRow r ∈ rowSpace rows := by
  rw [sparseRankL_eq, sparseRankL_eq] at h
  have heq := Submodule.eq_of_le_of_finrank_eq (rowSpace_le_append rows [r]) h.symm
  rw [heq]
  apply Submodule.subset_span
  simp

theorem preservesB_sound {n : ℕ} (rows : List (List (PauliCoord n))) (p : Fin n → Fin n)
    (h : preservesB rows p = true) :
    permuteSub (toPerm p) (rowSpace rows) = rowSpace rows := by
  simp only [preservesB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hinj, hrows⟩ := h
  have hp := injB_sound hinj
  have hmap : (Sum.map (toPerm p) (toPerm p) : PauliCoord n → PauliCoord n) = Sum.map p p := by
    funext c; cases c <;> simp [toPerm_apply hp]
  have hle : permuteSub (toPerm p) (rowSpace rows) ≤ rowSpace rows := by
    unfold permuteSub rowSpace
    rw [Submodule.map_span]
    apply Submodule.span_le.2
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    change permute (toPerm p) (decodeRow r) ∈ rowSpace rows
    rw [permute_decodeRow]
    have : permRow (toPerm p) r = permRow p r := by simp [permRow, hmap]
    rw [this]
    exact mem_of_rank_eq rows _ (hrows r hr)
  exact Submodule.eq_of_le_of_finrank_eq hle (finrank_permuteSub _ _)

/-- The group generated by the generators. -/
noncomputable def genGroup {n : ℕ} (gens : Array (Fin n → Fin n)) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {τ | ∃ p ∈ gens.toList, τ = toPerm p}

theorem permuteSub_mul {n : ℕ} (a b : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n)) :
    permuteSub (a * b) S = permuteSub a (permuteSub b S) := by
  ext z
  rw [mem_permuteSub, mem_permuteSub, mem_permuteSub]
  rfl

theorem permuteSub_one {n : ℕ} (S : Submodule Bit (Pauli n)) : permuteSub 1 S = S := by
  unfold permuteSub
  have : ((permute (1 : Equiv.Perm (Fin n)) : Pauli n ≃ₗ[Bit] Pauli n) : Pauli n →ₗ[Bit] Pauli n) =
      LinearMap.id := by
    ext x <;> rfl
  rw [this, Submodule.map_id]

theorem group_preserves {n : ℕ} (rows : List (List (PauliCoord n))) (gens : Array (Fin n → Fin n))
    (h : ∀ p ∈ gens.toList, preservesB rows p = true) :
    ∀ τ ∈ genGroup gens, permuteSub τ (rowSpace rows) = rowSpace rows := by
  intro τ hτ
  induction hτ using Subgroup.closure_induction with
  | mem τ hτ =>
    obtain ⟨p, hp, rfl⟩ := hτ
    exact preservesB_sound rows p (h p hp)
  | one => exact permuteSub_one _
  | mul a b _ _ ha hb => rw [permuteSub_mul, hb, ha]
  | inv a _ ha =>
    calc permuteSub a⁻¹ (rowSpace rows) = permuteSub a⁻¹ (permuteSub a (rowSpace rows)) := by
          rw [ha]
      _ = rowSpace rows := by rw [← permuteSub_mul, inv_mul_cancel, permuteSub_one]

/-- The listed sets as a finset of finsets. -/
def listFin {n : ℕ} (mins : Array (List (Fin n))) : Finset (Finset (Fin n)) :=
  (mins.toList.map List.toFinset).toFinset

/-- **Check 3b.** `img[k]` is the index of the image of `mins[k]` under `p`. -/
def closedB {n : ℕ} (mins : Array (List (Fin n))) (p : Fin n → Fin n) (img : Array ℕ) : Bool :=
  (List.range mins.size).all fun k =>
    match mins[k]?, img[k]? with
    | some M, some j =>
      match mins[j]? with
      | some M' => decide ((M.map p).toFinset = M'.toFinset)
      | none => false
    | _, _ => false

theorem closedB_sound {n : ℕ} (mins : Array (List (Fin n))) (p : Fin n → Fin n) (img : Array ℕ)
    (hp : Function.Injective p) (h : closedB mins p img = true) :
    ∀ A ∈ listFin mins, A.map (toPerm p).toEmbedding ∈ listFin mins := by
  intro A hA
  simp only [listFin, List.mem_toFinset, List.mem_map] at hA
  obtain ⟨M, hM, rfl⟩ := hA
  obtain ⟨k, hk, hMk⟩ := array_mem_get hM
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  rw [hMk] at this
  cases hj : img[k]? with
  | none => simp [hj] at this
  | some j =>
    simp only [hj] at this
    cases hM' : mins[j]? with
    | none => simp [hM'] at this
    | some M' =>
      simp only [hM', decide_eq_true_eq] at this
      have himg : M.toFinset.map (toPerm p).toEmbedding = (M.map p).toFinset := by
        ext a
        simp only [Finset.mem_map, List.mem_toFinset, Equiv.coe_toEmbedding, List.mem_map,
          toPerm_apply hp]
      rw [himg, this]
      simp only [listFin, List.mem_toFinset, List.mem_map]
      refine ⟨M', ?_, rfl⟩
      have hjs : j < mins.size := by
        by_contra hc
        rw [Array.getElem?_eq_none (by omega)] at hM'
        exact absurd hM' (by simp)
      rw [Array.getElem?_eq_getElem hjs] at hM'
      cases hM'
      simp

theorem group_closed {n : ℕ} (mins : Array (List (Fin n))) (gens : Array (Fin n → Fin n))
    (h : ∀ p ∈ gens.toList, ∃ img, Function.Injective p ∧ closedB mins p img = true) :
    ∀ τ ∈ genGroup gens, ∀ A ∈ listFin mins, A.map τ.toEmbedding ∈ listFin mins := by
  intro τ hτ
  induction hτ using Subgroup.closure_induction with
  | mem τ hτ =>
    obtain ⟨p, hp, rfl⟩ := hτ
    obtain ⟨img, hinj, hc⟩ := h p hp
    exact closedB_sound mins p img hinj hc
  | one =>
    intro A hA
    have : A.map (1 : Equiv.Perm (Fin n)).toEmbedding = A := by ext; simp; rfl
    rw [this]; exact hA
  | mul a b _ _ ha hb =>
    intro A hA
    have := ha _ (hb A hA)
    rwa [Finset.map_map] at this
  | inv a _ ha =>
    intro A hA
    set F := listFin mins
    have hsub : F.image (fun B => B.map a.toEmbedding) ⊆ F := by
      intro B hB
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
      exact ha C hC
    have hcard : F.card ≤ (F.image (fun B => B.map a.toEmbedding)).card := by
      rw [Finset.card_image_of_injective _ (Finset.map_injective _)]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    rw [← heq] at hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    have h2 := map_symm_map a⁻¹ B
    rw [show (a⁻¹ : Equiv.Perm (Fin n)).symm = a from rfl] at h2
    rw [h2]
    exact hB

/-- Apply a word of generator indices (`gens.getD k id`; the rightmost letter acts first). -/
def applyWord {n : ℕ} (gens : Array (Fin n → Fin n)) (w : List ℕ) (i : Fin n) : Fin n :=
  w.foldr (fun k j => (gens.getD k id) j) i

/-- **Check 3c.** For every qubit, its word moves it to a representative. -/
def repsB {n : ℕ} (gens : Array (Fin n → Fin n)) (reps : List (Fin n)) (words : Array (List ℕ)) :
    Bool :=
  (List.finRange n).all fun i => decide (applyWord gens (words.getD i.val []) i ∈ reps)

theorem word_mem {n : ℕ} (gens : Array (Fin n → Fin n)) (hinj : ∀ p ∈ gens.toList, injB p = true)
    (w : List ℕ) :
    ∃ τ ∈ genGroup gens, ∀ i, τ i = applyWord gens w i := by
  induction w with
  | nil => exact ⟨1, Subgroup.one_mem _, fun i => rfl⟩
  | cons k w ih =>
    obtain ⟨τ, hτ, hτi⟩ := ih
    have hk : Function.Injective (gens.getD k id) := by
      by_cases hks : k < gens.size
      · have : gens.getD k id = gens[k] := by simp [Array.getD, hks]
        rw [this]
        exact injB_sound (hinj _ (by simp))
      · have : gens.getD k id = id := by simp [Array.getD, hks]
        rw [this]; exact Function.injective_id
    have hmem : toPerm (gens.getD k id) ∈ genGroup gens := by
      by_cases hks : k < gens.size
      · apply Subgroup.subset_closure
        exact ⟨gens[k], by simp, by simp [Array.getD, hks]⟩
      · have e : gens.getD k id = id := by simp [Array.getD, hks]
        have : toPerm (gens.getD k id) = 1 := by
          rw [e]; ext i; simp [toPerm_apply Function.injective_id]
        rw [this]; exact Subgroup.one_mem _
    refine ⟨toPerm (gens.getD k id) * τ, Subgroup.mul_mem _ hmem hτ, fun i => ?_⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hτi, toPerm_apply hk, applyWord,
      List.foldr_cons]

theorem repsB_sound {n : ℕ} (gens : Array (Fin n → Fin n)) (hinj : ∀ p ∈ gens.toList, injB p = true)
    (reps : List (Fin n)) (words : Array (List ℕ)) (h : repsB gens reps words = true) :
    ∀ i : Fin n, ∃ τ ∈ genGroup gens, τ i ∈ reps.toFinset := by
  intro i
  obtain ⟨τ, hτ, hτi⟩ := word_mem gens hinj (words.getD i.val [])
  refine ⟨τ, hτ, ?_⟩
  have := List.all_eq_true.mp h i (List.mem_finRange i)
  rw [hτi, List.mem_toFinset]
  simpa using this

/-! ## 4. Case splits -/

/-- `E` satisfies every literal of the cube `c`. -/
def CubeSat {n : ℕ} (E : Finset (Fin n)) (c : List (Fin n × Bool)) : Prop :=
  ∀ u ∈ c, (u.1 ∈ E ↔ u.2 = true)

/-- Cubes compatible with `v = b`, with the literals on `v` removed. -/
def restrictCubes {n : ℕ} (v : Fin n) (b : Bool) (cs : List (List (Fin n × Bool))) :
    List (List (Fin n × Bool)) :=
  cs.filterMap fun c => if c.any (fun u => u.1 == v && u.2 != b) then none
    else some (c.filter (fun u => u.1 != v))

def coversB {n : ℕ} : ℕ → List (List (Fin n × Bool)) → Bool
  | 0, _ => false
  | f + 1, cs =>
    if cs.any List.isEmpty then true else
    match cs with
    | [] => false
    | [] :: _ => true
    | (u :: _) :: _ => coversB f (restrictCubes u.1 true cs) && coversB f (restrictCubes u.1 false cs)

/-- Fuel that suffices for `coversB`: the total number of literals plus one. -/
def coverFuel {n : ℕ} (cs : List (List (Fin n × Bool))) : ℕ := (cs.map List.length).sum + 1

theorem restrictCubes_sat {n : ℕ} (E : Finset (Fin n)) (v : Fin n) (b : Bool)
    (hb : v ∈ E ↔ b = true) (cs : List (List (Fin n × Bool))) :
    (∃ c ∈ restrictCubes v b cs, CubeSat E c) → ∃ c ∈ cs, CubeSat E c := by
  rintro ⟨c', hc', hsat⟩
  simp only [restrictCubes, List.mem_filterMap] at hc'
  obtain ⟨c, hc, hcc⟩ := hc'
  split_ifs at hcc with hany
  simp only [Option.some.injEq] at hcc
  subst hcc
  refine ⟨c, hc, fun u hu => ?_⟩
  by_cases huv : u.1 = v
  · have : ¬ (u.1 == v && u.2 != b) = true := fun h => hany (List.any_eq_true.mpr ⟨u, hu, h⟩)
    simp only [huv, beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq, Decidable.not_not] at this
    rw [huv, this]; exact hb
  · exact hsat u (List.mem_filter.mpr ⟨hu, by simpa using huv⟩)

theorem coversB_sound {n : ℕ} : ∀ (f : ℕ) (cs : List (List (Fin n × Bool))),
    coversB f cs = true → ∀ E : Finset (Fin n), ∃ c ∈ cs, CubeSat E c
  | 0, _, h => by simp [coversB] at h
  | f + 1, cs, h => by
    intro E
    unfold coversB at h
    by_cases he : cs.any List.isEmpty = true
    · obtain ⟨c, hc, hce⟩ := List.any_eq_true.mp he
      refine ⟨c, hc, fun u hu => ?_⟩
      rw [List.isEmpty_iff] at hce
      subst hce; simp at hu
    · rw [if_neg he] at h
      match cs, h with
      | [] :: _, _ => exact ⟨[], by simp, fun u hu => by simp at hu⟩
      | (u :: c) :: cs', h =>
        simp only [Bool.and_eq_true] at h
        by_cases hv : u.1 ∈ E
        · exact restrictCubes_sat E u.1 true (by simp [hv]) _
            (coversB_sound f _ h.1 E)
        · exact restrictCubes_sat E u.1 false (by simp [hv]) _
            (coversB_sound f _ h.2 E)

/-! ## 5. Completeness from the checks -/

/-- Every uncorrectable erased set of size at most `L` contains a listed set. -/
def Complete {n : ℕ} (rows : List (List (PauliCoord n))) (L : ℕ) (mins : List (List (Fin n))) :
    Prop :=
  ∀ E : Finset (Fin n), E.card ≤ L →
    0 < ambiguity (symplectic n) (rowSpace rows) (supported E) → ∃ M ∈ mins, M.toFinset ⊆ E

/-- **Plain combiner** (no symmetry): leaves covering all assignments, each refuted. -/
theorem complete_plain {n : ℕ} (rows : List (List (PauliCoord n))) (L : ℕ)
    (mins : List (List (Fin n))) (leaves : List (List (Fin n × Bool)))
    (hiso : isotropyB rows = true) (hcov : coversB (coverFuel leaves) leaves = true)
    (hunsat : ∀ u ∈ leaves, (certFormula rows L mins u).Unsat) :
    Complete rows L mins := by
  intro E hE hamb
  obtain ⟨u, hu, hsat⟩ := coversB_sound _ leaves hcov E
  exact certFormula_unsat rows (isotropyB_sound rows hiso) L mins u (hunsat u hu) E hE hsat hamb

/-- Symmetry checks: every generator preserves the code and the list (with an image table). -/
def symmetryB {n : ℕ} (rows : List (List (PauliCoord n))) (mins : Array (List (Fin n)))
    (gens : Array (Fin n → Fin n)) (imgs : Array (Array ℕ)) : Bool :=
  (List.range gens.size).all fun g =>
    match gens[g]?, imgs[g]? with
    | some p, some img => preservesB rows p && closedB mins p img
    | _, _ => false

theorem symmetryB_sound {n : ℕ} (rows : List (List (PauliCoord n))) (mins : Array (List (Fin n)))
    (gens : Array (Fin n → Fin n)) (imgs : Array (Array ℕ)) (h : symmetryB rows mins gens imgs = true) :
    ∀ p ∈ gens.toList, preservesB rows p = true ∧ ∃ img, closedB mins p img = true := by
  intro p hp
  obtain ⟨g, hg, hpg⟩ := array_mem_get hp
  have := List.all_eq_true.mp h g (List.mem_range.mpr hg)
  rw [hpg] at this
  cases hi : imgs[g]? with
  | none => simp [hi] at this
  | some img =>
    simp only [hi, Bool.and_eq_true] at this
    exact ⟨this.1, img, this.2⟩

/-- **Symmetric combiner.** For each representative `q` with leaves `us`, every formula
`certFormula rows L mins ((q, true) :: u)` (`u ∈ us`) is unsatisfiable. -/
theorem complete_symmetric {n : ℕ} (rows : List (List (PauliCoord n))) (L : ℕ)
    (mins : Array (List (Fin n))) (gens : Array (Fin n → Fin n)) (imgs : Array (Array ℕ))
    (words : Array (List ℕ)) (leaves : List (Fin n × List (List (Fin n × Bool))))
    (hiso : isotropyB rows = true)
    (hunc : ∀ M ∈ mins.toList, 0 < ambiguity (symplectic n) (rowSpace rows) (supported M.toFinset))
    (hsym : symmetryB rows mins gens imgs = true)
    (hreps : repsB gens (leaves.map Prod.fst) words = true)
    (hcov : ∀ p ∈ leaves, coversB (coverFuel p.2) p.2 = true)
    (hunsat : ∀ p ∈ leaves, ∀ u ∈ p.2, (certFormula rows L mins.toList ((p.1, true) :: u)).Unsat) :
    Complete rows L mins.toList := by
  have hS := isotropyB_sound rows hiso
  set S := rowSpace rows
  have hgens := symmetryB_sound rows mins gens imgs hsym
  have hinj : ∀ p ∈ gens.toList, injB p = true := fun p hp => by
    have := (hgens p hp).1
    simp only [preservesB, Bool.and_eq_true] at this
    exact this.1
  have hG := group_preserves rows gens (fun p hp => (hgens p hp).1)
  have hclosed := group_closed mins gens (fun p hp => by
    obtain ⟨img, himg⟩ := (hgens p hp).2
    exact ⟨img, injB_sound (hinj p hp), himg⟩)
  have hrep := repsB_sound gens hinj _ words hreps
  intro E hE hamb
  obtain ⟨M, hME, hM⟩ := exists_minimalUncorrectable_subset S E hamb
  obtain ⟨σ, hσ, M', hM', hcard, ⟨q, hq, hqM'⟩, hmap⟩ :=
    minimal_eq_image_through_representative S (genGroup gens) hG _ hrep hM
  rw [List.mem_toFinset, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  obtain ⟨u, hu, hsat⟩ := coversB_sound _ p.2 (hcov p hp) M'
  have hM'L : M'.card ≤ L := by
    rw [hcard]; exact (Finset.card_le_card hME).trans hE
  have hunits : ∀ w ∈ (p.1, true) :: u, (w.1 ∈ M' ↔ w.2 = true) := by
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · simpa using hqM'
    · exact hsat w hw
  obtain ⟨M0, hM0, hsub⟩ := certFormula_unsat rows hS L mins.toList _ (hunsat p hp u hu) M'
    hM'L hunits hM'.1
  have hM0eq : M0.toFinset = M' := by
    by_contra hne
    exact hM'.2 _ (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩) (hunc M0 hM0)
  have hlist : M' ∈ listFin mins := by
    simp only [listFin, List.mem_toFinset, List.mem_map]
    exact ⟨M0, hM0, hM0eq⟩
  have := hclosed σ hσ M' hlist
  rw [hmap] at this
  simp only [listFin, List.mem_toFinset, List.mem_map] at this
  obtain ⟨M1, hM1, hM1eq⟩ := this
  exact ⟨M1, hM1, hM1eq ▸ hME⟩

/-! ## 6. Consequences: distance, minimum-size sets, leading layer sum -/

section Consequences

variable {n : ℕ} (rows : List (List (PauliCoord n))) (L : ℕ) (mins : List (List (Fin n))) (d : ℕ)

/-- Size checks: every listed set has at least `d` elements, one has exactly `d`, `d ≤ L`. -/
def sizeB : Bool :=
  mins.all (fun M => decide (d ≤ M.toFinset.card)) && mins.any (fun M => M.toFinset.card == d) &&
    decide (d ≤ L)

theorem distance_of_complete (hc : Complete rows L mins)
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) (rowSpace rows) (supported M.toFinset))
    (hsize : sizeB L mins d = true) : IsDistance (rowSpace rows) d := by
  simp only [sizeB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hsize
  obtain ⟨⟨hge, M, hM, hMd⟩, hdL⟩ := hsize
  refine ⟨fun E hE hamb => ?_, M.toFinset, hMd, hunc M hM⟩
  obtain ⟨M', hM', hsub⟩ := hc E (by omega) hamb
  have := Finset.card_le_card hsub
  have := hge M' hM'
  omega

/-- The listed sets of size `d`, as distinct finsets. -/
def leadList : List (Finset (Fin n)) :=
  ((mins.map List.toFinset).filter (fun A => A.card == d)).dedup

theorem mem_leadList (A : Finset (Fin n)) :
    A ∈ leadList mins d ↔ (∃ M ∈ mins, M.toFinset = A) ∧ A.card = d := by
  simp [leadList, List.mem_dedup, List.mem_filter, List.mem_map]

/-- **The minimum-size uncorrectable sets are exactly the listed sets of size `d`.** -/
theorem layer_exact (hc : Complete rows L mins)
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) (rowSpace rows) (supported M.toFinset))
    (hsize : sizeB L mins d = true) (E : Finset (Fin n)) (hE : E.card = d) :
    0 < ambiguity (symplectic n) (rowSpace rows) (supported E) ↔ E ∈ leadList mins d := by
  have hsize' := hsize
  simp only [sizeB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsize'
  rw [mem_leadList]
  constructor
  · intro hamb
    obtain ⟨M, hM, hsub⟩ := hc E (by omega) hamb
    have h1 := hsize'.1.1 M hM
    have heq : M.toFinset = E := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact ⟨⟨M, hM, heq⟩, hE⟩
  · rintro ⟨⟨M, hM, rfl⟩, -⟩
    exact hunc M hM

/-- Number of listed size-`d` sets with exponent `k` (fast verified rank). -/
def leadCount (k : ℕ) : ℕ := ((leadList mins d).filter (fun A => ambRankL rows A == k)).length

/-- The nonzero counts `(exponent, count)`, computed with one rank evaluation per set. -/
def leadCounts : List (ℕ × ℕ) :=
  let ex := (leadList mins d).map (ambRankL rows)
  ((List.range (2 * n + 1)).map fun k => (k, ex.count k)).filter (fun p => p.2 != 0)

theorem count_map_eq_filter {α : Type} (f : α → ℕ) (k : ℕ) (l : List α) :
    (l.map f).count k = (l.filter (fun A => f A == k)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : f a = k
    · simp [List.count_cons, ih, h, List.filter_cons]
    · simp [List.count_cons, ih, h, List.filter_cons]

theorem leadCounts_spec : ∀ p ∈ leadCounts rows mins d, p.2 = leadCount rows mins d p.1 ∧
    p.1 ≤ 2 * n := by
  intro p hp
  simp only [leadCounts, List.mem_filter, List.mem_map, List.mem_range] at hp
  obtain ⟨⟨k, hk, rfl⟩, -⟩ := hp
  refine ⟨?_, by omega⟩
  exact count_map_eq_filter _ k _

/-- Exponents absent from `leadCounts` have count zero. -/
theorem leadCount_eq_zero_of_not_mem (k : ℕ) (hk : k ≤ 2 * n)
    (h : ∀ p ∈ leadCounts rows mins d, p.1 ≠ k) : leadCount rows mins d k = 0 := by
  by_contra hne
  apply h (k, leadCount rows mins d k) _ rfl
  simp only [leadCounts, List.mem_filter, List.mem_map, List.mem_range]
  refine ⟨⟨k, by omega, ?_⟩, by simpa using hne⟩
  simp only [Prod.mk.injEq, true_and]
  exact count_map_eq_filter _ k _

theorem sum_by_count (l : List (Finset (Fin n))) (f : ℕ → ℝ) (hl : ∀ A ∈ l, ambRankL rows A ≤ 2 * n) :
    (l.map fun A => f (ambRankL rows A)).sum =
      ∑ k ∈ Finset.range (2 * n + 1), ((l.filter fun A => ambRankL rows A == k).length : ℝ) * f k := by
  induction l with
  | nil => simp
  | cons A l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun B hB => hl B (by simp [hB]))]
    have hA := hl A (by simp)
    have : ∀ k, ((List.filter (fun B => ambRankL rows B == k) (A :: l)).length : ℝ) * f k =
        (if ambRankL rows A = k then f k else 0) +
          ((l.filter fun B => ambRankL rows B == k).length : ℝ) * f k := by
      intro k
      by_cases hk : ambRankL rows A = k
      · simp [List.filter_cons, hk]; ring
      · simp [List.filter_cons, hk]
    rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib,
      Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]

/-- **Exact leading layer sum.** -/
theorem leading_layer_sum (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows))
    (hc : Complete rows L mins)
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) (rowSpace rows) (supported M.toFinset))
    (hsize : sizeB L mins d = true) :
    ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = d),
        infidelityScore (rowSpace rows) E =
      ∑ k ∈ Finset.range (2 * n + 1), (leadCount rows mins d k : ℝ) * (1 - ((2 : ℝ) ^ k)⁻¹) := by
  have hnd : (leadList mins d).Nodup := List.nodup_dedup _
  -- the layer sum is the sum over the listed size-d sets
  have h1 : ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = d),
      infidelityScore (rowSpace rows) E =
      ∑ E ∈ (leadList mins d).toFinset, infidelityScore (rowSpace rows) E := by
    symm
    apply Finset.sum_subset
    · intro A hA
      rw [List.mem_toFinset, mem_leadList] at hA
      simp [hA.2]
    · intro E hE hnot
      have hEd : E.card = d := by simpa using hE
      apply infidelityScore_eq_zero
      have := (layer_exact rows L mins d hc hunc hsize E hEd).not.mpr
        (by simpa using hnot)
      omega
  rw [h1, List.sum_toFinset _ hnd]
  have h2 : ((leadList mins d).map fun E => infidelityScore (rowSpace rows) E) =
      (leadList mins d).map fun E => (fun k : ℕ => 1 - ((2 : ℝ) ^ k)⁻¹) (ambRankL rows E) := by
    apply List.map_congr_left
    intro E _
    simp only [infidelityScore, erasureScore, ambRankL_eq]
  rw [h2, sum_by_count rows _ (fun k : ℕ => 1 - ((2 : ℝ) ^ k)⁻¹) (fun A _ => ambRankL_le rows A)]
  rfl

end Consequences

/-! ## 7. The whole certificate -/

/-- All checks of a symmetric certificate. -/
def symCheckB {n : ℕ} (rows : List (List (PauliCoord n))) (L d : ℕ) (mins : Array (List (Fin n)))
    (xs : Array (List (PauliCoord n))) (zi : Array ℕ) (logs : Array (List (PauliCoord n)))
    (gens : Array (Fin n → Fin n)) (imgs : Array (Array ℕ)) (words : Array (List ℕ))
    (leaves : List (Fin n × List (List (Fin n × Bool)))) : Bool :=
  isotropyB rows && uncCheckB rows mins xs zi logs && sizeB L mins.toList d &&
    symmetryB rows mins gens imgs && repsB gens (leaves.map Prod.fst) words &&
    leaves.all (fun p => coversB (coverFuel p.2) p.2)

/-- All checks of a plain certificate. -/
def plainCheckB {n : ℕ} (rows : List (List (PauliCoord n))) (L d : ℕ) (mins : Array (List (Fin n)))
    (xs : Array (List (PauliCoord n))) (zi : Array ℕ) (logs : Array (List (PauliCoord n)))
    (leaves : List (List (Fin n × Bool))) : Bool :=
  isotropyB rows && uncCheckB rows mins xs zi logs && sizeB L mins.toList d &&
    coversB (coverFuel leaves) leaves

/-- What a certificate establishes. -/
def Certified {n : ℕ} (rows : List (List (PauliCoord n))) (L d : ℕ) (mins : List (List (Fin n))) :
    Prop :=
  Complete rows L mins ∧ IsDistance (rowSpace rows) d ∧
    (∀ E : Finset (Fin n), E.card = d →
      (0 < ambiguity (symplectic n) (rowSpace rows) (supported E) ↔ E ∈ leadList mins d)) ∧
    ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = d),
        infidelityScore (rowSpace rows) E =
      ∑ k ∈ Finset.range (2 * n + 1), (leadCount rows mins d k : ℝ) * (1 - ((2 : ℝ) ^ k)⁻¹)

theorem certified_of {n : ℕ} (rows : List (List (PauliCoord n))) (L d : ℕ)
    (mins : Array (List (Fin n))) (xs : Array (List (PauliCoord n))) (zi : Array ℕ)
    (logs : Array (List (PauliCoord n)))
    (hiso : isotropyB rows = true) (hcert : uncCheckB rows mins xs zi logs = true)
    (hsize : sizeB L mins.toList d = true) (hc : Complete rows L mins.toList) :
    Certified rows L d mins.toList := by
  have hS := isotropyB_sound rows hiso
  have hunc := uncCheckB_sound rows hS mins xs zi logs hcert
  exact ⟨hc, distance_of_complete rows L _ d hc hunc hsize,
    layer_exact rows L _ d hc hunc hsize, leading_layer_sum rows L _ d hS hc hunc hsize⟩

/-- **Symmetric certificate.** If `symCheckB` passes and every leaf formula
`certFormula rows L mins ((q, true) :: u)` is unsatisfiable, then the list is complete through
`L`, `d` is the distance, the minimum-size uncorrectable sets are exactly the listed ones of
size `d`, and the leading layer sum is given by the exponent counts. -/
theorem symmetric_certificate {n : ℕ} (rows : List (List (PauliCoord n))) (L d : ℕ)
    (mins : Array (List (Fin n))) (xs : Array (List (PauliCoord n))) (zi : Array ℕ)
    (logs : Array (List (PauliCoord n))) (gens : Array (Fin n → Fin n)) (imgs : Array (Array ℕ))
    (words : Array (List ℕ)) (leaves : List (Fin n × List (List (Fin n × Bool))))
    (h : symCheckB rows L d mins xs zi logs gens imgs words leaves = true)
    (hunsat : ∀ p ∈ leaves, ∀ u ∈ p.2, (certFormula rows L mins.toList ((p.1, true) :: u)).Unsat) :
    Certified rows L d mins.toList := by
  simp only [symCheckB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hiso, hcert⟩, hsize⟩, hsym⟩, hreps⟩, hcov⟩ := h
  have hS := isotropyB_sound rows hiso
  exact certified_of rows L d mins xs zi logs hiso hcert hsize
    (complete_symmetric rows L mins gens imgs words leaves hiso
      (uncCheckB_sound rows hS mins xs zi logs hcert) hsym hreps hcov hunsat)

/-- **Plain certificate.** -/
theorem plain_certificate {n : ℕ} (rows : List (List (PauliCoord n))) (L d : ℕ)
    (mins : Array (List (Fin n))) (xs : Array (List (PauliCoord n))) (zi : Array ℕ)
    (logs : Array (List (PauliCoord n))) (leaves : List (List (Fin n × Bool)))
    (h : plainCheckB rows L d mins xs zi logs leaves = true)
    (hunsat : ∀ u ∈ leaves, (certFormula rows L mins.toList u).Unsat) :
    Certified rows L d mins.toList := by
  simp only [plainCheckB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hiso, hcert⟩, hsize⟩, hcov⟩ := h
  exact certified_of rows L d mins xs zi logs hiso hcert hsize
    (complete_plain rows L mins.toList leaves hiso hcov hunsat)

end QecPhysical.Stabilizer.ListCertificate

#print axioms QecPhysical.Stabilizer.ListCertificate.rank_eq_rankL
#print axioms QecPhysical.Stabilizer.ListCertificate.ambRankL_eq
#print axioms QecPhysical.Stabilizer.ListCertificate.uncorrectableB_iff
#print axioms QecPhysical.Stabilizer.ListCertificate.isotropyB_sound
#print axioms QecPhysical.Stabilizer.ListCertificate.allCertOK_sound
#print axioms QecPhysical.Stabilizer.ListCertificate.group_preserves
#print axioms QecPhysical.Stabilizer.ListCertificate.group_closed
#print axioms QecPhysical.Stabilizer.ListCertificate.repsB_sound
#print axioms QecPhysical.Stabilizer.ListCertificate.coversB_sound
#print axioms QecPhysical.Stabilizer.ListCertificate.complete_plain
#print axioms QecPhysical.Stabilizer.ListCertificate.complete_symmetric
#print axioms QecPhysical.Stabilizer.ListCertificate.distance_of_complete
#print axioms QecPhysical.Stabilizer.ListCertificate.layer_exact
#print axioms QecPhysical.Stabilizer.ListCertificate.leading_layer_sum
#print axioms QecPhysical.Stabilizer.ListCertificate.allCertOK2_sound
#print axioms QecPhysical.Stabilizer.ListCertificate.symmetric_certificate
#print axioms QecPhysical.Stabilizer.ListCertificate.plain_certificate
#print axioms QecPhysical.Stabilizer.ListCertificate.leadCounts_spec
#print axioms QecPhysical.Stabilizer.ListCertificate.leadCount_eq_zero_of_not_mem
