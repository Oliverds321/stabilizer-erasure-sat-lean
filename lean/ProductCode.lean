import UncorrectableProbability
import QecReliability.SparseNormalizer

set_option autoImplicit false

/-!
# The `m`-fold direct sum of a stabilizer code and the uncorrectable-erasure probability

For a stabilizer space `S ≤ Pauli n` and `m : ℕ`, `power m S ≤ Pauli (n*m)` is the direct sum of
`m` copies of `S`, one per block of `n` qubits. Qubit `i` of block `b` is the coordinate
`idx n m (i, b) = finProdFinEquiv (i, b)` of the `n*m`-qubit register.

* `power_isotropic`: the `m`-fold code of an isotropic space is isotropic.
* `ambiguity_rep`: erasing the same set `E` in every block (`rep m E`) has ambiguity
  `m * d_E` (no isotropy needed).
* `powerFidelity`, `powerInfidelity`: the latent-bit fidelity and infidelity of the `m`-fold code
  when one latent iid bit per original qubit erases that qubit in every block.
* `uncorrectableProb_sandwich`: `(1 - 2^{-m}) U(p) ≤ I_m(p) ≤ U(p)` on `[0,1]`.
* `uncorrectable_of_relative`, `uncorrectable_relative_of_half`: transfer of a relative
  estimate of `I_m` to `U`.
* `rowSpace_rowsPower`: the row list of the `m`-fold code.
-/

noncomputable section

namespace QecReliability.ProductCode

open Module
open scoped BigOperators
open QecReliability.Binary
open QecPhysical.Stabilizer
open QecPhysical.Stabilizer.Uncorrectable

variable {n m : ℕ}

/-! ## Block coordinates -/

/-- Qubit `i` of block `b` in the `m`-fold register. -/
def idx (n m : ℕ) : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv

/-- Splitting a Pauli on `n*m` qubits into its `m` blocks. -/
def blocks (n m : ℕ) : Pauli (n * m) ≃ₗ[Bit] (Fin m → Pauli n) where
  toFun v b := (fun i => v.1 (idx n m (i, b)), fun i => v.2 (idx n m (i, b)))
  invFun w := (fun k => (w ((idx n m).symm k).2).1 ((idx n m).symm k).1,
    fun k => (w ((idx n m).symm k).2).2 ((idx n m).symm k).1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    ext k <;> simp
  right_inv w := by
    funext b
    ext i <;> simp

@[simp] theorem blocks_apply (v : Pauli (n * m)) (b : Fin m) :
    blocks n m v b = (fun i => v.1 (idx n m (i, b)), fun i => v.2 (idx n m (i, b))) := rfl

theorem symplectic_blocks (v w : Pauli (n * m)) :
    symplectic (n * m) v w = ∑ b, symplectic n (blocks n m v b) (blocks n m w b) := by
  simp only [symplectic_apply, blocks_apply]
  rw [← Equiv.sum_comp (idx n m), Fintype.sum_prod_type, Finset.sum_comm]

/-- Embedding of a Pauli on `n` qubits into block `b`. -/
def inj (m : ℕ) (b : Fin m) : Pauli n →ₗ[Bit] Pauli (n * m) :=
  (blocks n m).symm.toLinearMap ∘ₗ LinearMap.single Bit (fun _ : Fin m => Pauli n) b

@[simp] theorem blocks_inj (b : Fin m) (s : Pauli n) :
    blocks n m (inj m b s) = Pi.single b s := by
  simp [inj]

theorem symplectic_inj_left (b : Fin m) (s : Pauli n) (w : Pauli (n * m)) :
    symplectic (n * m) (inj m b s) w = symplectic n s (blocks n m w b) := by
  rw [symplectic_blocks, blocks_inj, Finset.sum_eq_single b]
  · rw [Pi.single_eq_same]
  · intro b' _ hb'
    rw [Pi.single_eq_of_ne hb', map_zero, LinearMap.zero_apply]
  · simp

theorem sum_inj_blocks (v : Pauli (n * m)) : ∑ b, inj m b (blocks n m v b) = v := by
  apply (blocks n m).injective
  rw [map_sum]
  simp only [blocks_inj]
  exact Finset.univ_sum_single _

/-! ## The `m`-fold code -/

/-- The direct sum of `m` copies of `P`, one per block. -/
def power (m : ℕ) (P : Submodule Bit (Pauli n)) : Submodule Bit (Pauli (n * m)) :=
  (Submodule.pi Set.univ (fun _ : Fin m => P)).comap (blocks n m).toLinearMap

@[simp] theorem mem_power (P : Submodule Bit (Pauli n)) (v : Pauli (n * m)) :
    v ∈ power m P ↔ ∀ b, blocks n m v b ∈ P := by
  simp [power, Submodule.mem_pi]

theorem power_mono {P Q : Submodule Bit (Pauli n)} (h : P ≤ Q) : power m P ≤ power m Q := by
  intro v hv
  rw [mem_power] at hv ⊢
  exact fun b => h (hv b)

theorem power_inf (P Q : Submodule Bit (Pauli n)) :
    power m (P ⊓ Q) = power m P ⊓ power m Q := by
  ext v
  simp only [mem_power, Submodule.mem_inf]
  exact forall_and

theorem inj_mem_power {P : Submodule Bit (Pauli n)} (b : Fin m) {s : Pauli n} (hs : s ∈ P) :
    inj m b s ∈ power m P := by
  rw [mem_power]
  intro b'
  rw [blocks_inj]
  by_cases h : b' = b
  · subst h
    simpa using hs
  · rw [Pi.single_eq_of_ne h]
    exact P.zero_mem

theorem normalizer_power (S : Submodule Bit (Pauli n)) :
    normalizer (symplectic (n * m)) (power m S) = power m (normalizer (symplectic n) S) := by
  ext w
  rw [mem_power]
  constructor
  · intro hw b s hs
    have h : symplectic (n * m) (inj m b s) w = 0 := hw (inj m b s) (inj_mem_power b hs)
    rw [symplectic_inj_left] at h
    exact h
  · intro hw v hv
    change symplectic (n * m) v w = 0
    rw [symplectic_blocks]
    apply Finset.sum_eq_zero
    intro b _
    exact hw b _ ((mem_power S v).mp hv b)

/-- The `m`-fold code of an isotropic space is isotropic. -/
theorem power_isotropic {S : Submodule Bit (Pauli n)}
    (hS : S ≤ normalizer (symplectic n) S) :
    power m S ≤ normalizer (symplectic (n * m)) (power m S) := by
  rw [normalizer_power]
  exact power_mono hS

theorem localized_power (S U : Submodule Bit (Pauli n)) :
    localized (symplectic (n * m)) (power m S) (power m U) =
      power m (localized (symplectic n) S U) := by
  unfold localized
  rw [normalizer_power, power_inf]

/-! ## Dimensions -/

/-- `Π_b P` as a submodule is linearly equivalent to `Fin m → P`. -/
def piEquiv (P : Submodule Bit (Pauli n)) :
    (Submodule.pi Set.univ (fun _ : Fin m => P)) ≃ₗ[Bit] (Fin m → P) where
  toFun x b := ⟨x.1 b, x.2 b (Set.mem_univ b)⟩
  invFun y := ⟨fun b => (y b).1, fun b _ => (y b).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finrank_power (P : Submodule Bit (Pauli n)) :
    finrank Bit (power m P) = m * finrank Bit P := by
  unfold power
  rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    LinearEquiv.finrank_eq (piEquiv P), Module.finrank_pi_fintype]
  simp

theorem ambiguity_power (S U : Submodule Bit (Pauli n)) :
    ambiguity (symplectic (n * m)) (power m S) (power m U) =
      m * ambiguity (symplectic n) S U := by
  unfold ambiguity
  rw [localized_power, ← power_inf, finrank_power, finrank_power, Nat.mul_sub]

/-! ## The same erased set in every block -/

/-- Erase the qubits of `E` in every block. -/
def rep (m : ℕ) (E : Finset (Fin n)) : Finset (Fin (n * m)) :=
  Finset.univ.filter (fun k => ((idx n m).symm k).1 ∈ E)

@[simp] theorem mem_rep (E : Finset (Fin n)) (k : Fin (n * m)) :
    k ∈ rep m E ↔ ((idx n m).symm k).1 ∈ E := by
  simp [rep]

theorem rep_mono : Monotone (rep (n := n) m) := by
  intro E E' h k hk
  rw [mem_rep] at hk ⊢
  exact h hk

theorem supported_rep (E : Finset (Fin n)) :
    supported (rep m E) = power m (supported E) := by
  ext v
  rw [mem_power, mem_supported]
  constructor
  · intro h b i hi
    exact h _ (by simpa using hi)
  · intro h k hk
    have h' := h ((idx n m).symm k).2 ((idx n m).symm k).1 (by simpa using hk)
    simpa using h'

/-- **(1)** The ambiguity of the `m`-fold code at the repeated erasure is `m * d_E`. -/
theorem ambiguity_rep (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    ambiguity (symplectic (n * m)) (power m S) (supported (rep m E)) =
      m * ambiguity (symplectic n) S (supported E) := by
  rw [supported_rep, ambiguity_power]

theorem erasureScore_rep (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    erasureScore (power m S) (rep m E) =
      ((2 : ℝ) ^ (m * ambiguity (symplectic n) S (supported E)))⁻¹ := by
  unfold erasureScore
  rw [ambiguity_rep]

theorem erasureScore_rep_eq_pow (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    erasureScore (power m S) (rep m E) = erasureScore S E ^ m := by
  rw [erasureScore_rep]
  unfold erasureScore
  rw [mul_comm, pow_mul, inv_pow]

/-! ## (2) Latent fidelity and infidelity of the `m`-fold code -/

/-- `F_m(p) = Σ_E P_p(E) 2^{-m d_E}`. -/
def powerFidelity (m : ℕ) (S : Submodule Bit (Pauli n)) (p : ℝ) : ℝ :=
  ∑ E : Finset (Fin n), causeMass p E *
    ((2 : ℝ) ^ (m * ambiguity (symplectic n) S (supported E)))⁻¹

/-- `I_m(p) = Σ_E P_p(E) (1 - 2^{-m d_E})`. -/
def powerInfidelity (m : ℕ) (S : Submodule Bit (Pauli n)) (p : ℝ) : ℝ :=
  ∑ E : Finset (Fin n), causeMass p E *
    (1 - ((2 : ℝ) ^ (m * ambiguity (symplectic n) S (supported E)))⁻¹)

theorem powerFidelity_eq_sum_rep (S : Submodule Bit (Pauli n)) (p : ℝ) :
    powerFidelity m S p =
      ∑ E : Finset (Fin n), causeMass p E * erasureScore (power m S) (rep m E) := by
  simp only [powerFidelity, erasureScore_rep]

theorem powerInfidelity_eq (S : Submodule Bit (Pauli n)) (p : ℝ) :
    powerInfidelity m S p = 1 - powerFidelity m S p := by
  unfold powerInfidelity powerFidelity
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, causeMass_sum]

/-! ## (3) Comparison with the uncorrectable probability -/

theorem pattern_sandwich (S : Submodule Bit (Pauli n)) (m : ℕ) (E : Finset (Fin n)) :
    (1 - ((2 : ℝ) ^ m)⁻¹) * uncorrectable S E ≤
        1 - ((2 : ℝ) ^ (m * ambiguity (symplectic n) S (supported E)))⁻¹ ∧
      1 - ((2 : ℝ) ^ (m * ambiguity (symplectic n) S (supported E)))⁻¹ ≤ uncorrectable S E := by
  unfold uncorrectable
  set d := ambiguity (symplectic n) S (supported E)
  split_ifs with hd
  · have hle : (2 : ℝ) ^ m ≤ 2 ^ (m * d) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right m hd)
    have hinv : ((2 : ℝ) ^ (m * d))⁻¹ ≤ ((2 : ℝ) ^ m)⁻¹ :=
      inv_anti₀ (by positivity) hle
    have hpos : (0 : ℝ) ≤ ((2 : ℝ) ^ (m * d))⁻¹ := by positivity
    constructor <;> linarith
  · have hd0 : d = 0 := by omega
    rw [hd0]
    norm_num

/-- **(3)** `(1 - 2^{-m}) U(p) ≤ I_m(p) ≤ U(p)` for `p ∈ [0,1]`. -/
theorem uncorrectableProb_sandwich (S : Submodule Bit (Pauli n)) (m : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - ((2 : ℝ) ^ m)⁻¹) * uncorrectableProb S p ≤ powerInfidelity m S p ∧
      powerInfidelity m S p ≤ uncorrectableProb S p := by
  unfold powerInfidelity uncorrectableProb
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro E _
    have h := mul_le_mul_of_nonneg_left (pattern_sandwich S m E).1 (causeMass_nonneg hp0 hp1 E)
    linarith
  · apply Finset.sum_le_sum
    intro E _
    exact mul_le_mul_of_nonneg_left (pattern_sandwich S m E).2 (causeMass_nonneg hp0 hp1 E)

theorem uncorrectableProb_nonneg (S : Submodule Bit (Pauli n)) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ uncorrectableProb S p :=
  Finset.sum_nonneg fun E _ =>
    mul_nonneg (causeMass_nonneg hp0 hp1 E) (uncorrectable_range S E).1

/-! ## (4) Transfer of relative accuracy -/

/-- **(4)** A relative `ε'`-estimate of `I_m(p)` is a two-sided estimate of `U(p)`. -/
theorem uncorrectable_of_relative (S : Submodule Bit (Pauli n)) (m : ℕ) {p ε' u : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε') (hε1 : ε' ≤ 1)
    (hu : |u - powerInfidelity m S p| ≤ ε' * powerInfidelity m S p) :
    (1 - ε') * (1 - ((2 : ℝ) ^ m)⁻¹) * uncorrectableProb S p ≤ u ∧
      u ≤ (1 + ε') * uncorrectableProb S p := by
  obtain ⟨h1, h2⟩ := uncorrectableProb_sandwich S m hp0 hp1
  obtain ⟨hl, hr⟩ := abs_le.mp hu
  have ha : 0 ≤ 1 - ε' := by linarith
  have hb : 0 ≤ 1 + ε' := by linarith
  have h3 := mul_le_mul_of_nonneg_left h1 ha
  have h4 := mul_le_mul_of_nonneg_left h2 hb
  constructor <;> nlinarith

/-- **(4)** With `2^{-m} ≤ ε/2` and `ε' = ε/2`, the estimate is within relative error `ε`
of `U(p)`. -/
theorem uncorrectable_relative_of_half (S : Submodule Bit (Pauli n)) (m : ℕ) {p ε u : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 2)
    (hm : ((2 : ℝ) ^ m)⁻¹ ≤ ε / 2)
    (hu : |u - powerInfidelity m S p| ≤ ε / 2 * powerInfidelity m S p) :
    |u - uncorrectableProb S p| ≤ ε * uncorrectableProb S p := by
  obtain ⟨hl, hr⟩ := uncorrectable_of_relative S m hp0 hp1 (by linarith) (by linarith) hu
  have hU := uncorrectableProb_nonneg S hp0 hp1
  have ha : 0 ≤ 1 - ε / 2 := by linarith
  have hb : (1 - ε / 2) * uncorrectableProb S p ≤
      (1 - ((2 : ℝ) ^ m)⁻¹) * uncorrectableProb S p :=
    mul_le_mul_of_nonneg_right (by linarith) hU
  have hc := mul_le_mul_of_nonneg_left hb ha
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (mul_nonneg hε0 hε0) hU]


/-! ## Exact zero pattern of the infidelity coefficients -/

/-- Per pattern: the `m`-fold score is one iff the pattern is correctable (`m ≥ 1`). -/
theorem erasureScore_rep_eq_one_iff (S : Submodule Bit (Pauli n)) (hm : 1 ≤ m)
    (E : Finset (Fin n)) :
    erasureScore (power m S) (rep m E) = 1 ↔ uncorrectable S E = 0 := by
  rw [erasureScore_rep]
  unfold uncorrectable
  set d := ambiguity (symplectic n) S (supported E)
  split_ifs with hd
  · have hle : (2 : ℝ) ^ 1 ≤ 2 ^ (m * d) :=
      pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.mpr (by positivity))
    have hinv : ((2 : ℝ) ^ (m * d))⁻¹ ≤ ((2 : ℝ) ^ 1)⁻¹ := inv_anti₀ (by positivity) hle
    constructor
    · intro h
      rw [h] at hinv
      norm_num at hinv
    · intro h
      norm_num at h
  · have hd0 : d = 0 := by omega
    rw [hd0]
    norm_num

theorem erasureScore_rep_le_one (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    erasureScore (power m S) (rep m E) ≤ 1 :=
by
  unfold erasureScore
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- The true Bernstein coefficients of the latent `m`-fold fidelity are one (zero infidelity)
exactly where the layer fractions of `U` vanish. -/
theorem layerAverage_rep_eq_one_iff (S : Submodule Bit (Pauli n)) (hm : 1 ≤ m)
    (j : Fin (n + 1)) :
    layerAverage (id : Causes n → Finset (Fin n))
        (fun E => erasureScore (power m S) (rep m E)) j = 1 ↔ layerFraction S j = 0 := by
  classical
  have hj : 0 < (n.choose j.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ j.isLt)
  have hc : (Fintype.card {b : Causes n // hammingLayer b = j} : ℝ) = n.choose j.val := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using hamming_layer_card n j)
  unfold layerFraction layerAverage
  rw [div_eq_one_iff_eq hj.ne', div_eq_zero_iff, or_iff_left hj.ne']
  have hone : (n.choose j.val : ℝ) = ∑ _b : {b : Causes n // hammingLayer b = j}, (1 : ℝ) := by
    simpa using hc.symm
  rw [hone, Finset.sum_eq_sum_iff_of_le (fun b _ => erasureScore_rep_le_one S _),
    Finset.sum_eq_zero_iff_of_nonneg (fun b _ => (uncorrectable_range S _).1)]
  exact forall₂_congr fun b _ => erasureScore_rep_eq_one_iff S hm _

/-! ## Rows of the `m`-fold code -/

section Rows

open QecReliability.SharedCircuit

/-- Coordinate `c` of block `b`. -/
def blockCoord (m : ℕ) (b : Fin m) : PauliCoord n → PauliCoord (n * m) :=
  Sum.map (fun i => idx n m (i, b)) (fun i => idx n m (i, b))

/-- For every block `b`, the input rows placed in block `b`. -/
def rowsPower (m : ℕ) (rows : List (List (PauliCoord n))) : List (List (PauliCoord (n * m))) :=
  (List.finRange m).flatMap (fun b => rows.map (List.map (blockCoord m b)))

theorem rowIncidences_rowsPower (rows : List (List (PauliCoord n))) :
    rowIncidences (rowsPower m rows) = m * rowIncidences rows := by
  unfold rowIncidences rowsPower
  simp [List.map_map, Function.comp_def, List.flatMap, List.sum_flatten,
    List.map_const', List.sum_replicate]

theorem blocks_xUnit (b : Fin m) (i : Fin n) :
    blocks n m (xUnit (idx n m (i, b))) = Pi.single b (xUnit i) := by
  funext b'
  by_cases h : b' = b
  · subst h
    ext i' <;> simp [xUnit, Pi.single_apply]
  · rw [Pi.single_eq_of_ne h]
    ext i' <;> simp [xUnit, h]

theorem blocks_zUnit (b : Fin m) (i : Fin n) :
    blocks n m (zUnit (idx n m (i, b))) = Pi.single b (zUnit i) := by
  funext b'
  by_cases h : b' = b
  · subst h
    ext i' <;> simp [zUnit, Pi.single_apply]
  · rw [Pi.single_eq_of_ne h]
    ext i' <;> simp [zUnit, h]

theorem coordPauli_blockCoord (b : Fin m) (c : PauliCoord n) :
    coordPauli (blockCoord m b c) = inj m b (coordPauli c) := by
  apply (blocks n m).injective
  rw [blocks_inj]
  cases c with
  | inl i => exact blocks_xUnit b i
  | inr i => exact blocks_zUnit b i

theorem decodeRow_blockCoord (b : Fin m) (row : List (PauliCoord n)) :
    decodeRow (row.map (blockCoord m b)) = inj m b (decodeRow row) := by
  unfold decodeRow
  rw [map_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  exact coordPauli_blockCoord b c

theorem mem_rowsPower_decode (rows : List (List (PauliCoord n))) (x : Pauli (n * m)) :
    x ∈ (rowsPower m rows).map decodeRow ↔
      ∃ b, ∃ row ∈ rows, inj m b (decodeRow row) = x := by
  simp only [rowsPower, List.mem_map, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨r, ⟨b, row, hrow, rfl⟩, rfl⟩
    exact ⟨b, row, hrow, (decodeRow_blockCoord b row).symm⟩
  · rintro ⟨b, row, hrow, rfl⟩
    exact ⟨row.map (blockCoord m b), ⟨b, row, hrow, rfl⟩, decodeRow_blockCoord b row⟩

/-- The row list of the `m`-fold code spans the `m`-fold row space. -/
theorem rowSpace_rowsPower (rows : List (List (PauliCoord n))) :
    rowSpace (rowsPower m rows) = power m (rowSpace rows) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨b, row, hrow, rfl⟩ := (mem_rowsPower_decode rows x).mp hx
    exact inj_mem_power b (Submodule.subset_span (List.mem_map.mpr ⟨row, hrow, rfl⟩))
  · intro v hv
    rw [← sum_inj_blocks v]
    refine Submodule.sum_mem _ fun b _ => ?_
    have hmap : (rowSpace rows).map (inj m b) ≤ rowSpace (rowsPower m rows) := by
      rw [rowSpace, Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
      exact (mem_rowsPower_decode rows _).mpr ⟨b, row, hrow, rfl⟩
    exact hmap ⟨blocks n m v b, (mem_power _ v).mp hv b, rfl⟩

theorem rowsPower_isotropic {rows : List (List (PauliCoord n))}
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) :
    rowSpace (rowsPower m rows) ≤
      normalizer (symplectic (n * m)) (rowSpace (rowsPower m rows)) := by
  rw [rowSpace_rowsPower]
  exact power_isotropic hS

end Rows

end QecReliability.ProductCode

#print axioms QecReliability.ProductCode.power_isotropic
#print axioms QecReliability.ProductCode.ambiguity_power
#print axioms QecReliability.ProductCode.ambiguity_rep
#print axioms QecReliability.ProductCode.erasureScore_rep_eq_pow
#print axioms QecReliability.ProductCode.powerFidelity_eq_sum_rep
#print axioms QecReliability.ProductCode.powerInfidelity_eq
#print axioms QecReliability.ProductCode.uncorrectableProb_sandwich
#print axioms QecReliability.ProductCode.uncorrectable_of_relative
#print axioms QecReliability.ProductCode.uncorrectable_relative_of_half
#print axioms QecReliability.ProductCode.rowSpace_rowsPower
#print axioms QecReliability.ProductCode.layerAverage_rep_eq_one_iff
#print axioms QecReliability.ProductCode.rowsPower_isotropic
#print axioms QecReliability.ProductCode.rowIncidences_rowsPower
