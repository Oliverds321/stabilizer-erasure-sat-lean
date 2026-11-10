import EnumeratorExample
import PointHardness
import QecReliability.LatentEncoder

set_option autoImplicit false

/-!
# Worked examples of the manuscript, machine-checked

P6. Sampling tail bound `(1/2) p^d ≤ I(p) ≤ U(p) ≤ Σ_{|E| ≥ d} p^|E| (1-p)^(n-|E|)`, and the
    right side equals the binomial tail `Σ_{j=d}^{n} C(n,j) p^j (1-p)^(n-j)` (`eq:tail`).
P3. One erased repetition-code qubit: uncorrectable, entanglement fidelity `1/2`,
    average fidelity `(D F_e + 1)/(D + 1) = 2/3` with `D = 2^k = 2`.
P1. Bell stabilizer state under full erasure: `Good` holds on all of `N = S`, but on exactly
    `4` of the `16` vectors of the ambient `W`.
P2. Bell pair on qubits 1,2 plus two free qubits: a positive `Bad` pair has `|N_E|/2`
    witnesses, i.e. `2` for `E = {1,3}` and `8` for `E = {3,4}` (1-based labels).
P5. One unencoded qubit with latent map `C(b₁,b₂) = b₁ XOR b₂` (an explicit one-gate
    `SharedCircuit.Program`): coefficients `(1, 1/4, 1)` and `I_{H,C}(p) = (3/2) p (1-p)`,
    also for the physical optimum of the latent iid flagged erasure channel.
P4. Three-qubit repetition code with five appended `Z`-stabilized qubits: the homogeneous
    weight-two fidelity polynomial `P(y) = Σ_{i<j} 2^{-d_{\{i,j\}}} y_i y_j` has the constant
    Hessian `H_ij = 2^{-d_{\{i,j\}}}` (`i ≠ j`), `H_ii = 0`, which is positive definite on
    `span{1_R, 1_A}`; and `log P` is not concave on the open positive orthant.
-/

noncomputable section

namespace QecPhysical.Stabilizer.PaperExamples

open scoped BigOperators
open Finset
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecReliability.BinaryElimination
open QecPhysical.Stabilizer.EnumeratorExample
open QecPhysical.Stabilizer.Uncorrectable

/-! ## P6. The sampling tail bound -/

theorem uncorrectable_le_tail_indicator {n : ℕ} (S : Submodule Bit (Pauli n)) {d : ℕ}
    (hd : IsDistance S d) (E : Finset (Fin n)) :
    uncorrectable S E ≤ if d ≤ E.card then 1 else 0 := by
  unfold uncorrectable
  by_cases h2 : d ≤ E.card
  · rw [if_pos h2]
    split_ifs <;> norm_num
  · rw [if_neg h2, if_neg (hd.1 E (by omega))]

theorem tail_mass_eq_indicator_sum {n : ℕ} (d : ℕ) (p : ℝ) :
    ∑ E ∈ univ.filter (fun E : Finset (Fin n) => d ≤ E.card), causeMass p E =
      ∑ E : Finset (Fin n), causeMass p E * (if d ≤ E.card then (1:ℝ) else 0) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun E _ => ?_)
  split_ifs <;> simp

theorem card_layer (n j : ℕ) :
    (univ.filter (fun E : Finset (Fin n) => E.card = j)).card = n.choose j := by
  rw [← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

/-- The iid mass of `{E : d ≤ |E|}` is the binomial tail `P{Binomial(n,p) ≥ d}`. -/
theorem tail_mass_eq_binomial {n : ℕ} (d : ℕ) (p : ℝ) :
    ∑ E ∈ univ.filter (fun E : Finset (Fin n) => d ≤ E.card), causeMass p E =
      ∑ j ∈ Finset.Ico d (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
  rw [tail_mass_eq_indicator_sum, causeMass_sum_layers]
  have h2 : ∀ j, ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j),
      (if d ≤ E.card then (1:ℝ) else 0) = if d ≤ j then (n.choose j : ℝ) else 0 := by
    intro j
    rw [Finset.sum_congr rfl (fun E hE => by rw [(Finset.mem_filter.mp hE).2]),
      Finset.sum_const, nsmul_eq_mul, card_layer]
    split_ifs <;> simp
  simp_rw [h2, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hs : (range (n + 1)).filter (fun j => d ≤ j) = Finset.Ico d (n + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hs]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **P6 (`eq:tail`).** For an isotropic `S` with distance `d` and `0 ≤ p ≤ 1`:
`p^d/2 ≤ I(p) ≤ U(p) ≤ Σ_{|E| ≥ d} causeMass p E = Σ_{j=d}^{n} C(n,j) p^j (1-p)^(n-j)`. -/
theorem tail_bound {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ d / 2 ≤ infidelity S p ∧
    infidelity S p ≤ uncorrectableProb S p ∧
    uncorrectableProb S p ≤
      ∑ E ∈ univ.filter (fun E : Finset (Fin n) => d ≤ E.card), causeMass p E ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin n) => d ≤ E.card), causeMass p E =
      ∑ j ∈ Finset.Ico d (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
  refine ⟨le_infidelity S hS hd hp0 hp1, (infidelity_le_uncorrectableProb S hp0 hp1).1, ?_,
    tail_mass_eq_binomial d p⟩
  rw [tail_mass_eq_indicator_sum]
  exact Finset.sum_le_sum (fun E _ => mul_le_mul_of_nonneg_left
    (uncorrectable_le_tail_indicator S hd E) (causeMass_nonneg hp0 hp1 E))

/-! ## P3. One erased repetition-code qubit -/

/-- The repetition code (rows of code R) encodes `k = 1` qubit: `n - dim S = 1`. -/
theorem repetition_k_eq_one : 3 - Module.finrank Bit (rowSpace rowsR) = 1 := by
  have h := ambiguity_full (rowSpace rowsR) isotropic_R
  have h2 : ambiguityRank rowsR univ = 2 := by decide
  rw [ambiguity_eq_rank, h2] at h
  omega

/-- One erased repetition-code qubit is uncorrectable (correctability zero). -/
theorem repetition_single_uncorrectable (i : Fin 3) :
    uncorrectable (rowSpace rowsR) {i} = 1 := by
  unfold uncorrectable
  rw [ambiguity_eq_rank, repetition_single]
  norm_num

/-- Average fidelity `(D F_e + 1)/(D + 1)` with `D = 2^1` and `F_e = 1/2` equals `2/3`. -/
theorem repetition_single_average_fidelity (i : Fin 3) :
    ((2:ℝ) ^ (3 - Module.finrank Bit (rowSpace rowsR)) * erasureScore (rowSpace rowsR) {i} + 1) /
      ((2:ℝ) ^ (3 - Module.finrank Bit (rowSpace rowsR)) + 1) = 2 / 3 := by
  rw [repetition_k_eq_one, repetition_single_score]
  norm_num

/-! ## P1. Bell stabilizer state under full erasure -/

/-- Bell pair: checks `X₁X₂`, `Z₁Z₂`. -/
def rowsBell : List (List (PauliCoord 2)) := [[.inl 0, .inl 1], [.inr 0, .inr 1]]

theorem bell_full_good_iff (z : Pauli 2) :
    Good (symplectic 2) (rowSpace rowsBell) (supported univ) z ↔ z ∈ rowSpace rowsBell := by
  rw [good_iff_cleaning, Finset.compl_univ, supported_empty, sup_bot_eq]

theorem bell_mem_iff (z : Pauli 2) :
    z ∈ rowSpace rowsBell ↔
      ∃ c d : Bit, c • decodeRow [.inl 0, .inl 1] + d • decodeRow [.inr 0, .inr 1] = z :=
  mem_rowSpace_pair _ _ z

/-- **P1(a).** `Good` holds for every `z ∈ N` (here `N = S`). -/
theorem bell_good_on_normalizer (z : Pauli 2)
    (hz : z ∈ normalizer (symplectic 2) (rowSpace rowsBell)) :
    Good (symplectic 2) (rowSpace rowsBell) (supported univ) z := by
  have key : ∀ z : Pauli 2, (∀ row ∈ rowsBell, symplectic 2 (decodeRow row) z = 0) →
      ∃ c d : Bit, c • decodeRow [.inl 0, .inl 1] + d • decodeRow [.inr 0, .inr 1] = z := by
    decide
  rw [bell_full_good_iff, bell_mem_iff]
  exact key z ((mem_normalizer_rows rowsBell z).mp hz)

theorem bell_count_aux :
    (univ.filter (fun z : Pauli 2 =>
      ∃ c d : Bit, c • decodeRow [.inl 0, .inl 1] + d • decodeRow [.inr 0, .inr 1] = z)).card = 4 := by
  decide

theorem bell_normalizer_count_aux :
    (univ.filter (fun z : Pauli 2 =>
      ∀ row ∈ rowsBell, symplectic 2 (decodeRow row) z = 0)).card = 4 := by
  decide

theorem card_pauli_two : Fintype.card (Pauli 2) = 16 := by
  simp [Pauli, Fintype.card_fun, ZMod.card]

open Classical in
/-- **P1(b).** Over `N`, all `4` vectors are `Good` (probability one); over the ambient
`W = Pauli 2`, exactly `4` of `16` are `Good` (probability `1/4`). -/
theorem bell_good_counts :
    (univ.filter (fun z : Pauli 2 => z ∈ normalizer (symplectic 2) (rowSpace rowsBell) ∧
        Good (symplectic 2) (rowSpace rowsBell) (supported univ) z)).card =
      (univ.filter (fun z : Pauli 2 => z ∈ normalizer (symplectic 2) (rowSpace rowsBell))).card ∧
    (univ.filter (fun z : Pauli 2 => z ∈ normalizer (symplectic 2) (rowSpace rowsBell))).card = 4 ∧
    (univ.filter (fun z : Pauli 2 =>
        Good (symplectic 2) (rowSpace rowsBell) (supported univ) z)).card = 4 ∧
    Fintype.card (Pauli 2) = 16 ∧
    ((univ.filter (fun z : Pauli 2 =>
        Good (symplectic 2) (rowSpace rowsBell) (supported univ) z)).card : ℚ) /
      Fintype.card (Pauli 2) = 1 / 4 := by
  have hN : (univ.filter (fun z : Pauli 2 =>
      z ∈ normalizer (symplectic 2) (rowSpace rowsBell))).card = 4 := by
    rw [← bell_normalizer_count_aux]
    congr 1
    exact Finset.filter_congr (fun z _ => mem_normalizer_rows rowsBell z)
  have hG : (univ.filter (fun z : Pauli 2 =>
      Good (symplectic 2) (rowSpace rowsBell) (supported univ) z)).card = 4 := by
    rw [← bell_count_aux]
    congr 1
    exact Finset.filter_congr (fun z _ => (bell_full_good_iff z).trans (bell_mem_iff z))
  refine ⟨?_, hN, hG, card_pauli_two, ?_⟩
  · congr 1
    exact Finset.filter_congr (fun z _ =>
      ⟨fun h => h.1, fun h => ⟨h, bell_good_on_normalizer z h⟩⟩)
  · rw [hG, card_pauli_two]
    norm_num

/-! ## P2. Witness multiplicity of `Bad` -/

theorem bit_cases : ∀ b : Bit, b = 0 ∨ b = 1 := by decide

theorem pauli_add_self {n : ℕ} (x : Pauli n) : x + x = 0 := by
  have h2 : (2 : Bit) = 0 := by decide
  rw [← two_smul Bit x, h2, zero_smul]

open Classical in
/-- A positive `Bad` pair for `(L, z)` has exactly `|L|/2` witnesses `x ∈ L` with `⟨x,z⟩ = 1`. -/
theorem witness_count {n : ℕ} (L : Submodule Bit (Pauli n)) (z : Pauli n) {x0 : Pauli n}
    (hx0 : x0 ∈ L) (h1 : symplectic n x0 z = 1) :
    2 * (univ.filter (fun x : Pauli n => x ∈ L ∧ symplectic n x z = 1)).card =
      (univ.filter (fun x : Pauli n => x ∈ L)).card := by
  set O := univ.filter (fun x : Pauli n => x ∈ L ∧ symplectic n x z = 1)
  set Z := univ.filter (fun x : Pauli n => x ∈ L ∧ symplectic n x z = 0)
  have hadd : ∀ x, symplectic n (x + x0) z = symplectic n x z + 1 := by
    intro x
    rw [LinearMap.map_add₂, h1]
  have hinv : ∀ x : Pauli n, x + x0 + x0 = x := by
    intro x
    rw [add_assoc, pauli_add_self, add_zero]
  have h01 : (0 : Bit) + 1 = 1 := by decide
  have h11 : (1 : Bit) + 1 = 0 := by decide
  have hZO : Z.card = O.card := by
    refine Finset.card_bij' (fun x _ => x + x0) (fun x _ => x + x0) ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hL, hb⟩ := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L.add_mem hL hx0, by rw [hadd, hb, h01]⟩
    · intro x hx
      obtain ⟨hL, hb⟩ := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L.add_mem hL hx0, by rw [hadd, hb, h11]⟩
    · intro x _
      exact hinv x
    · intro x _
      exact hinv x
  have hdisj : Disjoint Z O := by
    rw [Finset.disjoint_left]
    intro x hZ hO
    have a := (Finset.mem_filter.mp hZ).2.2
    have b := (Finset.mem_filter.mp hO).2.2
    rw [a] at b
    exact absurd b (by decide)
  have hunion : Z ∪ O = univ.filter (fun x : Pauli n => x ∈ L) := by
    ext x
    simp only [Z, O, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro h
      rcases bit_cases (symplectic n x z) with hb | hb
      · exact Or.inl ⟨h, hb⟩
      · exact Or.inr ⟨h, hb⟩
  rw [← hunion, Finset.card_union_of_disjoint hdisj, hZO]
  ring

open Classical in
theorem filter_mem_card {n : ℕ} (L : Submodule Bit (Pauli n)) :
    (univ.filter (fun x : Pauli n => x ∈ L)).card = 2 ^ Module.finrank Bit L := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  change Nat.card L = _
  rw [Module.natCard_eq_pow_finrank (K := Bit)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem finrank_localized_rows {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    Module.finrank Bit (localized (symplectic n) (rowSpace rows) (supported E)) =
      2 * E.card - restrictedRank rows E := by
  rw [localized_dimension, restrictedRank_correct]

/-- Bell pair on qubits 1,2 of four qubits (qubits 3,4 free). -/
def rowsBell4 : List (List (PauliCoord 4)) := [[.inl 0, .inl 1], [.inr 0, .inr 1]]

theorem isotropic_Bell4 : rowSpace rowsBell4 ≤ normalizer (symplectic 4) (rowSpace rowsBell4) :=
  rowSpace_isotropic_of rowsBell4 (by decide)

/-- `E = {1,3}` (1-based) is `{0,2}` in `Fin 4`; `E = {3,4}` is `{2,3}`. -/
def E13 : Finset (Fin 4) := {0, 2}
def E34 : Finset (Fin 4) := {2, 3}

theorem localized_E13 :
    Module.finrank Bit (localized (symplectic 4) (rowSpace rowsBell4) (supported E13)) = 2 := by
  rw [finrank_localized_rows]
  decide

theorem localized_E34 :
    Module.finrank Bit (localized (symplectic 4) (rowSpace rowsBell4) (supported E34)) = 4 := by
  rw [finrank_localized_rows]
  decide

/-- Both erasures are uncorrectable, so positive `Bad` pairs exist (ambiguities `2` and `4`). -/
theorem bell4_ambiguities :
    ambiguity (symplectic 4) (rowSpace rowsBell4) (supported E13) = 2 ∧
    ambiguity (symplectic 4) (rowSpace rowsBell4) (supported E34) = 4 := by
  rw [ambiguity_eq_rank, ambiguity_eq_rank]
  decide

theorem bell4_bad_exists (E : Finset (Fin 4))
    (hE : 0 < ambiguity (symplectic 4) (rowSpace rowsBell4) (supported E)) :
    ∃ z ∈ normalizer (symplectic 4) (rowSpace rowsBell4),
      Bad (symplectic 4) (rowSpace rowsBell4) (supported E) z :=
  (ambiguity_pos_iff_exists_bad (symplectic 4) (symplectic_nondegenerate 4) (symplectic_refl 4)
    _ _ isotropic_Bell4).mp hE

open Classical in
/-- **P2, `E = {1,3}`.** Every positive `Bad` pair has exactly `2` witnesses. -/
theorem bell4_witnesses_E13 (z : Pauli 4)
    (hz : Bad (symplectic 4) (rowSpace rowsBell4) (supported E13) z) :
    (univ.filter (fun x : Pauli 4 =>
      x ∈ localized (symplectic 4) (rowSpace rowsBell4) (supported E13) ∧
        symplectic 4 x z = 1)).card = 2 := by
  obtain ⟨x0, hx0, h1⟩ := hz
  have h := witness_count _ z hx0 h1
  rw [filter_mem_card, localized_E13] at h
  omega

open Classical in
/-- **P2, `E = {3,4}`.** Every positive `Bad` pair has exactly `8` witnesses. -/
theorem bell4_witnesses_E34 (z : Pauli 4)
    (hz : Bad (symplectic 4) (rowSpace rowsBell4) (supported E34) z) :
    (univ.filter (fun x : Pauli 4 =>
      x ∈ localized (symplectic 4) (rowSpace rowsBell4) (supported E34) ∧
        symplectic 4 x z = 1)).card = 8 := by
  obtain ⟨x0, hx0, h1⟩ := hz
  have h := witness_count _ z hx0 h1
  rw [filter_mem_card, localized_E34] at h
  omega

/-! ## P5. The latent XOR example -/

/-- One XOR gate on two latent bits; its output wire is the single physical erasure bit. -/
def xorProgram : SharedCircuit.Program 2 1 :=
  ⟨1, Circuit.snoc Circuit.nil (Gate.xorGate ⟨0, by decide⟩ ⟨1, by decide⟩),
    fun _ => ⟨2, by decide⟩⟩

/-- The circuit map erases the qubit iff exactly one latent bit is set. -/
theorem xor_circuitMap :
    ∀ b : Causes 2, LatentEncoding.circuitMap xorProgram b = if b.card = 1 then univ else ∅ := by
  decide

theorem bare_score_empty : erasureScore (rowSpace rowsBare) ∅ = 1 := by
  have h0 : ambiguityRank rowsBare ∅ = 0 := by decide
  rw [erasureScore_eq_rank, h0]
  norm_num

theorem bare_score_univ : erasureScore (rowSpace rowsBare) univ = 1 / 4 := by
  have h : (univ : Finset (Fin 1)) = {0} := by decide
  rw [h, bare_score]

theorem xor_score (b : Causes 2) :
    erasureScore (rowSpace rowsBare) (LatentEncoding.circuitMap xorProgram b) =
      if b.card = 1 then 1 / 4 else 1 := by
  rw [xor_circuitMap]
  split_ifs
  · exact bare_score_univ
  · exact bare_score_empty

theorem univ_finset_fin_two :
    (univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, univ} := by decide

/-- **P5(a).** The latent fidelity curve. -/
theorem xor_latentCurve (p : ℝ) :
    latentCurve (LatentEncoding.circuitMap xorProgram) (erasureScore (rowSpace rowsBare)) p =
      1 - (3 / 2) * p * (1 - p) := by
  unfold latentCurve
  simp only [xor_score]
  rw [univ_finset_fin_two]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have c0 : (∅ : Finset (Fin 2)).card = 0 := rfl
  have c1 : ({0} : Finset (Fin 2)).card = 1 := rfl
  have c2 : ({1} : Finset (Fin 2)).card = 1 := rfl
  have c3 : (univ : Finset (Fin 2)).card = 2 := rfl
  simp only [c0, c1, c2, c3]
  norm_num
  ring

/-- **P5(b).** Exact fidelity coefficients `(1, 1/4, 1)`. -/
theorem xor_coefficients :
    layerAverage (LatentEncoding.circuitMap xorProgram) (erasureScore (rowSpace rowsBare)) 0 = 1 ∧
    layerAverage (LatentEncoding.circuitMap xorProgram) (erasureScore (rowSpace rowsBare)) 1 =
      1 / 4 ∧
    layerAverage (LatentEncoding.circuitMap xorProgram) (erasureScore (rowSpace rowsBare)) 2 = 1 := by
  have key : ∀ j : Fin 3,
      layerAverage (LatentEncoding.circuitMap xorProgram) (erasureScore (rowSpace rowsBare)) j =
        (∑ b ∈ univ.filter (fun b : Causes 2 => hammingLayer b = j),
          (if b.card = 1 then (1:ℝ) / 4 else 1)) / ((2 : ℕ).choose j.val : ℝ) := by
    intro j
    unfold layerAverage
    have hs : ∑ b ∈ univ.filter (fun b : Causes 2 => hammingLayer b = j),
        erasureScore (rowSpace rowsBare) (LatentEncoding.circuitMap xorProgram b) =
        ∑ b : {b : Causes 2 // hammingLayer b = j},
          erasureScore (rowSpace rowsBare) (LatentEncoding.circuitMap xorProgram b) :=
      Finset.sum_subtype _ (by simp) _
    rw [← hs, Finset.sum_congr rfl (fun b _ => xor_score b)]
  have f0 : univ.filter (fun b : Causes 2 => hammingLayer b = 0) = {∅} := by decide
  have f1 : univ.filter (fun b : Causes 2 => hammingLayer b = 1) = {{0}, {1}} := by decide
  have f2 : univ.filter (fun b : Causes 2 => hammingLayer b = 2) = {univ} := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [key, f0, Finset.sum_singleton]
    norm_num
  · rw [key, f1, Finset.sum_pair (by decide)]
    have c1 : ({0} : Finset (Fin 2)).card = 1 := rfl
    have c2 : ({1} : Finset (Fin 2)).card = 1 := rfl
    simp only [c1, c2]
    norm_num
  · rw [key, f2, Finset.sum_singleton]
    have c3 : (univ : Finset (Fin 2)).card = 2 := rfl
    simp only [c3]
    norm_num

theorem isotropic_bare : rowSpace rowsBare ≤ normalizer (symplectic 1) (rowSpace rowsBare) :=
  rowSpace_isotropic_of rowsBare (by decide)

def liftBare : Lift (rowSpace rowsBare) := isotropicLift _ isotropic_bare

/-- **P5(c).** Physical form: the optimal infidelity of the latent iid flagged erasure channel
with latent map `C = circuitMap xorProgram` is `(3/2) p (1-p)`, and no recovery does better. -/
theorem xor_physical (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - entanglementFidelity (liftBare.erasureFlagDecoder.comp
        (liftBare.iidLatentErasure (LatentEncoding.circuitMap xorProgram) p hp hp1)).map =
      (3 / 2) * p * (1 - p) ∧
    ∀ Q : Channel (ErasureFlagOutput 1) liftBare.LogicalIndex,
      1 - (3 / 2) * p * (1 - p) ≥ entanglementFidelity
        (Q.comp (liftBare.iidLatentErasure (LatentEncoding.circuitMap xorProgram) p hp hp1)).map := by
  have h := liftBare.iidLatentErasure_optimum (LatentEncoding.circuitMap xorProgram) p hp hp1
  rw [← latentCurve_eq_bernstein, xor_latentCurve] at h
  refine ⟨by rw [h.1]; ring, fun Q => h.2 Q⟩

/-! ## P4. Repetition code with five appended stabilized qubits -/

/-- Checks `Z₁Z₂`, `Z₂Z₃` and `Z₄, …, Z₈` (qubits `0..2` repetition code, `3..7` in `|0⟩`). -/
def rowsPad : List (List (PauliCoord 8)) :=
  [[.inr 0, .inr 1], [.inr 1, .inr 2], [.inr 3], [.inr 4], [.inr 5], [.inr 6], [.inr 7]]

theorem isotropic_Pad : rowSpace rowsPad ≤ normalizer (symplectic 8) (rowSpace rowsPad) :=
  rowSpace_isotropic_of rowsPad (by decide)

set_option maxHeartbeats 4000000 in
/-- Pair ambiguities: `1` if the pair meets the repetition block, `0` otherwise. -/
theorem pad_pair_rank (i j : Fin 8) (h : i ≠ j) :
    ambiguityRank rowsPad {i, j} = if i.val < 3 ∨ j.val < 3 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | decide +kernel

/-- Hessian entry: `H_ij = 2^{-d_{\{i,j\}}}` for `i ≠ j`, `H_ii = 0`. -/
def hessEntry (i j : Fin 8) : ℝ := if i = j then 0 else erasureScore (rowSpace rowsPad) {i, j}

/-- Twice the Hessian entry, as a natural number. -/
def hessNat (i j : Fin 8) : ℕ := if i = j then 0 else if i.val < 3 ∨ j.val < 3 then 1 else 2

theorem hessEntry_eq (i j : Fin 8) : hessEntry i j = (hessNat i j : ℝ) / 2 := by
  unfold hessEntry hessNat
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg h, erasureScore_eq_rank, pad_pair_rank i j h]
    split_ifs <;> norm_num

/-- The homogeneous weight-two part of the fidelity polynomial: `Σ_{i<j} 2^{-d_{\{i,j\}}} y_i y_j`. -/
def pairPoly (y : Fin 8 → ℝ) : ℝ :=
  ∑ i, ∑ j, (if i < j then erasureScore (rowSpace rowsPad) {i, j} else 0) * y i * y j

/-- The (constant) Hessian bilinear form `uᵀ H v`. -/
def hessForm (u v : Fin 8 → ℝ) : ℝ := ∑ i, ∑ j, hessEntry i j * u i * v j

/-- `P(y) = (1/2) yᵀ H y`, with `H` symmetric and zero on the diagonal: `H` is the Hessian. -/
theorem pairPoly_eq_half_hess (y : Fin 8 → ℝ) : pairPoly y = hessForm y y / 2 := by
  set g : Fin 8 → Fin 8 → ℝ := fun i j => erasureScore (rowSpace rowsPad) {i, j}
  have hsymm : ∀ i j, g i j = g j i := fun i j => by simp only [g, Finset.pair_comm]
  have hsplit : ∀ i j : Fin 8, hessEntry i j =
      (if i < j then g i j else 0) + (if j < i then g i j else 0) := by
    intro i j
    unfold hessEntry
    rcases lt_trichotomy i j with h | h | h
    · rw [if_neg (ne_of_lt h), if_pos h, if_neg (not_lt.mpr h.le)]
      simp [g]
    · subst h
      simp
    · rw [if_neg (ne_of_gt h), if_neg (not_lt.mpr h.le), if_pos h]
      simp [g]
  have hB : ∑ i : Fin 8, ∑ j : Fin 8, (if j < i then g i j else 0) * y i * y j =
      ∑ i : Fin 8, ∑ j : Fin 8, (if i < j then g i j else 0) * y i * y j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hsymm]
    ring
  unfold hessForm pairPoly
  simp_rw [hsplit, add_mul, Finset.sum_add_distrib, hB]
  ring

/-- Block vector: `a` on the repetition qubits `R = {0,1,2}`, `b` on the appended `A = {3..7}`. -/
def blockVec (a b : ℝ) : Fin 8 → ℝ := fun i => if i.val < 3 then a else b

theorem hessForm_block (a b c d : ℝ) :
    hessForm (blockVec a b) (blockVec c d) =
      3 * a * c + (15 / 2) * (a * d + b * c) + 20 * b * d := by
  unfold hessForm
  simp only [hessEntry_eq, hessNat, blockVec, Fin.sum_univ_eight]
  norm_num
  ring

/-- **P4(a).** Gram matrix of `H` on `1_R = blockVec 1 0`, `1_A = blockVec 0 1`:
`[[3, 15/2], [15/2, 20]]`, positive diagonal and determinant `15/4 > 0`. -/
theorem pad_gram :
    hessForm (blockVec 1 0) (blockVec 1 0) = 3 ∧
    hessForm (blockVec 1 0) (blockVec 0 1) = 15 / 2 ∧
    hessForm (blockVec 0 1) (blockVec 1 0) = 15 / 2 ∧
    hessForm (blockVec 0 1) (blockVec 0 1) = 20 ∧
    hessForm (blockVec 1 0) (blockVec 1 0) * hessForm (blockVec 0 1) (blockVec 0 1) -
      hessForm (blockVec 1 0) (blockVec 0 1) ^ 2 = 15 / 4 := by
  simp only [hessForm_block]
  norm_num

/-- **P4(b).** `H` is positive definite on the two-dimensional subspace
`{blockVec s t} = span{1_R, 1_A}`. -/
theorem pad_hess_posDef (s t : ℝ) (h : s ≠ 0 ∨ t ≠ 0) :
    0 < hessForm (blockVec s t) (blockVec s t) := by
  rw [hessForm_block]
  rcases h with hs | ht
  · by_cases ht : t = 0
    · subst ht
      have : 0 < s ^ 2 := by positivity
      nlinarith
    · have : 0 < t ^ 2 := by positivity
      nlinarith [sq_nonneg (s + 5 / 2 * t)]
  · have : 0 < t ^ 2 := by positivity
    nlinarith [sq_nonneg (s + 5 / 2 * t)]

theorem pairPoly_block (a b : ℝ) :
    pairPoly (blockVec a b) = (3 * a ^ 2 + 15 * a * b + 20 * b ^ 2) / 2 := by
  rw [pairPoly_eq_half_hess, hessForm_block]
  ring

/-- **P4(c).** `log P` is not concave on the open positive orthant: at
`y₁ = blockVec 1 2`, `y₂ = blockVec 4 1` one has `P(y₁) = 113/2`, `P(y₂) = 64`, and
`P((y₁+y₂)/2) = 60`, with `60² < (113/2)·64`. -/
theorem pad_not_logConcave :
    ¬ ConcaveOn ℝ {y : Fin 8 → ℝ | ∀ i, 0 < y i} (fun y => Real.log (pairPoly y)) := by
  intro hc
  have hy1 : blockVec 1 2 ∈ {y : Fin 8 → ℝ | ∀ i, 0 < y i} := by
    intro i
    unfold blockVec
    split_ifs <;> norm_num
  have hy2 : blockVec 4 1 ∈ {y : Fin 8 → ℝ | ∀ i, 0 < y i} := by
    intro i
    unfold blockVec
    split_ifs <;> norm_num
  have h := hc.2 hy1 hy2 (show (0:ℝ) ≤ 1 / 2 by norm_num) (show (0:ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hmid : (1 / 2 : ℝ) • blockVec 1 2 + (1 / 2 : ℝ) • blockVec 4 1 = blockVec (5 / 2) (3 / 2) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, blockVec]
    split_ifs <;> norm_num
  simp only [hmid, pairPoly_block, smul_eq_mul] at h
  norm_num at h
  have e1 : Real.log (113 / 2) + Real.log 64 = Real.log 3616 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have e2 : Real.log 60 + Real.log 60 = Real.log 3600 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hlt : Real.log 3600 < Real.log 3616 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

end QecPhysical.Stabilizer.PaperExamples

#print axioms QecPhysical.Stabilizer.PaperExamples.tail_bound
#print axioms QecPhysical.Stabilizer.PaperExamples.tail_mass_eq_binomial
#print axioms QecPhysical.Stabilizer.PaperExamples.repetition_k_eq_one
#print axioms QecPhysical.Stabilizer.PaperExamples.repetition_single_uncorrectable
#print axioms QecPhysical.Stabilizer.PaperExamples.repetition_single_average_fidelity
#print axioms QecPhysical.Stabilizer.PaperExamples.bell_good_on_normalizer
#print axioms QecPhysical.Stabilizer.PaperExamples.bell_good_counts
#print axioms QecPhysical.Stabilizer.PaperExamples.witness_count
#print axioms QecPhysical.Stabilizer.PaperExamples.bell4_ambiguities
#print axioms QecPhysical.Stabilizer.PaperExamples.bell4_bad_exists
#print axioms QecPhysical.Stabilizer.PaperExamples.bell4_witnesses_E13
#print axioms QecPhysical.Stabilizer.PaperExamples.bell4_witnesses_E34
#print axioms QecPhysical.Stabilizer.PaperExamples.xor_circuitMap
#print axioms QecPhysical.Stabilizer.PaperExamples.xor_latentCurve
#print axioms QecPhysical.Stabilizer.PaperExamples.xor_coefficients
#print axioms QecPhysical.Stabilizer.PaperExamples.xor_physical
#print axioms QecPhysical.Stabilizer.PaperExamples.pad_pair_rank
#print axioms QecPhysical.Stabilizer.PaperExamples.pairPoly_eq_half_hess
#print axioms QecPhysical.Stabilizer.PaperExamples.pad_gram
#print axioms QecPhysical.Stabilizer.PaperExamples.pad_hess_posDef
#print axioms QecPhysical.Stabilizer.PaperExamples.pad_not_logConcave
