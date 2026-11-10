import HybridEstimator

set_option autoImplicit false

/-!
# Symmetry reduction and the stratified split of the hybrid erasure estimator

P1. A qubit permutation acts on Pauli vectors, preserves the symplectic form and maps
    `supported E` onto `supported (σ E)`.
P2. If the permutation preserves the stabilizer space then `d_{σ E} = d_E`; minimal
    uncorrectable sets are mapped to minimal uncorrectable sets.
P3. Representative search: for a group of such permutations and a set of qubits meeting
    every orbit, every minimal uncorrectable set is the image, under a group element, of a
    minimal uncorrectable set of the same size through a representative.
R1. Stratified split: a layer sum is the Karp–Luby sum over any listed family plus the sum
    over the sets containing no listed set; when the list contains all minimal uncorrectable
    sets of size `≤ w`, every minimal uncorrectable subset of a remainder set is larger than `w`.
-/

noncomputable section

namespace QecPhysical.Stabilizer.Uncorrectable

open scoped BigOperators
open Module
open QecReliability
open QecReliability.Binary

variable {n : ℕ}

/-! ## P1. Qubit permutations -/

/-- The action of a qubit permutation on Pauli vectors: the content of qubit `i` moves to
qubit `σ i`. -/
def permute (σ : Equiv.Perm (Fin n)) : Pauli n ≃ₗ[Bit] Pauli n where
  toFun x := (fun i => x.1 (σ.symm i), fun i => x.2 (σ.symm i))
  invFun x := (fun i => x.1 (σ i), fun i => x.2 (σ i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Prod.ext (funext fun i => by simp) (funext fun i => by simp)
  right_inv x := Prod.ext (funext fun i => by simp) (funext fun i => by simp)

@[simp] theorem permute_fst (σ : Equiv.Perm (Fin n)) (x : Pauli n) (i : Fin n) :
    (permute σ x).1 i = x.1 (σ.symm i) := rfl

@[simp] theorem permute_snd (σ : Equiv.Perm (Fin n)) (x : Pauli n) (i : Fin n) :
    (permute σ x).2 i = x.2 (σ.symm i) := rfl

@[simp] theorem permute_symm_fst (σ : Equiv.Perm (Fin n)) (x : Pauli n) (i : Fin n) :
    ((permute σ).symm x).1 i = x.1 (σ i) := rfl

@[simp] theorem permute_symm_snd (σ : Equiv.Perm (Fin n)) (x : Pauli n) (i : Fin n) :
    ((permute σ).symm x).2 i = x.2 (σ i) := rfl

/-- The image of a subspace under a qubit permutation. -/
def permuteSub (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n)) : Submodule Bit (Pauli n) :=
  S.map (permute σ : Pauli n →ₗ[Bit] Pauli n)

theorem mem_permuteSub (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n)) (z : Pauli n) :
    z ∈ permuteSub σ S ↔ (permute σ).symm z ∈ S := by
  unfold permuteSub
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨(permute σ).symm z, h, by simp⟩

theorem symplectic_permute (σ : Equiv.Perm (Fin n)) (x y : Pauli n) :
    symplectic n (permute σ x) (permute σ y) = symplectic n x y := by
  simp only [symplectic_apply, permute_fst, permute_snd]
  exact Equiv.sum_comp σ.symm (fun i => x.1 i * y.2 i + x.2 i * y.1 i)

theorem symplectic_permute_symm (σ : Equiv.Perm (Fin n)) (x y : Pauli n) :
    symplectic n ((permute σ).symm x) y = symplectic n x (permute σ y) := by
  rw [← symplectic_permute σ, LinearEquiv.apply_symm_apply]

theorem permuteSub_supported (σ : Equiv.Perm (Fin n)) (E : Finset (Fin n)) :
    permuteSub σ (supported E) = supported (E.map σ.toEmbedding) := by
  ext z
  rw [mem_permuteSub]
  simp only [mem_supported, Finset.mem_map, Equiv.coe_toEmbedding, permute_symm_fst,
    permute_symm_snd]
  constructor
  · intro h i hi
    have hi' : σ.symm i ∉ E := fun hmem => hi ⟨σ.symm i, hmem, by simp⟩
    simpa using h (σ.symm i) hi'
  · intro h i hi
    exact h (σ i) (by
      rintro ⟨j, hj, hji⟩
      exact hi (σ.injective hji ▸ hj))

theorem permuteSub_normalizer (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n)) :
    permuteSub σ (normalizer (symplectic n) S) = normalizer (symplectic n) (permuteSub σ S) := by
  ext z
  rw [mem_permuteSub]
  simp only [normalizer, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h x hx
    have := h ((permute σ).symm x) ((mem_permuteSub σ S x).mp hx)
    rwa [symplectic_permute_symm, LinearEquiv.apply_symm_apply] at this
  · intro h x hx
    have hx' : permute σ x ∈ permuteSub σ S := (mem_permuteSub σ S _).mpr (by simpa using hx)
    have := h (permute σ x) hx'
    rwa [← symplectic_permute σ, LinearEquiv.apply_symm_apply]

theorem permuteSub_inf (σ : Equiv.Perm (Fin n)) (A B : Submodule Bit (Pauli n)) :
    permuteSub σ (A ⊓ B) = permuteSub σ A ⊓ permuteSub σ B := by
  ext z
  simp only [mem_permuteSub, Submodule.mem_inf]

theorem finrank_permuteSub (σ : Equiv.Perm (Fin n)) (A : Submodule Bit (Pauli n)) :
    finrank Bit (permuteSub σ A) = finrank Bit A :=
  LinearEquiv.finrank_map_eq (permute σ) A

/-! ## P2. Invariance of the ambiguity exponent -/

/-- `d_{σE}` for the permuted code equals `d_E`. -/
theorem ambiguity_permuteSub (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n))
    (E : Finset (Fin n)) :
    ambiguity (symplectic n) (permuteSub σ S) (supported (E.map σ.toEmbedding)) =
      ambiguity (symplectic n) S (supported E) := by
  unfold ambiguity localized
  rw [← permuteSub_supported, ← permuteSub_normalizer, ← permuteSub_inf, ← permuteSub_inf,
    finrank_permuteSub, finrank_permuteSub]

/-- **P2.** A qubit permutation that preserves the stabilizer space preserves `d_E`. -/
theorem ambiguity_map_of_preserved (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n))
    (hσ : permuteSub σ S = S) (E : Finset (Fin n)) :
    ambiguity (symplectic n) S (supported (E.map σ.toEmbedding)) =
      ambiguity (symplectic n) S (supported E) := by
  have h := ambiguity_permuteSub σ S E
  rwa [hσ] at h

theorem erasureScore_map_of_preserved (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n))
    (hσ : permuteSub σ S = S) (E : Finset (Fin n)) :
    erasureScore S (E.map σ.toEmbedding) = erasureScore S E := by
  unfold erasureScore
  rw [ambiguity_map_of_preserved σ S hσ]

theorem map_symm_map (σ : Equiv.Perm (Fin n)) (M : Finset (Fin n)) :
    (M.map σ.symm.toEmbedding).map σ.toEmbedding = M := by
  ext j
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    simpa using hb
  · intro hj
    exact ⟨σ.symm j, ⟨j, hj, rfl⟩, by simp⟩

/-- **P2, minimal sets.** The image of a minimal uncorrectable set is minimal uncorrectable. -/
theorem isMinimalUncorrectable_map (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n))
    (hσ : permuteSub σ S = S) {M : Finset (Fin n)} (hM : IsMinimalUncorrectable S M) :
    IsMinimalUncorrectable S (M.map σ.toEmbedding) := by
  refine ⟨by rw [ambiguity_map_of_preserved σ S hσ]; exact hM.1, ?_⟩
  intro M' hM'
  rw [← map_symm_map σ M'] at hM' ⊢
  rw [ambiguity_map_of_preserved σ S hσ]
  exact hM.2 _ (Finset.map_ssubset_map.mp hM')

/-! ## P3. Search through orbit representatives -/

theorem IsMinimalUncorrectable.nonempty {S : Submodule Bit (Pauli n)} {M : Finset (Fin n)}
    (hM : IsMinimalUncorrectable S M) : M.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  have h := hM.1
  rw [ambiguity_empty] at h
  exact lt_irrefl _ h

/-- **P3.** Let `G` be a group of qubit permutations preserving the stabilizer space and
let `reps` meet every `G`-orbit of qubits. Then every minimal uncorrectable set is the image
under an element of `G` of a minimal uncorrectable set of the same size that contains a
representative. Hence the list of all minimal uncorrectable sets of a given size is the
`G`-closure of those through a representative. -/
theorem minimal_eq_image_through_representative (S : Submodule Bit (Pauli n))
    (G : Subgroup (Equiv.Perm (Fin n))) (hG : ∀ σ ∈ G, permuteSub σ S = S)
    (reps : Finset (Fin n)) (hreps : ∀ i : Fin n, ∃ σ ∈ G, σ i ∈ reps)
    {M : Finset (Fin n)} (hM : IsMinimalUncorrectable S M) :
    ∃ σ ∈ G, ∃ M' : Finset (Fin n), IsMinimalUncorrectable S M' ∧ M'.card = M.card ∧
      (∃ q ∈ reps, q ∈ M') ∧ M'.map σ.toEmbedding = M := by
  obtain ⟨i, hi⟩ := hM.nonempty
  obtain ⟨τ, hτ, hq⟩ := hreps i
  refine ⟨τ⁻¹, G.inv_mem hτ, M.map τ.toEmbedding, isMinimalUncorrectable_map τ S (hG τ hτ) hM,
    Finset.card_map _, ⟨τ i, hq, Finset.mem_map_of_mem _ hi⟩, ?_⟩
  have h := map_symm_map τ⁻¹ M
  rwa [show (τ⁻¹ : Equiv.Perm (Fin n)).symm = τ from rfl] at h

/-- The closure step: the image of a listed minimal set under a group element is again a
minimal uncorrectable set of the same size, so adding whole orbits adds no wrong set. -/
theorem orbit_isMinimalUncorrectable (S : Submodule Bit (Pauli n))
    (G : Subgroup (Equiv.Perm (Fin n))) (hG : ∀ σ ∈ G, permuteSub σ S = S)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ G) {M : Finset (Fin n)}
    (hM : IsMinimalUncorrectable S M) :
    IsMinimalUncorrectable S (M.map σ.toEmbedding) ∧ (M.map σ.toEmbedding).card = M.card :=
  ⟨isMinimalUncorrectable_map σ S (hG σ hσ) hM, Finset.card_map _⟩

/-! ## R1. Stratified split -/

/-- **R1.** For any listed family and any layer, the layer sum is the Karp–Luby sum over the
family plus the sum over the sets that contain no listed set. -/
theorem sum_eq_karpLuby_add_remainder {α : Type*} [DecidableEq α]
    (terms layer : Finset (Finset α)) (g : Finset α → ℝ) :
    ∑ E ∈ layer, g E =
      (∑ M ∈ terms, ∑ E ∈ layer.filter (fun E => M ⊆ E),
        g E / ((terms.filter (fun M' => M' ⊆ E)).card : ℝ)) +
      ∑ E ∈ layer.filter (fun E => ¬ ∃ M ∈ terms, M ⊆ E), g E := by
  rw [← sum_union_eq_karpLuby, Finset.sum_filter_add_sum_filter_not]

/-- **R1, remainder.** If the list contains every minimal uncorrectable set of size `≤ w`,
then every minimal uncorrectable subset of a set containing no listed set has size `> w`. -/
theorem remainder_minimal_card (S : Submodule Bit (Pauli n)) (w : ℕ)
    (mins : Finset (Finset (Fin n)))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {E : Finset (Fin n)} (hE : ¬ ∃ M ∈ mins, M ⊆ E)
    {M : Finset (Fin n)} (hM : IsMinimalUncorrectable S M) (hME : M ⊆ E) : w < M.card := by
  by_contra h
  exact hE ⟨M, hcover M hM (not_lt.mp h), hME⟩

/-- **R1, remainder below the bound.** A remainder set of size `≤ w` is correctable, so the
remainder vanishes on layers `j ≤ w`. -/
theorem remainder_correctable (S : Submodule Bit (Pauli n)) (w : ℕ)
    (mins : Finset (Finset (Fin n)))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {E : Finset (Fin n)} (hE : ¬ ∃ M ∈ mins, M ⊆ E) (hcard : E.card ≤ w) :
    ambiguity (symplectic n) S (supported E) = 0 := by
  by_contra hne
  obtain ⟨M, hME, hmin⟩ := exists_minimalUncorrectable_subset S E (Nat.pos_of_ne_zero hne)
  have := remainder_minimal_card S w mins hcover hE hmin hME
  have := Finset.card_le_card hME
  omega

end QecPhysical.Stabilizer.Uncorrectable

#print axioms QecPhysical.Stabilizer.Uncorrectable.symplectic_permute
#print axioms QecPhysical.Stabilizer.Uncorrectable.permuteSub_supported
#print axioms QecPhysical.Stabilizer.Uncorrectable.permuteSub_normalizer
#print axioms QecPhysical.Stabilizer.Uncorrectable.ambiguity_permuteSub
#print axioms QecPhysical.Stabilizer.Uncorrectable.ambiguity_map_of_preserved
#print axioms QecPhysical.Stabilizer.Uncorrectable.erasureScore_map_of_preserved
#print axioms QecPhysical.Stabilizer.Uncorrectable.isMinimalUncorrectable_map
#print axioms QecPhysical.Stabilizer.Uncorrectable.minimal_eq_image_through_representative
#print axioms QecPhysical.Stabilizer.Uncorrectable.orbit_isMinimalUncorrectable
#print axioms QecPhysical.Stabilizer.Uncorrectable.sum_eq_karpLuby_add_remainder
#print axioms QecPhysical.Stabilizer.Uncorrectable.remainder_minimal_card
#print axioms QecPhysical.Stabilizer.Uncorrectable.remainder_correctable
