import PointHardness
import EnumeratorExample

set_option autoImplicit false

/-!
# The distance as a minimum weight

The paper defines the distance of an isotropic `S` as the minimum Pauli weight of a normalizer
element outside the stabilizer. The Lean development (`PointHardness.IsDistance`) uses the least
size of an uncorrectable erased set. This module proves that the two agree.

Ingredients: for `x ∈ N \ S` there is `z ∈ N` with `symplectic n x z = 1` (double orthogonality
of the nondegenerate symplectic form: `S = N^⊥`), and `x` is supported on its own support,
whose size is `pauliWeight x`.
-/

noncomputable section

namespace QecPhysical.Stabilizer.Uncorrectable

open scoped BigOperators
open QecReliability
open QecReliability.Binary
open QecPhysical.Stabilizer.EnumeratorExample

variable {n : ℕ}

/-- The set of qubits on which `x` acts nontrivially. -/
def pauliSupport (x : Pauli n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x.1 i ≠ 0 ∨ x.2 i ≠ 0)

theorem card_pauliSupport (x : Pauli n) : (pauliSupport x).card = pauliWeight x := rfl

theorem mem_supported_pauliSupport (x : Pauli n) : x ∈ supported (pauliSupport x) := by
  intro i hi
  simp only [pauliSupport, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hi
  exact hi

theorem pauliWeight_le_card {x : Pauli n} {E : Finset (Fin n)} (hx : x ∈ supported E) :
    pauliWeight x ≤ E.card := by
  rw [← card_pauliSupport]
  apply Finset.card_le_card
  intro i hi
  by_contra hiE
  have h := hx i hiE
  simp only [pauliSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with h1 | h2
  · exact h1 h.1
  · exact h2 h.2

/-- A normalizer element outside an isotropic `S` pairs to one with some normalizer element. -/
theorem exists_pair_of_not_mem (S : Submodule Bit (Pauli n)) {x : Pauli n}
    (hxS : x ∉ S) : ∃ z ∈ normalizer (symplectic n) S, symplectic n x z = 1 := by
  have hSS : (symplectic n).orthogonal (normalizer (symplectic n) S) = S :=
    (symplectic n).orthogonal_orthogonal (symplectic_nondegenerate n) (symplectic_refl n) S
  rw [← hSS] at hxS
  have : ¬ ∀ z ∈ normalizer (symplectic n) S, symplectic n z x = 0 := by
    intro h
    exact hxS (fun z hz => h z hz)
  push Not at this
  obtain ⟨z, hz, hzx⟩ := this
  refine ⟨z, hz, ?_⟩
  rw [(symplectic_symm n).eq] at hzx
  have : ∀ b : Bit, b ≠ 0 → b = 1 := by decide
  exact this _ (by simpa using hzx)

/-- An erased set is uncorrectable iff it supports a normalizer element outside `S`. -/
theorem uncorrectable_iff_logical (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (E : Finset (Fin n)) :
    0 < ambiguity (symplectic n) S (supported E) ↔
      ∃ x ∈ normalizer (symplectic n) S, x ∈ supported E ∧ x ∉ S := by
  rw [uncorrectable_iff_certificate S hS E]
  constructor
  · rintro ⟨x, ⟨hxN, hxE⟩, z, hz, hxz⟩
    refine ⟨x, hxN, hxE, fun hxS => ?_⟩
    have h0 : symplectic n x z = 0 := hz x hxS
    rw [h0] at hxz
    exact zero_ne_one hxz
  · rintro ⟨x, hxN, hxE, hxS⟩
    obtain ⟨z, hz, hxz⟩ := exists_pair_of_not_mem S hxS
    exact ⟨x, ⟨hxN, hxE⟩, z, hz, hxz⟩

/-- **The distance is the minimum weight of a logical operator.** For isotropic `S`, the least
size `d` of an uncorrectable erased set is the minimum Pauli weight of a normalizer element
outside `S`. -/
theorem isDistance_iff_minWeight (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (d : ℕ) :
    IsDistance S d ↔
      (∃ x ∈ normalizer (symplectic n) S, x ∉ S ∧ pauliWeight x = d) ∧
        ∀ x ∈ normalizer (symplectic n) S, x ∉ S → d ≤ pauliWeight x := by
  have hmin : ∀ x ∈ normalizer (symplectic n) S, x ∉ S →
      0 < ambiguity (symplectic n) S (supported (pauliSupport x)) := fun x hxN hxS =>
    (uncorrectable_iff_logical S hS _).mpr ⟨x, hxN, mem_supported_pauliSupport x, hxS⟩
  constructor
  · rintro ⟨hlt, E, hE, hpos⟩
    have hlow : ∀ x ∈ normalizer (symplectic n) S, x ∉ S → d ≤ pauliWeight x := by
      intro x hxN hxS
      by_contra h
      exact hlt (pauliSupport x) (by rw [card_pauliSupport]; omega) (hmin x hxN hxS)
    obtain ⟨x, hxN, hxE, hxS⟩ := (uncorrectable_iff_logical S hS E).mp hpos
    have := pauliWeight_le_card hxE
    exact ⟨⟨x, hxN, hxS, le_antisymm (hE ▸ this) (hlow x hxN hxS)⟩, hlow⟩
  · rintro ⟨⟨x0, hx0N, hx0S, hx0w⟩, hlow⟩
    refine ⟨fun E hE hpos => ?_, pauliSupport x0, by rw [card_pauliSupport, hx0w],
      hmin x0 hx0N hx0S⟩
    obtain ⟨x, hxN, hxE, hxS⟩ := (uncorrectable_iff_logical S hS E).mp hpos
    have h1 := pauliWeight_le_card hxE
    have h2 := hlow x hxN hxS
    omega

end QecPhysical.Stabilizer.Uncorrectable

#print axioms QecPhysical.Stabilizer.Uncorrectable.isDistance_iff_minWeight
#print axioms QecPhysical.Stabilizer.Uncorrectable.uncorrectable_iff_logical
