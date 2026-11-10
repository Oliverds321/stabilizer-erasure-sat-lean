import QecReliability.CodeCore
import QecReliability.Certificates
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring

/-! The concrete binary symplectic space and coordinate erasures. -/

noncomputable section

namespace QecReliability.Binary

open Module LinearMap
open LinearMap (BilinForm)
open scoped BigOperators

abbrev Pauli (n : ℕ) := (Fin n → Bit) × (Fin n → Bit)

def symplectic (n : ℕ) : BilinForm Bit (Pauli n) :=
  LinearMap.mk₂ Bit (fun x y => ∑ i, (x.1 i * y.2 i + x.2 i * y.1 i))
    (by
      intro x x' y
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro c x y
      change (∑ i, ((c * x.1 i) * y.2 i + (c * x.2 i) * y.1 i)) =
        c * ∑ i, (x.1 i * y.2 i + x.2 i * y.1 i)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro x y y'
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro c x y
      change (∑ i, (x.1 i * (c * y.2 i) + x.2 i * (c * y.1 i))) =
        c * ∑ i, (x.1 i * y.2 i + x.2 i * y.1 i)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

theorem symplectic_apply {n : ℕ} (x y : Pauli n) :
    symplectic n x y = ∑ i, (x.1 i * y.2 i + x.2 i * y.1 i) := rfl

theorem symplectic_symm (n : ℕ) : (symplectic n).IsSymm := by
  constructor
  intro x y
  rw [symplectic_apply, symplectic_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem symplectic_refl (n : ℕ) : (symplectic n).IsRefl :=
  (symplectic_symm n).isRefl

theorem symplectic_alt (n : ℕ) : (symplectic n).IsAlt := by
  intro x
  rw [symplectic_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm (x.2 i) (x.1 i), CharTwo.add_self_eq_zero]

def xUnit {n : ℕ} (i : Fin n) : Pauli n := (Pi.single i 1, 0)
def zUnit {n : ℕ} (i : Fin n) : Pauli n := (0, Pi.single i 1)

@[simp] theorem symplectic_xUnit {n : ℕ} (x : Pauli n) (i : Fin n) :
    symplectic n x (xUnit i) = x.2 i := by
  simp [symplectic_apply, xUnit, Pi.single_apply]

@[simp] theorem symplectic_zUnit {n : ℕ} (x : Pauli n) (i : Fin n) :
    symplectic n x (zUnit i) = x.1 i := by
  simp [symplectic_apply, zUnit, Pi.single_apply]

theorem symplectic_nondegenerate (n : ℕ) : (symplectic n).Nondegenerate := by
  apply (symplectic_refl n).nondegenerate_iff_separatingLeft.mpr
  intro x hx
  apply Prod.ext
  · funext i
    simpa using hx (zUnit i)
  · funext i
    simpa using hx (xUnit i)

/-- Both Pauli coordinates vanish off the erased set. -/
def supported {n : ℕ} (E : Finset (Fin n)) : Submodule Bit (Pauli n) where
  carrier := {x | ∀ i, i ∉ E → x.1 i = 0 ∧ x.2 i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [(hx i hi).1, (hx i hi).2, (hy i hi).1, (hy i hi).2]
  smul_mem' := by
    intro c x hx i hi
    simp [(hx i hi).1, (hx i hi).2]

@[simp] theorem mem_supported {n : ℕ} (E : Finset (Fin n)) (x : Pauli n) :
    x ∈ supported E ↔ ∀ i, i ∉ E → x.1 i = 0 ∧ x.2 i = 0 := Iff.rfl

theorem supported_mono {n : ℕ} {E E' : Finset (Fin n)} (h : E ⊆ E') :
    supported E ≤ supported E' := by
  intro x hx i hi
  exact hx i (fun hmem => hi (h hmem))

theorem xUnit_mem_supported {n : ℕ} {E : Finset (Fin n)} {i : Fin n} (hi : i ∈ E) :
    xUnit i ∈ supported E := by
  intro j hj
  have hji : j ≠ i := fun h => hj (h ▸ hi)
  simp [xUnit, hji]

theorem zUnit_mem_supported {n : ℕ} {E : Finset (Fin n)} {i : Fin n} (hi : i ∈ E) :
    zUnit i ∈ supported E := by
  intro j hj
  have hji : j ≠ i := fun h => hj (h ▸ hi)
  simp [zUnit, hji]

theorem orthogonal_supported {n : ℕ} (E : Finset (Fin n)) :
    (symplectic n).orthogonal (supported E) = supported Eᶜ := by
  ext z
  constructor
  · intro hz i hi
    have hiE : i ∈ E := by simpa using hi
    have hx := hz (xUnit i) (xUnit_mem_supported hiE)
    have hzz := hz (zUnit i) (zUnit_mem_supported hiE)
    change symplectic n (xUnit i) z = 0 at hx
    change symplectic n (zUnit i) z = 0 at hzz
    rw [(symplectic_symm n).eq] at hx hzz
    exact ⟨by simpa using hzz, by simpa using hx⟩
  · intro hz x hx
    change symplectic n x z = 0
    rw [symplectic_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ E
    · have hzi := hz i (by simpa using hi)
      simp [hzi.1, hzi.2]
    · have hxi := hx i hi
      simp [hxi.1, hxi.2]

@[simp] theorem supported_empty (n : ℕ) : supported (∅ : Finset (Fin n)) = ⊥ := by
  ext x
  constructor
  · intro h
    exact Prod.ext (funext fun i => (h i (by simp)).1)
      (funext fun i => (h i (by simp)).2)
  · intro h
    rw [Submodule.mem_bot] at h
    simp [h]

@[simp] theorem supported_univ (n : ℕ) : supported (Finset.univ : Finset (Fin n)) = ⊤ := by
  ext x
  simp [mem_supported]

theorem good_iff_cleaning {n : ℕ} (S : Submodule Bit (Pauli n))
    (E : Finset (Fin n)) (z : Pauli n) :
    Good (F := Bit) (symplectic n) S (supported E) z ↔ z ∈ S ⊔ supported Eᶜ := by
  simp only [Good, orthogonal_supported]

theorem bad_iff_not_cleaning {n : ℕ} (S : Submodule Bit (Pauli n))
    (E : Finset (Fin n)) (z : Pauli n) :
    (∃ x ∈ normalizer (F := Bit) (symplectic n) S ⊓ supported E, symplectic n x z = 1) ↔
      z ∉ S ⊔ supported Eᶜ := by
  rw [← good_iff_cleaning]
  exact bad_iff_not_good (F := Bit) _ (symplectic_nondegenerate n) (symplectic_refl n) S (supported E) z

theorem good_fraction_binary {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S) (E : Finset (Fin n)) :
    (Nat.card (goodSpace (F := Bit) (symplectic n) S (supported E)) : ℚ) /
      Nat.card (normalizer (F := Bit) (symplectic n) S) =
      (2 ^ ambiguity (F := Bit) (symplectic n) S (supported E) : ℚ)⁻¹ := by
  simpa [Nat.card_eq_fintype_card, ZMod.card] using
    good_fraction (F := Bit) (symplectic n) (symplectic_nondegenerate n) (symplectic_refl n)
      S (supported E) hS

theorem ambiguity_erasure_mono {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S) {E E' : Finset (Fin n)} (h : E ⊆ E') :
    ambiguity (F := Bit) (symplectic n) S (supported E) ≤ ambiguity (F := Bit) (symplectic n) S (supported E') :=
  ambiguity_mono (F := Bit) _ (symplectic_nondegenerate n) (symplectic_refl n) S _ _ hS
    (supported_mono h)

@[simp] theorem finrank_pauli (n : ℕ) : finrank Bit (Pauli n) = 2 * n := by
  simp [Pauli, Module.finrank_prod, two_mul]

theorem finrank_normalizer {n : ℕ} (S : Submodule Bit (Pauli n)) :
    finrank Bit (normalizer (F := Bit) (symplectic n) S) = 2 * n - finrank Bit S := by
  calc
    _ = finrank Bit (Pauli n) - finrank Bit S :=
      (symplectic n).finrank_orthogonal (symplectic_nondegenerate n) S
    _ = _ := by rw [finrank_pauli]

theorem isotropic_finrank_le {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S) : finrank Bit S ≤ n := by
  have h := Submodule.finrank_mono hS
  have hs := Submodule.finrank_le S
  rw [finrank_pauli] at hs
  rw [finrank_normalizer] at h
  omega

theorem ambiguity_empty {n : ℕ} (S : Submodule Bit (Pauli n)) :
    ambiguity (F := Bit) (symplectic n) S (supported ∅) = 0 := by
  rw [supported_empty, ambiguity_bot]

theorem ambiguity_full {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S) :
    ambiguity (F := Bit) (symplectic n) S (supported Finset.univ) =
      2 * (n - finrank Bit S) := by
  rw [supported_univ, ambiguity_top, finrank_normalizer]
  have h := isotropic_finrank_le S hS
  omega

theorem normalizer_card {n : ℕ} (S : Submodule Bit (Pauli n)) :
    Nat.card (normalizer (F := Bit) (symplectic n) S) = 2 ^ (2 * n - finrank Bit S) := by
  rw [Module.natCard_eq_pow_finrank (K := Bit), finrank_normalizer]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem counted_good_fraction {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S) (E : Finset (Fin n)) :
    (Nat.card {z : normalizer (F := Bit) (symplectic n) S //
      (z : Pauli n) ∈ S ⊔ supported Eᶜ} : ℚ) /
      Nat.card (normalizer (F := Bit) (symplectic n) S) =
      (2 ^ ambiguity (F := Bit) (symplectic n) S (supported E) : ℚ)⁻¹ := by
  simpa only [Good, orthogonal_supported, Nat.card_eq_fintype_card, ZMod.card,
    Nat.cast_ofNat] using
    good_card_fraction (F := Bit) (symplectic n) (symplectic_nondegenerate n)
      (symplectic_refl n) S (supported E) hS

end QecReliability.Binary
