import PhysicalBridge.StabilizerEncoding

/-! Ordered products of binary powers. The ambient matrix algebra need not
be commutative; the required cross-commutation is explicit. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix
open QecReliability.Binary
open QecPhysical.BinaryPauli

def binaryPower {α : Type*} [One α] (A : α) (b : Bit) : α := if b = 0 then 1 else A

theorem binaryPower_add {α : Type*} [Monoid α] (A : α) (hA : A*A=1) (b c : Bit) :
    binaryPower A (b+c) = binaryPower A b * binaryPower A c := by
  fin_cases b <;> fin_cases c <;> norm_num [binaryPower, hA]
  simp [CharTwo.two_eq_zero]

theorem binaryPower_commute {α : Type*} [Monoid α] (A B : α) (h : Commute A B)
    (b c : Bit) : Commute (binaryPower A b) (binaryPower B c) := by
  unfold binaryPower
  split_ifs <;> first | exact Commute.one_left _ | exact Commute.one_right _ | exact h

theorem list_product_mul {α M : Type*} [Monoid M] (l : List α) (f g : α → M)
    (h : ∀ i j, Commute (f i) (g j)) :
    (l.map (fun i => f i * g i)).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    have hc : Commute (g i) (l.map f).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact (h j i).symm
    simp only [mul_assoc]
    rw [← mul_assoc (g i), hc.eq, mul_assoc]

theorem list_product_unitary {α : Type*} {n : ℕ} (l : List α)
    (f : α → Square (Word n)) (h : ∀ i, (f i)ᴴ * f i = 1) :
    (l.map f).prodᴴ * (l.map f).prod = 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.conjTranspose_mul]
    calc
      _ = (l.map f).prodᴴ * ((f i)ᴴ * f i) * (l.map f).prod := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, ih]

theorem binaryPower_pauli_phase {n : ℕ} (u : Pauli n) (b : Bit) :
    ∃ c : ℂ, binaryPower (hermitianPauli u) b = c • pauli (b • u) := by
  by_cases hb : b=0
  · refine ⟨1, ?_⟩
    simp [hb, binaryPower]
  · have hb1 := bit_eq_one_of_ne_zero b hb
    refine ⟨hermitianPhase (wordDot u.2 u.1), ?_⟩
    simp [hb1, binaryPower, hermitianPauli]

theorem list_product_pauli_phase {α : Type*} {n : ℕ} (l : List α)
    (f : α → Square (Word n)) (u : α → Pauli n)
    (h : ∀ i, ∃ c : ℂ, f i = c • pauli (u i)) :
    ∃ c : ℂ, (l.map f).prod = c • pauli (l.map u).sum := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons i l ih =>
    obtain ⟨a, ha⟩ := h i
    obtain ⟨b, hb⟩ := ih
    refine ⟨(a*b) * bitSign (wordDot (u i).2 (l.map u).sum.1), ?_⟩
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ha, hb,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauli_mul]
    congr 1
    ring

end QecPhysical.Stabilizer
