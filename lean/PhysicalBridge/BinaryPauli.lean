import PhysicalBridge.PauliTensor
import QecReliability.BinarySymplectic

/-! Concrete Pauli matrices on the same binary symplectic space as M12. -/
noncomputable section
namespace QecPhysical.BinaryPauli
open scoped BigOperators ComplexOrder
open Matrix
open QecReliability.Binary

abbrev Word (n : ℕ) := Fin n → Bit

def bitSign (b : Bit) : ℂ := if b = 0 then 1 else -1

@[simp] theorem bitSign_zero : bitSign 0 = 1 := by simp [bitSign]
@[simp] theorem bitSign_one : bitSign 1 = -1 := by norm_num [bitSign]

theorem bitSign_add (a b : Bit) : bitSign (a+b) = bitSign a * bitSign b := by
  fin_cases a <;> fin_cases b <;> norm_num [bitSign]
  exact CharTwo.two_eq_zero

@[simp] theorem bitSign_square (b : Bit) : bitSign b * bitSign b = 1 := by
  fin_cases b <;> norm_num [bitSign]

@[simp] theorem bitSign_star (b : Bit) : star (bitSign b) = bitSign b := by
  by_cases h : b = 0 <;> simp [bitSign, h]

@[simp] theorem bitSign_eq_one_iff (b : Bit) : bitSign b = 1 ↔ b = 0 := by
  fin_cases b <;> norm_num [bitSign]

def wordDot {n : ℕ} (x y : Word n) : Bit := ∑ i, x i * y i

@[simp] theorem wordDot_zero_right {n : ℕ} (x : Word n) : wordDot x 0 = 0 := by simp [wordDot]
@[simp] theorem wordDot_zero_left {n : ℕ} (x : Word n) : wordDot 0 x = 0 := by simp [wordDot]

theorem wordDot_add_right {n : ℕ} (x y z : Word n) :
    wordDot x (y+z) = wordDot x y + wordDot x z := by
  simp [wordDot, mul_add, Finset.sum_add_distrib]

theorem wordDot_add_left {n : ℕ} (x y z : Word n) :
    wordDot (x+y) z = wordDot x z + wordDot y z := by
  simp [wordDot, add_mul, Finset.sum_add_distrib]

theorem wordDot_comm {n : ℕ} (x y : Word n) : wordDot x y = wordDot y x := by
  simp [wordDot, mul_comm]

theorem symplectic_eq_dot {n : ℕ} (u v : Pauli n) :
    symplectic n u v = wordDot u.1 v.2 + wordDot u.2 v.1 := by
  simp [symplectic_apply, wordDot, Finset.sum_add_distrib]

@[simp] theorem word_add_self {n : ℕ} (x : Word n) : x+x=0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

@[simp] theorem pauliLabel_add_self {n : ℕ} (u : Pauli n) : u+u=0 := by
  apply Prod.ext <;> exact word_add_self _

def pauli {n : ℕ} (u : Pauli n) : Square (Word n) :=
  fun i j => if i = j + u.1 then bitSign (wordDot u.2 j) else 0

@[simp] theorem pauli_zero (n : ℕ) : pauli (0 : Pauli n) = 1 := by
  ext i j
  simp [pauli, Matrix.one_apply]

@[simp] theorem pauli_origin {n : ℕ} (u : Pauli n) : pauli u u.1 0 = 1 := by
  simp [pauli]

theorem pauli_mul {n : ℕ} (u v : Pauli n) :
    pauli u * pauli v = bitSign (wordDot u.2 v.1) • pauli (u+v) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (j+v.1)]
  · simp [pauli, wordDot_add_right, wordDot_add_left, bitSign_add,
      add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]
  · intro k _ hk
    simp [pauli, hk]
  · simp

theorem pauli_commutation {n : ℕ} (u v : Pauli n) :
    pauli u * pauli v = bitSign (symplectic n u v) • (pauli v * pauli u) := by
  rw [pauli_mul, pauli_mul, symplectic_eq_dot, bitSign_add,
    wordDot_comm u.1 v.2, add_comm v u, smul_smul]
  congr 1
  calc
    bitSign (wordDot u.2 v.1) =
        (bitSign (wordDot v.2 u.1) * bitSign (wordDot v.2 u.1)) * bitSign (wordDot u.2 v.1) := by simp
    _ = (bitSign (wordDot v.2 u.1) * bitSign (wordDot u.2 v.1)) * bitSign (wordDot v.2 u.1) := by ring

theorem pauli_commute_of_symplectic_zero {n : ℕ} (u v : Pauli n)
    (h : symplectic n u v = 0) : Commute (pauli u) (pauli v) := by
  exact (pauli_commutation u v).trans (by rw [h, bitSign_zero, one_smul])

theorem pauli_adjoint {n : ℕ} (u : Pauli n) :
    (pauli u)ᴴ = bitSign (wordDot u.2 u.1) • pauli u := by
  ext i j
  change star (pauli u j i) = bitSign (wordDot u.2 u.1) * pauli u i j
  have hi : j = i + u.1 ↔ i = j + u.1 := by
    constructor <;> intro h <;> rw [h] <;> simp [add_assoc]
  by_cases h : i = j + u.1
  · subst i
    simp [pauli, wordDot_add_right, bitSign_add,
      add_assoc, star_mul', mul_comm]
  · simp [pauli, hi, h]

theorem pauli_unitary {n : ℕ} (u : Pauli n) : (pauli u)ᴴ * pauli u = 1 := by
  rw [pauli_adjoint, Matrix.smul_mul, pauli_mul, smul_smul]
  simp

end QecPhysical.BinaryPauli
