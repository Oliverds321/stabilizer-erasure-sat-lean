import PhysicalBridge.BinaryPauli

/-! Trace orthogonality of the concrete binary Pauli representation. -/
noncomputable section
namespace QecPhysical.BinaryPauli
open scoped BigOperators ComplexOrder
open Matrix
open QecReliability.Binary

theorem bit_eq_one_of_ne_zero (b : Bit) (h : b ≠ 0) : b = 1 := by
  fin_cases b <;> simp_all

theorem character_sum_zero {n : ℕ} (z : Word n) (hz : z ≠ 0) :
    ∑ q : Word n, bitSign (wordDot z q) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  let t : Word n := Pi.single i 1
  have ht : wordDot z t = 1 := by
    simpa [wordDot, t, Pi.single_apply] using bit_eq_one_of_ne_zero (z i) hi
  have hshift := Fintype.sum_bijective (fun q : Word n => q+t)
    (Equiv.addRight t).bijective
    (fun q : Word n => bitSign (wordDot z (q+t)))
    (fun q : Word n => bitSign (wordDot z q)) (fun _ => rfl)
  change (∑ q : Word n, bitSign (wordDot z (q+t))) = ∑ q : Word n, bitSign (wordDot z q) at hshift
  simp only [wordDot_add_right, ht, bitSign_add, bitSign_one, mul_neg_one,
    Finset.sum_neg_distrib] at hshift
  have htwo : (2 : ℂ) * (∑ q : Word n, bitSign (wordDot z q)) = 0 := by
    linear_combination -hshift
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem character_sum {n : ℕ} (z : Word n) :
    ∑ q : Word n, bitSign (wordDot z q) = if z = 0 then (Fintype.card (Word n) : ℂ) else 0 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [hz, character_sum_zero z hz]

theorem pauli_trace {n : ℕ} (u : Pauli n) :
    (pauli u).trace = if u = 0 then (Fintype.card (Word n) : ℂ) else 0 := by
  by_cases hx : u.1 = 0
  · have h : (pauli u).trace = ∑ q : Word n, bitSign (wordDot u.2 q) := by
      simp [pauli, Matrix.trace, Matrix.diag, hx]
    rw [h, character_sum]
    have hu : u = 0 ↔ u.2 = 0 := by
      constructor
      · intro h; simp [h]
      · intro h; exact Prod.ext hx h
    simp only [hu]
  · have hu : u ≠ 0 := fun h => hx (congrArg Prod.fst h)
    have hi (i : Word n) : ¬ i = i+u.1 := by
      intro h
      apply hx
      exact add_left_cancel (show i+u.1 = i+0 by simpa using h.symm)
    simp [pauli, Matrix.trace, Matrix.diag, hi, hu]

theorem card_word (n : ℕ) : Fintype.card (Word n) = 2 ^ n := by
  simp [Word, Bit, ZMod.card]

theorem pauli_commute_iff {n : ℕ} (u v : Pauli n) :
    Commute (pauli u) (pauli v) ↔ symplectic n u v = 0 := by
  constructor
  · intro h
    have hv := congrFun (congrFun h.eq (u+v).1) 0
    rw [pauli_mul, pauli_mul, add_comm v u] at hv
    simp only [Matrix.smul_apply, pauli_origin, smul_eq_mul, mul_one] at hv
    apply (bitSign_eq_one_iff _).mp
    rw [symplectic_eq_dot, bitSign_add, wordDot_comm u.1 v.2, hv]
    exact bitSign_square _
  · exact pauli_commute_of_symplectic_zero u v

end QecPhysical.BinaryPauli
