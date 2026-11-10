import QecReliability.SymbolAlignment

/-! Least dyadic lengths and exact padding bounds. This is length arithmetic,
not a polynomial-uniform construction of codes or expanders at those lengths. -/
noncomputable section
namespace QecReliability.CodeHash

theorem dyadic_exists (L₀ M : ℕ) (h₀ : 0 < L₀) : ∃ e, M ≤ L₀ * 2 ^ e := by
  refine ⟨M, (Nat.lt_two_pow_self (n := M)).le.trans ?_⟩
  exact Nat.le_mul_of_pos_left _ h₀

def dyadicIndex (L₀ M : ℕ) (h₀ : 0 < L₀) : ℕ := Nat.find (dyadic_exists L₀ M h₀)
def dyadicLength (L₀ M : ℕ) (h₀ : 0 < L₀) : ℕ := L₀ * 2 ^ dyadicIndex L₀ M h₀

theorem dyadicLength_ge (L₀ M : ℕ) (h₀ : 0 < L₀) : M ≤ dyadicLength L₀ M h₀ :=
  Nat.find_spec (dyadic_exists L₀ M h₀)

theorem dyadicLength_ge_base (L₀ M : ℕ) (h₀ : 0 < L₀) : L₀ ≤ dyadicLength L₀ M h₀ := by
  exact Nat.le_mul_of_pos_right _ (pow_pos (by decide) _)

theorem dyadicIndex_minimal (L₀ M : ℕ) (h₀ : 0 < L₀) {e : ℕ}
    (he : e < dyadicIndex L₀ M h₀) : L₀ * 2 ^ e < M :=
  Nat.lt_of_not_ge (Nat.find_min (dyadic_exists L₀ M h₀) he)

theorem dyadicLength_le (L₀ M : ℕ) (h₀ : 0 < L₀) :
    dyadicLength L₀ M h₀ ≤ max L₀ (2 * M) := by
  cases he : dyadicIndex L₀ M h₀ with
  | zero => simp [dyadicLength, he]
  | succ e =>
    have h := dyadicIndex_minimal L₀ M h₀ (e := e) (by omega)
    have hb : dyadicLength L₀ M h₀ ≤ 2 * M := by
      simp only [dyadicLength, he, pow_succ]
      nlinarith
    exact hb.trans (le_max_right _ _)

theorem dyadicLength_between {L₀ M : ℕ} (h₀ : 0 < L₀) (hM : L₀ ≤ M) :
    M ≤ dyadicLength L₀ M h₀ ∧ dyadicLength L₀ M h₀ ≤ 2 * M := by
  refine ⟨dyadicLength_ge L₀ M h₀, ?_⟩
  have h := dyadicLength_le L₀ M h₀
  have h₀M : L₀ ≤ 2 * M := by omega
  simpa [max_eq_right h₀M] using h

theorem dyadicLength_divisible {L₀ M : ℕ} (h₀ : 0 < L₀) (h₄ : 4 ∣ L₀) :
    4 ∣ dyadicLength L₀ M h₀ := dvd_mul_of_dvd_left h₄ _

theorem initial_padding_capacity (L₀ q : ℕ) (h₀ : 0 < L₀) :
    q ≤ dyadicLength L₀ (4 * q) h₀ / 4 ∧
    dyadicLength L₀ (4 * q) h₀ ≤ max L₀ (8 * q) := by
  have h := dyadicLength_ge L₀ (4 * q) h₀
  have hb := dyadicLength_le L₀ (4 * q) h₀
  constructor
  · omega
  · simpa only [← Nat.mul_assoc, show 2 * 4 = 8 from rfl] using hb

theorem second_padding_contract (L₀ q M : ℕ) (h₀ : 0 < L₀) (h₄ : 4 ∣ L₀)
    (hM : dyadicLength L₀ (4 * q) h₀ ≤ M) :
    M ≤ dyadicLength L₀ M h₀ ∧ dyadicLength L₀ M h₀ ≤ 2 * M ∧
    q ≤ dyadicLength L₀ M h₀ / 4 ∧ 4 ∣ dyadicLength L₀ M h₀ := by
  have hb := dyadicLength_ge_base L₀ (4 * q) h₀
  have hi := dyadicLength_ge L₀ (4 * q) h₀
  have hl := dyadicLength_between h₀ (hb.trans hM)
  exact ⟨hl.1, hl.2, by omega, dyadicLength_divisible h₀ h₄⟩

end QecReliability.CodeHash
