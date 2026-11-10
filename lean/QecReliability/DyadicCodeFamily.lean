import QecReliability.CodingHashBridge

/-! Exact interface to the remaining classical dyadic binary-code construction.
This file does not assert existence of such a family or its small circuits. -/
noncomputable section
namespace QecReliability.CodeHash

structure DyadicCodeFamily where
  base : ℕ
  base_pos : 0 < base
  base_four : 4 ∣ base
  α : ℝ
  alpha_pos : 0 < α
  encoder : (ell : ℕ) → Word (base * 2 ^ ell / 4) →ₗ[F] Word (base * 2 ^ ell)
  distance : ∀ ell a, a ≠ 0 → α * (base * 2 ^ ell) ≤ (weight (encoder ell a) : ℝ)

def DyadicCodeFamily.codingData {A : Type*} (FAM : DyadicCodeFamily) (q M t : ℕ)
    (hM : dyadicLength FAM.base (4 * q) FAM.base_pos ≤ M)
    (encode : A → Fin M → Word t)
    (hsep : ∀ x y, x ≠ y → (agreements (encode x) (encode y) : ℝ) < FAM.α * M / 4) :
    CodingData A q where
  M := M
  L := dyadicLength FAM.base M FAM.base_pos
  t := t
  k := dyadicLength FAM.base M FAM.base_pos / 4
  positive := FAM.base_pos.trans_le ((dyadicLength_ge_base _ _ _).trans hM)
  length_ge := (second_padding_contract _ _ _ FAM.base_pos FAM.base_four hM).1
  length_le := (second_padding_contract _ _ _ FAM.base_pos FAM.base_four hM).2.1
  capacity := (second_padding_contract _ _ _ FAM.base_pos FAM.base_four hM).2.2.1
  α := FAM.α
  alpha_pos := FAM.alpha_pos
  encode := encode
  separation := hsep
  code := FAM.encoder (dyadicIndex FAM.base M FAM.base_pos)
  distance := by
    intro a ha
    simpa only [dyadicLength, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      FAM.distance (dyadicIndex FAM.base M FAM.base_pos) a ha

end QecReliability.CodeHash
