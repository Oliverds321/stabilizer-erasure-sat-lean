import QecReliability.CodeCore

/-! Explicit zero padding preserves message injectivity and code distance. -/
noncomputable section
namespace QecReliability.CodeHash
open scoped BigOperators

def pad {q k : ℕ} (_h : q ≤ k) : Word q →ₗ[F] Word k where
  toFun a i := if hi : i.val < q then a ⟨i.val, hi⟩ else 0
  map_add' a b := by ext i; by_cases hi : i.val < q <;> simp [hi]
  map_smul' c a := by ext i; by_cases hi : i.val < q <;> simp [hi]

theorem truncate_pad {q k : ℕ} (h : q ≤ k) (a : Word q) : truncate h (pad h a) = a := by
  ext i
  simp [truncate, pad, i.isLt]

theorem pad_injective {q k : ℕ} (h : q ≤ k) : Function.Injective (pad h) := by
  intro a b hab
  simpa only [truncate_pad] using congrArg (truncate h) hab

theorem distance_pad {q k m d : ℕ} (h : q ≤ k) (G : Word k →ₗ[F] Word m)
    (hd : DistanceAtLeast G d) : DistanceAtLeast (G.comp (pad h)) d := by
  intro a ha
  apply hd (pad h a)
  intro hz
  exact ha (pad_injective h (hz.trans (pad h).map_zero.symm))

theorem weight_append_zero {m z : ℕ} (a : Word m) :
    weight (Fin.append a (0 : Word z)) = weight a := by
  unfold weight
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_add]
  simp

theorem seed_card (m t : ℕ) : Fintype.card (Seed m t) = 2 ^ (m * (t + 1)) := by
  simp only [Seed, LocalSeed, Word, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin, F, Binary.Bit, ZMod.card]
  rw [← pow_succ, ← pow_mul]
  congr 1
  ring

end QecReliability.CodeHash
