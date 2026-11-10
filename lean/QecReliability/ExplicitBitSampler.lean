import QecReliability.CodeHash
import QecReliability.QuantumDecisionBridge
import QecReliability.SimultaneousConfidence
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

/-!


The sampler definitions precede the noncomputable
probability section. No Fintype enumeration or choice occurs in the decoder.
-/

namespace QecReliability.CodeHash

abbrev BitTape (N : ℕ) := Fin N → Bool

def seedBits (L t : ℕ) : ℕ := L * (t+1)
def repeatBits (L t m : ℕ) : ℕ := (2*m+1) * seedBits L t

/-- Pointwise lifting of an explicit equivalence: no finite enumeration. -/
def mapFunctionEquiv (I : Type*) {A B : Type*} (e : A ≃ B) : (I → A) ≃ (I → B) where
  toFun f i := e (f i)
  invFun g i := e.symm (g i)
  left_inv f := by funext i; exact e.symm_apply_apply (f i)
  right_inv g := by funext i; exact e.apply_symm_apply (g i)

/-- Pinned finProdFinEquiv sends (i,h) to h + width*i, exactly row-major.
The empty dimension cases need no division-by-positive premise. -/
def blockTapeEquiv (rows width : ℕ) (A : Type*) :
    (Fin (rows*width) → A) ≃ (Fin rows → Fin width → A) where
  toFun u i h := u (finProdFinEquiv (i,h))
  invFun v h := v (finProdFinEquiv.symm h).1 (finProdFinEquiv.symm h).2
  left_inv u := by
    funext h
    change u (finProdFinEquiv (finProdFinEquiv.symm h)) = u h
    rw [Equiv.apply_symm_apply]
  right_inv v := by
    funext i h
    change v (finProdFinEquiv.symm (finProdFinEquiv (i,h))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i,h))).2 = v i h
    rw [Equiv.symm_apply_apply]

/-- First t coordinates are the affine coefficients, final coordinate is intercept. -/
def localSeedTapeEquiv (t : ℕ) : BitTape (t+1) ≃ LocalSeed t :=
  (mapFunctionEquiv (Fin (t+1)) Binary.bitBool.symm).trans (Fin.succFunEquiv F t)

def seedTapeEquiv (L t : ℕ) : BitTape (seedBits L t) ≃ Seed L t :=
  (blockTapeEquiv L (t+1) Bool).trans (mapFunctionEquiv (Fin L) (localSeedTapeEquiv t))

def repeatedSeedTapeEquiv (L t m : ℕ) :
    BitTape (repeatBits L t m) ≃ (Fin (2*m+1) → Seed L t) :=
  (blockTapeEquiv (2*m+1) (seedBits L t) Bool).trans
    (mapFunctionEquiv (Fin (2*m+1)) (seedTapeEquiv L t))

theorem seed_encode_decode (L t : ℕ) (u : BitTape (seedBits L t)) :
    (seedTapeEquiv L t).symm (seedTapeEquiv L t u) = u :=
  (seedTapeEquiv L t).symm_apply_apply u

theorem seed_decode_encode (L t : ℕ) (s : Seed L t) :
    seedTapeEquiv L t ((seedTapeEquiv L t).symm s) = s :=
  (seedTapeEquiv L t).apply_symm_apply s

theorem repeat_encode_decode (L t m : ℕ) (u : BitTape (repeatBits L t m)) :
    (repeatedSeedTapeEquiv L t m).symm (repeatedSeedTapeEquiv L t m u) = u :=
  (repeatedSeedTapeEquiv L t m).symm_apply_apply u

theorem repeat_decode_encode (L t m : ℕ) (s : Fin (2*m+1) → Seed L t) :
    repeatedSeedTapeEquiv L t m ((repeatedSeedTapeEquiv L t m).symm s) = s :=
  (repeatedSeedTapeEquiv L t m).apply_symm_apply s

theorem card_seed_from_tape (L t : ℕ) : Fintype.card (Seed L t) = 2 ^ seedBits L t := by
  calc
    Fintype.card (Seed L t) = Fintype.card (BitTape (seedBits L t)) :=
      (Fintype.card_congr (seedTapeEquiv L t)).symm
    _ = 2 ^ seedBits L t := by simp [BitTape, Fintype.card_fun]

end QecReliability.CodeHash

noncomputable section
namespace QecReliability
open scoped BigOperators

/-- This transports arbitrary events, including noncomputable semantic events. -/
theorem uniformLaw_equiv_prob
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (P : B → Prop) :
    (uniformLaw A).prob (fun a => P (e a)) = (uniformLaw B).prob P := by
  classical
  change (∑ a, (1 / (Fintype.card A : ℝ)) * indicator P (e a)) =
    ∑ b, (1 / (Fintype.card B : ℝ)) * indicator P b
  rw [Fintype.card_congr e]
  exact e.sum_comp (fun b => (1 / (Fintype.card B : ℝ)) * indicator P b)

/-- Event form avoids assuming a generated extensionality lemma for the source
FiniteProbability structure (the structure has no explicit @[ext] attribute). -/
theorem uniformLaw_product_prob
    {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (P : (I → A) → Prop) :
    (FiniteProbability.product (fun _ : I => uniformLaw A)).prob P =
      (uniformLaw (I → A)).prob P := by
  classical
  have hm (ω : I → A) :
      (FiniteProbability.product (fun _ : I => uniformLaw A)).mass ω =
        (uniformLaw (I → A)).mass ω := by
    change (∏ _ : I, (1 / (Fintype.card A : ℝ))) =
      1 / (Fintype.card (I → A) : ℝ)
    rw [Fintype.card_fun, Nat.cast_pow]
    simp [one_div, inv_pow]
  unfold FiniteProbability.prob FiniteProbability.expect average
  apply Finset.sum_congr rfl
  intro ω _
  rw [hm]

namespace CodeHash

theorem seedTape_law (L t : ℕ) (P : Seed L t → Prop) :
    (uniformLaw (BitTape (seedBits L t))).prob
      (fun u => P (seedTapeEquiv L t u)) = (uniformLaw (Seed L t)).prob P :=
  uniformLaw_equiv_prob (seedTapeEquiv L t) P

theorem repeatedSeedTape_law (L t m : ℕ)
    (P : (Fin (2*m+1) → Seed L t) → Prop) :
    (uniformLaw (BitTape (repeatBits L t m))).prob
      (fun u => P (repeatedSeedTapeEquiv L t m u)) =
        (repeatedLaw (uniformLaw (Seed L t)) m).prob P := by
  calc
    _ = (uniformLaw (Fin (2*m+1) → Seed L t)).prob P :=
      uniformLaw_equiv_prob (repeatedSeedTapeEquiv L t m) P
    _ = (repeatedLaw (uniformLaw (Seed L t)) m).prob P :=
      (uniformLaw_product_prob P).symm

theorem confidence_from_raw_bits (L t m : ℕ)
    (Good : (Fin (2*m+1) → Seed L t) → Prop) (δ : ℝ)
    (h : 1-δ ≤ (repeatedLaw (uniformLaw (Seed L t)) m).prob Good) :
    1-δ ≤ (uniformLaw (BitTape (repeatBits L t m))).prob
      (fun u => Good (repeatedSeedTapeEquiv L t m u)) := by
  rw [repeatedSeedTape_law]
  exact h

end CodeHash
end QecReliability
