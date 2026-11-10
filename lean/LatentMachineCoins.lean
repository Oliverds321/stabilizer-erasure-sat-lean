import LatentMachineBridge

/-! Discharges the exact-law premise for actual CodeHash stored seed decoding.
One uniform finite coin string is retained and decoded once, without resampling,
deduplication, or assuming success of the estimation event.
-/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine
open scoped Classical
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open OracleCost.StoredCodeHashConfidence CodeHash.FiniteRandomTape

def decodeCoins (L t m : ℕ) (w : Fin (CodeHash.repeatBits L t m) → Bool) :
    Fin (2*m+1) → CodeHash.Seed L t :=
  actualCodeHashSeedTuple L t m (InputWord.ofTape _ w)

theorem decodeCoins_eq (L t m : ℕ) (w : Fin (CodeHash.repeatBits L t m) → Bool) :
    decodeCoins L t m w = CodeHash.repeatedSeedTapeEquiv L t m w := by
  simp only [decodeCoins, actualCodeHashSeedTuple, outputSeeds_sample,
    semanticSeeds, InputWord.denote_ofTape]

/-- Every seed predicate, not only the accuracy event, has the exact counting law. -/
theorem decodeCoins_law (L t m : ℕ)
    (P : (Fin (2*m+1) → CodeHash.Seed L t) → Prop) :
    (repeatedLaw (uniformLaw (CodeHash.Seed L t)) m).prob P *
        (2:ℝ)^(CodeHash.repeatBits L t m) =
      ((Finset.univ.filter (fun w : Fin (CodeHash.repeatBits L t m) → Bool =>
        P (decodeCoins L t m w))).card : ℝ) := by
  simp only [decodeCoins_eq]
  rw [← CodeHash.repeatedSeedTape_law L t m P, uniformLaw_prob]
  have hcard : (Fintype.card (CodeHash.BitTape (CodeHash.repeatBits L t m)) : ℝ) =
      (2:ℝ)^(CodeHash.repeatBits L t m) := by
    simp [CodeHash.BitTape, Fintype.card_fun]
  rw [hcard]
  exact div_mul_cancel₀ _ (by positivity)

theorem actualCodeHash_realizesCoins {n r L t : ℕ}
    (S : CodeHash.System (CoefficientKey n r) L t (keySize n r)) (c d : ℕ) :
    RealizesCoins (actualCodeHash S) c d
      (CodeHash.repeatBits L t (repetitions (r:=r) c d))
      (decodeCoins L t (repetitions (r:=r) c d)) := by
  intro P
  exact decodeCoins_law L t (repetitions (r:=r) c d) P

end QecReliability.LatentMachine
