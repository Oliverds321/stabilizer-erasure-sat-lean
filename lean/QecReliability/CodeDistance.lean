import QecReliability.CodeCore
import QecReliability.CodeHashQuantum
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A binary linear code's distance implies surjectivity of its transposed
encoder after deletion of strictly fewer coordinates than that distance. -/
noncomputable section
namespace QecReliability.CodeHash
open scoped BigOperators


/-- Ordinary nonzero-codeword distance plus encoder injectivity supplies the
message-indexed distance condition. Neither condition alone is substituted. -/
theorem distance_of_range {k m d : ℕ} (G : Word k →ₗ[F] Word m)
    (hG : Function.Injective G)
    (hd : ∀ v ∈ LinearMap.range G, v ≠ 0 → d ≤ weight v) : DistanceAtLeast G d := by
  intro a ha
  apply hd (G a) ⟨a, rfl⟩
  intro hz
  exact ha (hG (hz.trans G.map_zero.symm))

def dotDual (k : ℕ) : Word k ≃ₗ[F] Module.Dual F (Word k) where
  toFun a :=
    { toFun := fun b => ∑ i, a i * b i
      map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_left_comm, ← Finset.mul_sum] }
  invFun φ i := φ (Pi.single i 1)
  left_inv a := by ext i; simp [Pi.single_apply]
  right_inv φ := by
    apply LinearMap.ext
    intro b
    have hb : b = ∑ i : Fin k, b i • (Pi.single i (1 : F) : Word k) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hb]
    simp [map_sum, mul_comm]
  map_add' a b := by ext c; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by ext b; simp [mul_assoc, ← Finset.mul_sum]

def transpose {k m : ℕ} (G : Word k →ₗ[F] Word m) : Word m →ₗ[F] Word k :=
  (dotDual k).symm.toLinearMap.comp (G.dualMap.comp (dotDual m).toLinearMap)

theorem transpose_apply {k m : ℕ} (G : Word k →ₗ[F] Word m) (u : Word m) (j : Fin k) :
    transpose G u j = ∑ i, u i * G (Pi.single j 1) i := rfl

theorem transpose_surjective {k m : ℕ} (G : Word k →ₗ[F] Word m)
    (hG : Function.Injective G) : Function.Surjective (transpose G) :=
  (dotDual k).symm.surjective.comp
    ((LinearMap.dualMap_surjective_of_injective hG).comp (dotDual m).surjective)

theorem transpose_mask {k m : ℕ} (G : Word k →ₗ[F] Word m)
    (D : Fin m → Prop) [DecidablePred D] :
    transpose ((mask D).comp G) = (transpose G).comp (mask D) := by
  ext u j
  simp only [transpose_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : D i <;> simp [mask, h]

theorem weight_le_deleted {m : ℕ} (v : Word m) (D : Fin m → Prop) [DecidablePred D]
    (h : mask D v = 0) : weight v ≤ (Finset.univ.filter (fun i => ¬ D i)).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro hD
  have hz := congrFun h i
  simp [mask, hD] at hz
  exact hi hz

/-- The strict deletion threshold is essential; equality with distance is not enough. -/
theorem puncture_injective {k m d : ℕ} (G : Word k →ₗ[F] Word m)
    (hd : DistanceAtLeast G d) (D : Fin m → Prop) [DecidablePred D]
    (hD : (Finset.univ.filter (fun i => ¬ D i)).card < d) :
    Function.Injective ((mask D).comp G) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra hne
  have hw := weight_le_deleted (G a) D ha
  have hl := hd a hne
  omega

theorem transpose_erasure_surjective {k m d : ℕ} (G : Word k →ₗ[F] Word m)
    (hd : DistanceAtLeast G d) (D : Fin m → Prop) [DecidablePred D]
    (hD : (Finset.univ.filter (fun i => ¬ D i)).card < d) :
    Function.Surjective ((transpose G).comp (mask D)) := by
  rw [← transpose_mask]
  exact transpose_surjective _ (puncture_injective G hd D hD)

def fromDistance {A : Type*} {m t k d : ℕ}
    (encode : A → Fin m → Word t) (G : Word k →ₗ[F] Word m)
    (hd : DistanceAtLeast G d) (hdpos : 0 < d)
    (hsep : ∀ x y, x ≠ y → (Finset.univ.filter (fun i => encode x i = encode y i)).card < d) :
    System A m t k where
  encode := encode
  extract := transpose G
  onto := by
    have h := transpose_erasure_surjective G hd (fun _ => True) (by simpa using hdpos)
    have hm : mask (fun _ : Fin m => True) = LinearMap.id (R := F) (M := Word m) := by
      ext u i; simp [mask]
    simpa [hm] using h
  separating x y hxy := transpose_erasure_surjective G hd _ (by simpa using hsep x y hxy)

/-- Deleting exactly the distance already fails for the one-bit identity code. -/
theorem strict_threshold_example :
    DistanceAtLeast (LinearMap.id (R := F) (M := Word 1)) 1 ∧
    ¬ Function.Surjective ((transpose (LinearMap.id (R := F) (M := Word 1))).comp
      (mask (fun _ => False))) := by
  constructor
  · intro a ha
    have h : a 0 ≠ 0 := by
      intro hz
      apply ha
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using hz
    exact Finset.card_pos.mpr ⟨0, by simpa [weight] using h⟩
  · intro hs
    obtain ⟨u, hu⟩ := hs (fun _ => 1)
    have h := congrFun hu 0
    simp [transpose_apply, mask] at h

end QecReliability.CodeHash
