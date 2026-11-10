import QecReliability.CodeCore
import QecReliability.UniformLinear
import QecReliability.HashConfidence
import QecReliability.BinarySymplectic

/-! The algebraic core of code-based hashing. No code/expander existence or circuit
size is asserted: the precise residual assumption is erasure-surjectivity below. -/
noncomputable section
namespace QecReliability.CodeHash
open scoped BigOperators

def affine {t : ℕ} (v : Word t) : LocalSeed t →ₗ[F] F where
  toFun s := (∑ j, s.1 j * v j) + s.2
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]; ring
  map_smul' c s := by simp [mul_assoc, ← Finset.mul_sum, mul_add]

theorem affine_surjective {t : ℕ} (v : Word t) : Function.Surjective (affine v) := by
  intro a
  exact ⟨(0, a), by simp [affine]⟩

theorem affine_pair_surjective {t : ℕ} {v w : Word t} (h : v ≠ w) :
    Function.Surjective ((affine v).prod (affine w)) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ w j := Function.ne_iff.mp h
  intro ab
  let c := (ab.2 - ab.1) / (w j - v j)
  refine ⟨(Pi.single j c, ab.1 - c * v j), ?_⟩
  have hd : w j - v j ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
  apply Prod.ext
  · simp [affine, Pi.single_apply]
  · simp [affine, Pi.single_apply]
    dsimp [c]
    field_simp
    ring

def mask {m : ℕ} (D : Fin m → Prop) [DecidablePred D] : Word m →ₗ[F] Word m where
  toFun u i := if D i then u i else 0
  map_add' a b := by ext i; by_cases h : D i <;> simp [h]
  map_smul' c a := by ext i; by_cases h : D i <;> simp [h]

/-- An encoder with an extractor still onto after retaining only differing symbols.
This is the algebraic hypothesis delivered by the distance/expander construction. -/
structure System (A : Type*) (m t q : ℕ) where
  encode : A → Fin m → Word t
  extract : Word m →ₗ[F] Word q
  onto : Function.Surjective extract
  separating : ∀ x y, x ≠ y → Function.Surjective
    (extract.comp (mask (fun i => encode x i ≠ encode y i)))

def System.local {A : Type*} {m t q : ℕ} (D : System A m t q) (x : A) :
    Seed m t →ₗ[F] Word m := LinearMap.pi (fun i =>
      (affine (D.encode x i)).comp (LinearMap.proj i))

def System.eval {A : Type*} {m t q : ℕ} (D : System A m t q) (x : A) :
    Seed m t →ₗ[F] Word q := D.extract.comp (D.local x)

theorem System.eval_surjective {A : Type*} {m t q : ℕ} (D : System A m t q) (x : A) :
    Function.Surjective (D.eval x) := by
  intro a
  obtain ⟨u, hu⟩ := D.onto a
  refine ⟨fun i => (0, u i), ?_⟩
  change D.extract (fun i => affine (D.encode x i) (0, u i)) = a
  simpa [affine] using hu

theorem System.eval_pair_surjective {A : Type*} {m t q : ℕ} (D : System A m t q)
    {x y : A} (h : x ≠ y) : Function.Surjective ((D.eval x).prod (D.eval y)) := by
  classical
  intro ab
  obtain ⟨u, hu⟩ := D.separating x y h ab.1
  obtain ⟨v, hv⟩ := D.separating x y h ab.2
  have hs : ∀ i, ∃ s : LocalSeed t,
      affine (D.encode x i) s = mask (fun i => D.encode x i ≠ D.encode y i) u i ∧
      affine (D.encode y i) s = mask (fun i => D.encode x i ≠ D.encode y i) v i := by
    intro i
    by_cases hi : D.encode x i ≠ D.encode y i
    · obtain ⟨s, hs⟩ := affine_pair_surjective hi (u i, v i)
      exact ⟨s, by simpa [mask, hi] using congrArg Prod.fst hs,
        by simpa [mask, hi] using congrArg Prod.snd hs⟩
    · exact ⟨0, by simp [affine, mask, hi], by simp [affine, mask, hi]⟩
  choose s hx hy using hs
  refine ⟨s, Prod.ext ?_ ?_⟩
  · change D.extract (fun i => affine (D.encode x i) (s i)) = ab.1
    rw [funext hx]
    exact hu
  · change D.extract (fun i => affine (D.encode y i) (s i)) = ab.2
    rw [funext hy]
    exact hv

theorem System.uniform {A : Type*} {m t q : ℕ} (D : System A m t q) (x : A) (a : Word q) :
    (uniformLaw (Seed m t)).prob (fun s => D.eval x s = a) = 1 / (2 : ℝ) ^ q := by
  have h := uniformLaw_addHom (D.eval x).toAddMonoidHom (D.eval_surjective x) a
  simpa [Word, F, Binary.Bit] using h

theorem System.pairwise {A : Type*} {m t q : ℕ} (D : System A m t q)
    {x y : A} (hxy : x ≠ y) (a b : Word q) :
    (uniformLaw (Seed m t)).prob (fun s => D.eval x s = a ∧ D.eval y s = b) =
      (1 / (2 : ℝ) ^ q) ^ 2 := by
  have h := uniformLaw_addHom ((D.eval x).prod (D.eval y)).toAddMonoidHom
    (D.eval_pair_surjective hxy) (a, b)
  simpa [Word, F, Binary.Bit, Prod.ext_iff, pow_two, div_mul_div_comm] using h

end QecReliability.CodeHash
