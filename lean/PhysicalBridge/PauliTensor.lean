import PhysicalBridge.OptimalUnitaryMixture
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Constructive finite Pauli families for every number of qubits. The real
representatives are I, X, Z, XZ; global Pauli phases do not enter conjugation. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder Kronecker
open Matrix
variable {a b ι κ : Type*} [Fintype a] [Fintype b] [Fintype ι] [Fintype κ]
  [DecidableEq a] [DecidableEq b]

namespace UnitaryResolution

def tensor (U : UnitaryResolution a ι) (V : UnitaryResolution b κ) :
    UnitaryResolution (a × b) (ι × κ) where
  op t := U.op t.1 ⊗ₖ V.op t.2
  unitary t := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      U.unitary, V.unitary, Matrix.one_kronecker_one]
  resolution i j k l := by
    simp only [Matrix.kroneckerMap_apply, star_mul', Fintype.sum_prod_type]
    have h : (∑ t : ι, ∑ s : κ,
        (U.op t i.1 k.1 * V.op s i.2 k.2) * (star (U.op t j.1 l.1) * star (V.op s j.2 l.2))) =
        (∑ t : ι, U.op t i.1 k.1 * star (U.op t j.1 l.1)) *
          (∑ s : κ, V.op s i.2 k.2 * star (V.op s j.2 l.2)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [h, U.resolution, V.resolution]
    simp only [Fintype.card_prod, Nat.cast_mul]
    by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
      by_cases h₃ : k.1 = l.1 <;> by_cases h₄ : k.2 = l.2 <;>
      simp [Prod.ext_iff, h₁, h₂, h₃, h₄]

end UnitaryResolution

def qubitPauli (t : Fin 4) : Square (Fin 2) :=
  ![!![1, 0; 0, 1], !![0, 1; 1, 0], !![1, 0; 0, -1], !![0, -1; 1, 0]] t

def qubitResolution : UnitaryResolution (Fin 2) (Fin 4) where
  op := qubitPauli
  unitary t := by
    fin_cases t <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [qubitPauli, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  resolution i j k l := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [qubitPauli, Fin.sum_univ_succ]

def trivialResolution : UnitaryResolution Unit Unit where
  op _ := 1
  unitary _ := by simp
  resolution i j k l := by simp

/-- A concrete tensor-product basis index, with exactly d^n elements. -/
def TensorIndex (d : ℕ) : ℕ → Type
  | 0 => Unit
  | n+1 => TensorIndex d n × Fin d

instance tensorIndexFintype (d n : ℕ) : Fintype (TensorIndex d n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (TensorIndex d n × Fin d))

instance tensorIndexDecidableEq (d n : ℕ) : DecidableEq (TensorIndex d n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (TensorIndex d n × Fin d))

instance tensorIndexNonempty (d n : ℕ) [NeZero d] : Nonempty (TensorIndex d n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Nonempty (TensorIndex d n × Fin d))

theorem card_tensorIndex (d n : ℕ) : Fintype.card (TensorIndex d n) = d ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [TensorIndex, Fintype.card_prod, Fintype.card_fin, ih, pow_succ]

def pauliResolution : (n : ℕ) → UnitaryResolution (TensorIndex 2 n) (TensorIndex 4 n)
  | 0 => trivialResolution
  | n+1 => (pauliResolution n).tensor qubitResolution

/-- Exact all-CPTP recovery optimum for every finite n-qubit Pauli mixture. -/
theorem pauli_mixture_optimum (n : ℕ) (p : TensorIndex 4 n → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hpsum : ∑ t, p t = 1)
    (m : TensorIndex 4 n) (hm : ∀ t, p t ≤ p m) :
    entanglementFidelity (((pauliResolution n).inverseChannel m).comp
      ((pauliResolution n).noiseChannel p hp hpsum)).map = p m ∧
    ∀ R : Channel (TensorIndex 2 n) (TensorIndex 2 n),
      entanglementFidelity (R.comp ((pauliResolution n).noiseChannel p hp hpsum)).map ≤ p m :=
  (pauliResolution n).optimal_recovery p hp hpsum m hm


/-- A maximizing label and an attaining CPTP recovery exist for every Pauli distribution. -/
theorem pauli_mixture_optimum_exists (n : ℕ) (p : TensorIndex 4 n → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hpsum : ∑ t, p t = 1) :
    ∃ m : TensorIndex 4 n, (∀ t, p t ≤ p m) ∧
      ∃ R : Channel (TensorIndex 2 n) (TensorIndex 2 n),
        entanglementFidelity (R.comp ((pauliResolution n).noiseChannel p hp hpsum)).map = p m ∧
        ∀ R' : Channel (TensorIndex 2 n) (TensorIndex 2 n),
          entanglementFidelity (R'.comp ((pauliResolution n).noiseChannel p hp hpsum)).map ≤ p m := by
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  have hmax : ∀ t, p t ≤ p m := fun t => hm t (Finset.mem_univ t)
  exact ⟨m, hmax, (pauliResolution n).inverseChannel m, pauli_mixture_optimum n p hp hpsum m hmax⟩

/-- The physical uniform-ambiguity value needed by the binary-rank bridge.
The channel is still explicitly the supplied Pauli mixture, not an assumed erasure reduction. -/
theorem pauli_uniform_power_two_optimum (n d : ℕ) (A : Finset (TensorIndex 4 n))
    (hA : A.Nonempty) (hcard : A.card = 2 ^ d) (m : TensorIndex 4 n) (hm : m ∈ A) :
    let U := pauliResolution n
    let p := UnitaryResolution.uniformWeights A
    let N := U.noiseChannel p (UnitaryResolution.uniformWeights_nonneg A)
      (UnitaryResolution.uniformWeights_sum A hA)
    entanglementFidelity ((U.inverseChannel m).comp N).map = ((2 : ℝ) ^ d)⁻¹ ∧
    ∀ R : Channel (TensorIndex 2 n) (TensorIndex 2 n),
      entanglementFidelity (R.comp N).map ≤ ((2 : ℝ) ^ d)⁻¹ := by
  simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using
    (pauliResolution n).uniform_optimal_recovery A hA m hm

end QecPhysical
