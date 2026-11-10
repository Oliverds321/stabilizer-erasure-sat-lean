import PhysicalBridge.UnitaryResolution

/-! Optimal recovery of a unitary-basis mixture over all CPTP channels. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder
open Matrix
variable {a ι : Type*} [Fintype a] [Fintype ι] [DecidableEq a] [Nonempty a]
namespace UnitaryResolution
variable (U : UnitaryResolution a ι)

def noiseChannel (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t) (hpsum : ∑ t, p t = 1) : Channel a a :=
  mixtureChannel p hp hpsum U.errorChannel

omit [Nonempty a] in
theorem recovered_fidelity_eq (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t)
    (hpsum : ∑ t, p t = 1) (R : Channel a a) :
    entanglementFidelity (R.comp (U.noiseChannel p hp hpsum)).map =
      ∑ t, p t * entanglementFidelity (R.comp (U.errorChannel t)).map := by
  change entanglementFidelity (R.map.comp (mixtureMap p (fun t => (U.errorChannel t).map))) = _
  rw [comp_mixtureMap, entanglementFidelity_mixture]
  rfl

/-- An upper bound for every CPTP recovery, derived without a Kraus representation. -/
theorem recovered_fidelity_le (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t)
    (hpsum : ∑ t, p t = 1) (m : ι) (hm : ∀ t, p t ≤ p m) (R : Channel a a) :
    entanglementFidelity (R.comp (U.noiseChannel p hp hpsum)).map ≤ p m := by
  rw [U.recovered_fidelity_eq]
  calc
    (∑ t, p t * entanglementFidelity (R.comp (U.errorChannel t)).map) ≤
        ∑ t, p m * entanglementFidelity (R.comp (U.errorChannel t)).map := by
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_right (hm t) (entanglementFidelity_bounds _).1
    _ = p m := by rw [← Finset.mul_sum, U.sum_recovered_fidelity, mul_one]

theorem inverse_fidelity_ge (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t)
    (hpsum : ∑ t, p t = 1) (m : ι) :
    p m ≤ entanglementFidelity ((U.inverseChannel m).comp (U.noiseChannel p hp hpsum)).map := by
  rw [U.recovered_fidelity_eq]
  calc
    p m = p m * entanglementFidelity ((U.inverseChannel m).comp (U.errorChannel m)).map := by
      rw [U.inverse_corrects, entanglementFidelity_identity, mul_one]
    _ ≤ ∑ t, p t * entanglementFidelity ((U.inverseChannel m).comp (U.errorChannel t)).map := by
      apply Finset.single_le_sum (s := Finset.univ) (a := m)
        (f := fun t : ι => p t * entanglementFidelity ((U.inverseChannel m).comp (U.errorChannel t)).map)
      · intro t _
        exact mul_nonneg (hp t)
          (entanglementFidelity_bounds ((U.inverseChannel m).comp (U.errorChannel t))).1
      · exact Finset.mem_univ m

/-- Inverting any most likely error attains the exact all-CPTP optimum. -/
theorem optimal_recovery (p : ι → ℝ) (hp : ∀ t, 0 ≤ p t)
    (hpsum : ∑ t, p t = 1) (m : ι) (hm : ∀ t, p t ≤ p m) :
    entanglementFidelity ((U.inverseChannel m).comp (U.noiseChannel p hp hpsum)).map = p m ∧
    ∀ R : Channel a a, entanglementFidelity (R.comp (U.noiseChannel p hp hpsum)).map ≤ p m := by
  exact ⟨le_antisymm (U.recovered_fidelity_le p hp hpsum m hm _) (U.inverse_fidelity_ge p hp hpsum m),
    U.recovered_fidelity_le p hp hpsum m hm⟩

section Uniform
variable [DecidableEq ι]

def uniformWeights (A : Finset ι) (t : ι) : ℝ := if t ∈ A then (A.card : ℝ)⁻¹ else 0

omit [Fintype ι] in
theorem uniformWeights_nonneg (A : Finset ι) (t : ι) : 0 ≤ uniformWeights A t := by
  unfold uniformWeights
  split_ifs <;> positivity

theorem uniformWeights_sum (A : Finset ι) (hA : A.Nonempty) :
    ∑ t, uniformWeights A t = 1 := by
  have hn : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hA)
  simp [uniformWeights, hn]

/-- Uniform ambiguity on any nonempty subset gives optimum one divided by its size. -/
theorem uniform_optimal_recovery (A : Finset ι) (hA : A.Nonempty) (m : ι) (hm : m ∈ A) :
    entanglementFidelity ((U.inverseChannel m).comp
      (U.noiseChannel (uniformWeights A) (uniformWeights_nonneg A) (uniformWeights_sum A hA))).map =
        (A.card : ℝ)⁻¹ ∧
    ∀ R : Channel a a, entanglementFidelity (R.comp
      (U.noiseChannel (uniformWeights A) (uniformWeights_nonneg A) (uniformWeights_sum A hA))).map ≤
        (A.card : ℝ)⁻¹ := by
  have hmax : ∀ t, uniformWeights A t ≤ uniformWeights A m := by
    intro t
    simp only [uniformWeights, if_pos hm]
    split_ifs
    · exact le_rfl
    · positivity
  simpa only [uniformWeights, if_pos hm] using
    U.optimal_recovery (uniformWeights A) (uniformWeights_nonneg A) (uniformWeights_sum A hA) m hmax
end Uniform
end UnitaryResolution
end QecPhysical
