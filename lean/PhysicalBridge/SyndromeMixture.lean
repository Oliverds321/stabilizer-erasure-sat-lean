import PhysicalBridge.PauliSyndromes

/-! The first physical syndrome reduction, preserving every error index and
its probability. No logical Pauli frame or equal-fiber premise is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical.Stabilizer.Lift
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

def errorEncoding (e : Pauli n) := pauli e * L.encoding

theorem errorEncoding_isometry (e : Pauli n) :
    (L.errorEncoding e)ᴴ * L.errorEncoding e = 1 := by
  unfold errorEncoding
  rw [Matrix.conjTranspose_mul]
  calc
    _ = L.encodingᴴ * ((pauli e)ᴴ * pauli e) * L.encoding := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [pauli_unitary, Matrix.mul_one, L.encoding_isometry]

def errorDensity (e : Pauli n) (M : Square (Fin (finrank ℂ L.hilbertCodeSpace))) :
    Square (Word n) := L.errorEncoding e * M * (L.errorEncoding e)ᴴ

theorem errorDensity_trace (e : Pauli n) (M : Square (Fin (finrank ℂ L.hilbertCodeSpace))) :
    (L.errorDensity e M).trace = M.trace := by
  rw [errorDensity, Matrix.trace_mul_cycle, L.errorEncoding_isometry, Matrix.one_mul]

theorem errorEncoding_block_right (χ : S →ₗ[Bit] Bit) (e : Pauli n) :
    (L.errorEncoding e)ᴴ * (L.twist χ).projector =
      if χ = errorCharacter S e then (L.errorEncoding e)ᴴ else 0 := by
  have h := congrArg Matrix.conjTranspose (L.error_encoding_block χ e)
  simpa only [Matrix.conjTranspose_mul, (L.twist χ).projector_hermitian.eq,
    apply_ite, Matrix.conjTranspose_zero, errorEncoding] using h

theorem errorDensity_block (χ ψ : S →ₗ[Bit] Bit) (e : Pauli n)
    (M : Square (Fin (finrank ℂ L.hilbertCodeSpace))) :
    (L.twist χ).projector * L.errorDensity e M * (L.twist ψ).projector =
      if χ = errorCharacter S e ∧ ψ = errorCharacter S e then L.errorDensity e M else 0 := by
  have hl := L.error_encoding_block χ e
  change (L.twist χ).projector * L.errorEncoding e = _ at hl
  calc
    _ = ((L.twist χ).projector * L.errorEncoding e) * M *
        ((L.errorEncoding e)ᴴ * (L.twist ψ).projector) := by
      simp only [errorDensity, Matrix.mul_assoc]
    _ = _ := by
      rw [hl, L.errorEncoding_block_right]
      by_cases hχ : χ = errorCharacter S e <;>
        by_cases hψ : ψ = errorCharacter S e <;> simp [hχ, hψ, errorDensity, errorEncoding]

variable {τ : Type*} [Fintype τ]

/-- An actual CPTP encoded physical Pauli mixture. The map e need not be injective. -/
def encodedPauliChannel (e : τ → Pauli n) (p : τ → ℝ) (hp : ∀ t, 0 ≤ p t)
    (hsum : ∑ t, p t = 1) : Channel (Fin (finrank ℂ L.hilbertCodeSpace)) (Word n) :=
  mixtureChannel p hp hsum (fun t => isometryChannel (L.errorEncoding (e t)) (L.errorEncoding_isometry (e t)))

theorem encodedPauliChannel_apply (e : τ → Pauli n) (p : τ → ℝ) (hp : ∀ t, 0 ≤ p t)
    (hsum : ∑ t, p t = 1) (M : Square (Fin (finrank ℂ L.hilbertCodeSpace))) :
    (L.encodedPauliChannel e p hp hsum).map M = ∑ t, (p t : ℂ) • L.errorDensity (e t) M := by
  simp [encodedPauliChannel, mixtureChannel, mixtureMap, isometryChannel, conjugateMap, errorDensity]

theorem encodedPauliChannel_syndrome_block (e : τ → Pauli n) (p : τ → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hsum : ∑ t, p t = 1) (χ : S →ₗ[Bit] Bit)
    (M : Square (Fin (finrank ℂ L.hilbertCodeSpace))) :
    (L.twist χ).projector * (L.encodedPauliChannel e p hp hsum).map M * (L.twist χ).projector =
      ∑ t ∈ Finset.univ.filter (fun t => errorCharacter S (e t) = χ),
        (p t : ℂ) • L.errorDensity (e t) M := by
  rw [L.encodedPauliChannel_apply, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, L.errorDensity_block, and_self]
  simp [Finset.sum_filter, eq_comm]

theorem encodedPauliChannel_offDiagonal (e : τ → Pauli n) (p : τ → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hsum : ∑ t, p t = 1) (χ ψ : S →ₗ[Bit] Bit) (hne : χ≠ψ)
    (M : Square (Fin (finrank ℂ L.hilbertCodeSpace))) :
    (L.twist χ).projector * (L.encodedPauliChannel e p hp hsum).map M * (L.twist ψ).projector = 0 := by
  rw [L.encodedPauliChannel_apply, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_eq_zero
  intro t _
  rw [Matrix.mul_smul, Matrix.smul_mul, L.errorDensity_block]
  have h : ¬ (χ = errorCharacter S (e t) ∧ ψ = errorCharacter S (e t)) :=
    fun ht => hne (ht.1.trans ht.2.symm)
  rw [if_neg h, smul_zero]

theorem encodedPauliChannel_syndrome_mass (e : τ → Pauli n) (p : τ → ℝ)
    (hp : ∀ t, 0 ≤ p t) (hsum : ∑ t, p t = 1) (χ : S →ₗ[Bit] Bit)
    (M : Square (Fin (finrank ℂ L.hilbertCodeSpace))) (hM : M.trace = 1) :
    ((L.twist χ).projector * (L.encodedPauliChannel e p hp hsum).map M * (L.twist χ).projector).trace =
      ((∑ t ∈ Finset.univ.filter (fun t => errorCharacter S (e t) = χ), p t : ℝ) : ℂ) := by
  rw [L.encodedPauliChannel_syndrome_block, Matrix.trace_sum]
  simp only [Matrix.trace_smul, L.errorDensity_trace, hM, smul_eq_mul, mul_one]
  exact (Complex.ofReal_sum _ _).symm

end QecPhysical.Stabilizer.Lift
