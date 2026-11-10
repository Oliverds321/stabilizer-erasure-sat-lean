import PhysicalBridge.MatrixChannels

/-! Entanglement fidelity defined by actual overlap with the normalized Bell
projector. The trace formulas below are derived from that overlap. -/
noncomputable section
namespace QecPhysical
open scoped BigOperators ComplexOrder Kronecker
open Matrix
variable {a b e : Type*} [Fintype a] [Fintype b] [Fintype e]
  [DecidableEq a] [DecidableEq b] [DecidableEq e]

def bellDelta (a : Type*) [DecidableEq a] : a × a → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

def bellProjector (a : Type*) [Fintype a] [DecidableEq a] : Square (a × a) :=
  ((Fintype.card a : ℝ)⁻¹) • Matrix.vecMulVec (bellDelta a) (star (bellDelta a))

theorem bellProjector_posSemidef : (bellProjector a).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star (bellDelta a)).smul (by positivity)

theorem bellProjector_apply (i k j l : a) :
    bellProjector a (i,k) (j,l) =
      (Fintype.card a : ℂ)⁻¹ * (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  simp [bellProjector, bellDelta, Matrix.vecMulVec]

theorem bellProjector_trace [Nonempty a] : (bellProjector a).trace = 1 := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, bellProjector_apply,
    Fintype.card_ne_zero]

theorem bellProjector_block (i j : a) :
    (fun k l => bellProjector a (i,k) (j,l)) =
      (Fintype.card a : ℂ)⁻¹ • Matrix.single i j 1 := by
  ext k l
  rw [bellProjector_apply]
  change _ = (Fintype.card a : ℂ)⁻¹ * (if i = k ∧ j = l then 1 else 0)
  by_cases h₁ : i = k <;> by_cases h₂ : j = l <;> simp [h₁, h₂]

theorem trace_mul_bellProjector (X : Square (a × a)) :
    (X * bellProjector a).trace =
      (Fintype.card a : ℂ)⁻¹ * ∑ i : a, ∑ j : a, X (i,i) (j,j) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    bellProjector_apply, Finset.mul_sum, mul_comm]

theorem bellProjector_idempotent [Nonempty a] :
    bellProjector a * bellProjector a = bellProjector a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, bellProjector_apply,
    Fintype.card_ne_zero]

/-- Squared fidelity with a maximally entangled reference for maximally mixed input. -/
def entanglementFidelity (Φ : MatrixMap a a) : ℝ :=
  ((amplify Φ (bellProjector a) * bellProjector a).trace).re

theorem bell_overlap_eq (Φ : MatrixMap a a) :
    (amplify Φ (bellProjector a) * bellProjector a).trace =
      (Fintype.card a : ℂ)⁻¹ ^ 2 * ∑ i : a, ∑ j : a, Φ (Matrix.single i j 1) i j := by
  rw [trace_mul_bellProjector]
  have hentry : ∀ i j : a, amplify Φ (bellProjector a) (i, i) (j, j) =
      (Fintype.card a : ℂ)⁻¹ * Φ (Matrix.single i j 1) i j := by
    intro i j
    change Φ (fun k l => bellProjector a (i, k) (j, l)) i j = _
    calc
      _ = Φ ((Fintype.card a : ℂ)⁻¹ • Matrix.single i j 1) i j :=
        congrArg (fun M : Square a => Φ M i j) (bellProjector_block i j)
      _ = _ := congrArg (fun M : Square a => M i j)
        (Φ.map_smul (Fintype.card a : ℂ)⁻¹ (Matrix.single i j 1))
  simp_rw [hentry]
  simp only [← Finset.mul_sum]
  ring

theorem entanglementFidelity_eq (Φ : MatrixMap a a) :
    entanglementFidelity Φ = (Fintype.card a : ℝ)⁻¹ ^ 2 *
      (∑ i : a, ∑ j : a, Φ (Matrix.single i j 1) i j).re := by
  rw [entanglementFidelity, bell_overlap_eq]
  have hc : (Fintype.card a : ℂ)⁻¹ ^ 2 = (((Fintype.card a : ℝ)⁻¹ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem entanglementFidelity_identity [Nonempty a] :
    entanglementFidelity (Channel.identity a).map = 1 := by
  rw [entanglementFidelity_eq]
  have hn : (Fintype.card a : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [Channel.identity]
  field_simp

/-- Optimization quantifies over every all-ancilla CPTP recovery. -/
def AttainsErasureOptimum (V : Matrix (b × e) a ℂ) (hV : Vᴴ * V = 1)
    (score : ℝ) : Prop :=
  ∃ R : Channel b a,
    entanglementFidelity (R.comp (encodedErasure V hV)).map = score ∧
    ∀ R' : Channel b a,
      entanglementFidelity (R'.comp (encodedErasure V hV)).map ≤ score

end QecPhysical
