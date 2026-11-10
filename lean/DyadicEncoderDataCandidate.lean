import OneZeroPaddingCandidate

/-!
This is the SEMANTIC/CIRCUIT projection of the fixed,
certified dyadic generator supplied by the encoder construction, not a claim that an
arbitrary family-valued structure is a polynomial-time generator.
-/
namespace QecReliability.UniformAdapter
open CodeHash SharedCircuit

noncomputable def castEncoder {a b a' b' : ℕ} (E : Word a →ₗ[F] Word b)
    (ha : a = a') (hb : b = b') : Word a' →ₗ[F] Word b' := by
  subst a'; subst b'
  exact E

def castProgram {a b a' b' : ℕ} (P : Program a b)
    (ha : a = a') (hb : b = b') : Program a' b' :=
  (inputCast P ha).outputCast hb

@[simp] theorem castProgram_gates {a b a' b' : ℕ} (P : Program a b)
    (ha : a = a') (hb : b = b') : (castProgram P ha hb).gates = P.gates := by
  cases ha; cases hb; rfl

@[simp] theorem castProgram_xorOnly {a b a' b' : ℕ} (P : Program a b)
    (ha : a = a') (hb : b = b') :
    (castProgram P ha hb).circuit.xorOnly = P.circuit.xorOnly := by
  cases ha; cases hb; rfl

theorem castProgram_correct {a b a' b' : ℕ} (P : Program a b)
    (E : Word a →ₗ[F] Word b)
    (hP : ∀ x i, boolBit (P.eval x i) = E (bitsVector x) i)
    (ha : a = a') (hb : b = b') :
    ∀ x i, boolBit ((castProgram P ha hb).eval x i) =
      castEncoder E ha hb (bitsVector x) i := by
  cases ha; cases hb
  exact hP

theorem castEncoder_distance {a b a' b' : ℕ} (E : Word a →ₗ[F] Word b) {α : ℝ}
    (hE : ∀ x, x ≠ 0 → α*b ≤ (weight (E x) : ℝ))
    (ha : a = a') (hb : b = b') :
    ∀ x, x ≠ 0 → α*b' ≤ (weight (castEncoder E ha hb x) : ℝ) := by
  cases ha; cases hb
  exact hE

structure DyadicXorData where
  base : ℕ
  base_pos : 0 < base
  base_four : 4 ∣ base
  num : ℕ
  den : ℕ
  gateConstant : ℕ
  num_pos : 0 < num
  num_le_den : num ≤ den
  encoder : (ell : ℕ) → Word (base * 2^ell / 4) →ₗ[F] Word (base * 2^ell)
  program : (ell : ℕ) → Program (base * 2^ell / 4) (base * 2^ell)
  xorOnly : ∀ ell, (program ell).circuit.xorOnly = true
  correct : ∀ ell x i, boolBit ((program ell).eval x i) = encoder ell (bitsVector x) i
  distance : ∀ ell x, x ≠ 0 →
    ((num:ℝ)/(den:ℝ))*(base*2^ell) ≤ (weight (encoder ell x) : ℝ)
  gates_le : ∀ ell, (program ell).gates ≤ gateConstant*(base*2^ell)

namespace DyadicXorData

noncomputable def alpha (X : DyadicXorData) : ℝ := (X.num:ℝ)/X.den

theorem den_pos (X : DyadicXorData) : 0 < X.den := lt_of_lt_of_le X.num_pos X.num_le_den

theorem alpha_pos (X : DyadicXorData) : 0 < X.alpha := by
  exact div_pos (by exact_mod_cast X.num_pos) (by exact_mod_cast X.den_pos)

theorem alpha_le_one (X : DyadicXorData) : X.alpha ≤ 1 := by
  exact (div_le_one (by exact_mod_cast X.den_pos)).2 (by exact_mod_cast X.num_le_den)

noncomputable def toFamily (X : DyadicXorData) : DyadicCodeFamily where
  base := X.base
  base_pos := X.base_pos
  base_four := X.base_four
  α := X.alpha
  alpha_pos := X.alpha_pos
  encoder := X.encoder
  distance := X.distance

theorem shiftLength (base ell : ℕ) : (2*base)*2^ell = base*2^(ell+1) := by
  rw [pow_succ]
  ring

/-- Executable program projection of the shift, independent of real-valued proofs. -/
def shiftedProgram (X : DyadicXorData) (ell : ℕ) :
    Program ((2*X.base)*2^ell/4) ((2*X.base)*2^ell) :=
  castProgram (X.program (ell+1))
    (congrArg (fun n => n/4) (shiftLength X.base ell).symm) (shiftLength X.base ell).symm

/-- The SAME generator is called at ell+1. No new code is selected or searched. -/
noncomputable def shift (X : DyadicXorData) : DyadicXorData where
  base := 2*X.base
  base_pos := Nat.mul_pos (by decide) X.base_pos
  base_four := dvd_mul_of_dvd_right X.base_four 2
  num := X.num
  den := X.den
  gateConstant := X.gateConstant
  num_pos := X.num_pos
  num_le_den := X.num_le_den
  encoder ell := castEncoder (X.encoder (ell+1))
    (congrArg (fun n => n/4) (shiftLength X.base ell).symm) (shiftLength X.base ell).symm
  program ell := castProgram (X.program (ell+1))
    (congrArg (fun n => n/4) (shiftLength X.base ell).symm) (shiftLength X.base ell).symm
  xorOnly ell := by rw [castProgram_xorOnly]; exact X.xorOnly (ell+1)
  correct ell := castProgram_correct _ _ (X.correct (ell+1)) _ _
  distance ell := by
    intro x hx
    have hd := castEncoder_distance (X.encoder (ell+1)) (α := X.alpha)
      (by
        intro y hy
        simpa only [alpha, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using X.distance (ell+1) y hy)
      (congrArg (fun n => n/4) (shiftLength X.base ell).symm)
      (shiftLength X.base ell).symm x hx
    simpa only [alpha, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hd
  gates_le ell := by
    rw [castProgram_gates, shiftLength]
    exact X.gates_le (ell+1)

@[simp] theorem shift_program_eq (X : DyadicXorData) (ell : ℕ) :
    X.shift.program ell = X.shiftedProgram ell := rfl

theorem shift_base_ge_eight (X : DyadicXorData) : 8 ≤ X.shift.base := by
  change 8 ≤ 2*X.base
  obtain ⟨k, hk⟩ := X.base_four
  have hp := X.base_pos
  omega

@[simp] theorem shift_gateConstant (X : DyadicXorData) :
    X.shift.gateConstant = X.gateConstant := rfl

@[simp] theorem shift_den (X : DyadicXorData) : X.shift.den = X.den := rfl

@[simp] theorem shift_alpha (X : DyadicXorData) : X.shift.alpha = X.alpha := rfl

end DyadicXorData
end QecReliability.UniformAdapter
