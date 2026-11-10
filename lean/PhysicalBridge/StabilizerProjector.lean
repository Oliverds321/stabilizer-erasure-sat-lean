import PhysicalBridge.HermitianPauli
import Mathlib.LinearAlgebra.Trace

/-! A supplied phase-consistent Pauli stabilizer lift gives a concrete
orthogonal codespace projector. No code dimension or channel decomposition
is assumed in the lift interface. -/
noncomputable section
namespace QecPhysical.Stabilizer
open scoped BigOperators ComplexOrder
open Matrix
open QecReliability.Binary
open QecPhysical.BinaryPauli

instance stabilizerFintype {n : ℕ} (S : Submodule Bit (Pauli n)) : Fintype S := Fintype.ofFinite S

/-- Exact phases and multiplication are part of the supplied stabilizer group.
Constructing this data from arbitrary binary generators is a separate problem. -/
structure Lift {n : ℕ} (S : Submodule Bit (Pauli n)) where
  op : S → Square (Word n)
  phase : S → ℂ
  op_eq_phase : ∀ s, op s = phase s • pauli s.val
  map_zero : op 0 = 1
  map_add : ∀ s t, op (s+t) = op s * op t
  unitary : ∀ s, (op s)ᴴ * op s = 1

variable {n : ℕ} {S : Submodule Bit (Pauli n)}
namespace Lift
variable (L : Lift S)

theorem index_add_self (s : S) : s+s=0 := Subtype.ext (pauliLabel_add_self s.val)

theorem operator_square (s : S) : L.op s * L.op s = 1 := by
  rw [← L.map_add, index_add_self, L.map_zero]

theorem operator_hermitian (s : S) : (L.op s).IsHermitian := by
  change (L.op s)ᴴ = L.op s
  calc
    (L.op s)ᴴ = (L.op s)ᴴ * (L.op s * L.op s) := by rw [L.operator_square, Matrix.mul_one]
    _ = ((L.op s)ᴴ * L.op s) * L.op s := (Matrix.mul_assoc _ _ _).symm
    _ = L.op s := by rw [L.unitary, Matrix.one_mul]

theorem operator_commute (s t : S) : Commute (L.op s) (L.op t) := by
  change L.op s * L.op t = L.op t * L.op s
  rw [← L.map_add, ← L.map_add, add_comm s t]


theorem phase_ne_zero (s : S) : L.phase s ≠ 0 := by
  intro h
  have hu := L.unitary s
  rw [L.op_eq_phase, h, zero_smul, Matrix.conjTranspose_zero, Matrix.zero_mul] at hu
  have he := congrFun (congrFun hu (0 : Word n)) 0
  simp at he

include L in
theorem isotropic : S ≤ QecReliability.normalizer (symplectic n) S := by
  intro v hv u hu
  let s : S := ⟨u, hu⟩
  let t : S := ⟨v, hv⟩
  have h := (L.operator_commute s t).eq
  simp only [L.op_eq_phase, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h
  rw [mul_comm (L.phase t) (L.phase s)] at h
  have hn : L.phase s * L.phase t ≠ 0 := mul_ne_zero (L.phase_ne_zero s) (L.phase_ne_zero t)
  have hc := congrArg (fun M : Square (Word n) => (L.phase s * L.phase t)⁻¹ • M) h
  simp only [smul_smul, inv_mul_cancel₀ hn, one_smul] at hc
  exact (pauli_commute_iff u v).mp hc

theorem operator_trace (s : S) :
    (L.op s).trace = if s = 0 then (Fintype.card (Word n) : ℂ) else 0 := by
  classical
  by_cases hs : s = 0
  · simp [hs, L.map_zero]
  · have hv : s.val ≠ 0 := fun h => hs (Subtype.ext h)
    rw [L.op_eq_phase, Matrix.trace_smul, pauli_trace, if_neg hv, smul_zero, if_neg hs]

def projector : Square (Word n) := (Fintype.card S : ℂ)⁻¹ • ∑ s : S, L.op s

theorem card_ne_zero : (Fintype.card S : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

theorem projector_left_fixed (s : S) : L.op s * L.projector = L.projector := by
  unfold projector
  rw [Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  simpa only [L.map_add] using
    Fintype.sum_bijective (fun t : S => s+t) (Equiv.addLeft s).bijective
      (fun t : S => L.op (s+t)) L.op (fun _ => rfl)

theorem projector_idempotent : L.projector * L.projector = L.projector := by
  calc
    L.projector * L.projector =
        (Fintype.card S : ℂ)⁻¹ • ∑ s : S, L.op s * L.projector := by
      rw [projector, Matrix.smul_mul, Matrix.sum_mul]
    _ = (Fintype.card S : ℂ)⁻¹ • ((Fintype.card S : ℂ) • L.projector) := by
      simp only [L.projector_left_fixed, Finset.sum_const, Finset.card_univ,
        Nat.cast_smul_eq_nsmul]
    _ = L.projector := by rw [smul_smul, inv_mul_cancel₀ (card_ne_zero (S := S)), one_smul]

theorem projector_hermitian : L.projector.IsHermitian := by
  change L.projectorᴴ = L.projector
  have h (s : S) : (L.op s)ᴴ = L.op s := (L.operator_hermitian s).eq
  simp [projector, Matrix.conjTranspose_sum, h]

theorem projector_posSemidef : L.projector.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self L.projector
  rw [L.projector_hermitian.eq, L.projector_idempotent] at h
  exact h

def codeSpace : Submodule ℂ (Word n → ℂ) where
  carrier := {v | ∀ s : S, L.op s *ᵥ v = v}
  zero_mem' := by intro s; simp
  add_mem' := by intro v w hv hw s; rw [Matrix.mulVec_add, hv s, hw s]
  smul_mem' := by intro c v hv s; rw [Matrix.mulVec_smul, hv s]

theorem projector_mem (v : Word n → ℂ) : L.projector *ᵥ v ∈ L.codeSpace := by
  intro s
  rw [Matrix.mulVec_mulVec, L.projector_left_fixed]

theorem projector_fixes (v : Word n → ℂ) (hv : v ∈ L.codeSpace) : L.projector *ᵥ v = v := by
  change ∀ s : S, L.op s *ᵥ v = v at hv
  rw [projector, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [hv, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne_zero (S := S)), one_smul]

theorem isProj : LinearMap.IsProj L.codeSpace L.projector.toLin' :=
  ⟨L.projector_mem, L.projector_fixes⟩

theorem projector_trace : L.projector.trace =
    (Fintype.card S : ℂ)⁻¹ * (Fintype.card (Word n) : ℂ) := by
  classical
  rw [projector, Matrix.trace_smul, Matrix.trace_sum]
  simp [L.operator_trace]

theorem codeSpace_finrank_mul_card :
    Module.finrank ℂ L.codeSpace * Fintype.card S = Fintype.card (Word n) := by
  have ht := L.isProj.trace
  rw [Matrix.trace_toLin'_eq, L.projector_trace] at ht
  have hc : (Module.finrank ℂ L.codeSpace : ℂ) * (Fintype.card S : ℂ) =
      (Fintype.card (Word n) : ℂ) := by
    rw [← ht]
    field_simp
  exact_mod_cast hc

theorem index_card : Fintype.card S = 2 ^ Module.finrank Bit S := by
  rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := Bit)]
  simp [Bit, Nat.card_eq_fintype_card, ZMod.card]

theorem codeSpace_finrank (hS : S ≤ QecReliability.normalizer (symplectic n) S) :
    Module.finrank ℂ L.codeSpace = 2 ^ (n - Module.finrank Bit S) := by
  have h := L.codeSpace_finrank_mul_card
  rw [index_card, card_word] at h
  have hr := isotropic_finrank_le S hS
  have hp : 2 ^ n = 2 ^ (n - Module.finrank Bit S) * 2 ^ Module.finrank Bit S := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) (h.trans hp)


/-- The supplied phase-consistent lift itself forces isotropy. -/
theorem codeSpace_finrank_exact :
    Module.finrank ℂ L.codeSpace = 2 ^ (n - Module.finrank Bit S) :=
  L.codeSpace_finrank L.isotropic

end Lift
end QecPhysical.Stabilizer
