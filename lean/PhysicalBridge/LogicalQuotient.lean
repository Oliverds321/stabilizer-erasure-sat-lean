import PhysicalBridge.LogicalCompression

/-! Logical labels are actual normalizer cosets modulo stabilizers. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace QecPhysical.Stabilizer
open scoped BigOperators
open Matrix Module
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ}

def stabilizerInNormalizer (S : Submodule Bit (Pauli n)) : Submodule Bit (Normalizer S) :=
  S.comap (Normalizer S).subtype

abbrev LogicalClass (S : Submodule Bit (Pauli n)) := Normalizer S ⧸ stabilizerInNormalizer S

instance logicalClassFintype (S : Submodule Bit (Pauli n)) : Fintype (LogicalClass S) :=
  Fintype.ofFinite _

def logicalRepresentative {S : Submodule Bit (Pauli n)} (c : LogicalClass S) : Normalizer S :=
  Quotient.out c

theorem logicalRepresentative_class {S : Submodule Bit (Pauli n)} (c : LogicalClass S) :
    (stabilizerInNormalizer S).mkQ (logicalRepresentative c) = c :=
  Submodule.Quotient.mk_out c

theorem logicalClass_finrank (S : Submodule Bit (Pauli n))
    (hS : S ≤ Normalizer S) : finrank Bit (LogicalClass S) = 2*(n-finrank Bit S) := by
  have hr : finrank Bit (stabilizerInNormalizer S) = finrank Bit S :=
    (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  rw [Submodule.finrank_quotient, hr, finrank_normalizer]
  have hs := isotropic_finrank_le S hS
  omega

theorem logicalClass_card (S : Submodule Bit (Pauli n)) (hS : S ≤ Normalizer S) :
    Fintype.card (LogicalClass S) = 2 ^ (2*(n-finrank Bit S)) := by
  rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := Bit), logicalClass_finrank S hS]
  simp [Bit, Nat.card_eq_fintype_card, ZMod.card]

theorem logicalRepresentative_separated {S : Submodule Bit (Pauli n)}
    (c d : LogicalClass S) (h : c≠d) :
    (logicalRepresentative c).val + (logicalRepresentative d).val ∉ S := by
  intro hmem
  apply h
  rw [← logicalRepresentative_class c, ← logicalRepresentative_class d]
  apply (Submodule.Quotient.eq (stabilizerInNormalizer S)).mpr
  change (logicalRepresentative c).val - (logicalRepresentative d).val ∈ S
  have hneg : -(logicalRepresentative d).val = (logicalRepresentative d).val := by
    exact (eq_neg_of_add_eq_zero_left (pauliLabel_add_self (logicalRepresentative d).val)).symm
  simpa only [sub_eq_add_neg, hneg] using hmem

namespace Lift
variable {S : Submodule Bit (Pauli n)} (L : Lift S)

def logicalClassOp (c : LogicalClass S) : Square L.LogicalIndex :=
  L.logicalOp (logicalRepresentative c)

theorem logicalClassOp_unitary (c : LogicalClass S) :
    (L.logicalClassOp c)ᴴ * L.logicalClassOp c = 1 := L.logicalOp_unitary _

theorem logicalClassOp_trace_inner (c d : LogicalClass S) :
    ((L.logicalClassOp c)ᴴ * L.logicalClassOp d).trace =
      if c=d then (Fintype.card L.LogicalIndex : ℂ) else 0 := by
  by_cases h : c=d
  · subst d
    rw [L.logicalClassOp_unitary, Matrix.trace_one, if_pos rfl]
  · rw [if_neg h]
    exact L.logicalOp_trace_inner_zero _ _ (logicalRepresentative_separated c d h)

theorem logicalClass_card_square :
    Fintype.card (LogicalClass S) = Fintype.card L.LogicalIndex * Fintype.card L.LogicalIndex := by
  rw [logicalClass_card S L.isotropic, L.logical_dimension,
    two_mul, pow_add]

instance logicalIndexNonempty : Nonempty L.LogicalIndex := by
  apply Fintype.card_pos_iff.mp
  rw [L.logical_dimension]
  positivity

end Lift
end QecPhysical.Stabilizer
