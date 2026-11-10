import WholeWrapperInputBounds
import OracleCost.FixedSlotFields

/-! Fixed-slot representation of the UNCHANGED 22 macro fields. Capacities and
word width are explicit polynomials of the genuine immutable input measure.
Logical round-trip is proved; physical setup/address/controller simulation are
separate, and no RAM-cost or whole-machine resource contract is introduced. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open MultiTape.FixedSlot

def slotWidth (L : ℕ) : ℕ := fieldPolynomial L+wordPolynomial L+1

def fixedFieldsBits (L : ℕ) (s : Config) : List Bool :=
  MultiTape.FixedSlot.fieldsBits (slotWidth L) (fieldPolynomial L) (configFields s)

def fixedFieldsCapacity (L : ℕ) : ℕ := 22*(fieldPolynomial L+1)*slotWidth L

theorem reachable_fixed_fields_fit {q r B m L : ℕ} {shape : Bool} {ext : External}
    (hq : q≤2*L) (hr : r≤L) (hR : 2*m+1≤6*L+5) (hB : B.size≤8+2*L)
    (hd : (endpointDenCap ext).size≤2*L+3)
    {s : Config} (h : Reachable q r B m shape ext s) :
    Fits (slotWidth L) (fieldPolynomial L) (configFields s) := by
  have hl := (reachable_input_length_subset hq hr hR hB h).1
  have hv := reachable_all_field_words h
  have hb := broadValueBound_input_bound q r B m L ext hq hr hR hB hd
  have hc : fieldPolynomial L<2^(slotWidth L) := by
    have ht := Nat.lt_size_self (fieldPolynomial L)
    have hs := audit_size_le_value (fieldPolynomial L)
    exact ht.trans_le (Nat.pow_le_pow_right (by decide) (by unfold slotWidth; omega))
  refine ⟨hl,fun xs hx => (hl xs hx).trans_lt hc,?_⟩
  intro xs hx x hm
  have hs : x.size≤slotWidth L :=
    (Nat.size_le_size (hv xs hx x hm)).trans (hb.trans (by unfold slotWidth; omega))
  exact Nat.size_le.mp hs

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- Source-facing exact decoding, not an assumption that a machine can access
an array slot at unit cost. L is literally the input's paperLength. -/
theorem reachable_fixed_fields_input {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (a b c d : ℕ) (ha : 0<a) (hc : 0<c)
    (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω)
    (D : ℕ) (shape : Bool) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service
      (rationalRepetitionBudget (2*(r+1)) c d) ω D ext)
    {s : Config} (hreach : Reachable (keySize n r) r (rationalCellBudget a b)
      (rationalRepetitionBudget (2*(r+1)) c d) shape ext s) :
    let L := InputEncoding.paperLength rows C a b c d
    Fits (slotWidth L) (fieldPolynomial L) (configFields s) ∧
      (fixedFieldsBits L s).length=fixedFieldsCapacity L ∧
      (∀ suffix, readFields (slotWidth L) (fieldPolynomial L) 22
        (fixedFieldsBits L s++suffix)=some (configFields s,suffix)) := by
  let L := InputEncoding.paperLength rows C a b c d
  obtain ⟨hn,hq,hr,hR,hB⟩ := InputEncoding.budget_parameters rows C a b c d ha hc
  have hd := endpointDenCap_input_size rows C H K service
    (rationalRepetitionBudget (2*(r+1)) c d) ω D L ext hboundary hn
  have hf := reachable_fixed_fields_fit hq hr hR hB hd hreach
  refine ⟨hf,?_,?_⟩
  · simpa only [fixedFieldsBits,configFields_length,fixedFieldsCapacity,Nat.mul_assoc] using
      fieldsBits_length (slotWidth L) (fieldPolynomial L) (configFields s) hf.lengths
  · intro suffix
    simpa only [fixedFieldsBits,configFields_length] using
      readFields_fieldsBits (slotWidth L) (fieldPolynomial L) (configFields s) suffix hf

end QecReliability.OracleCost.WholeWrapperCandidate
