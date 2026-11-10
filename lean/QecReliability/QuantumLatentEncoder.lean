import QecReliability.LatentEncoder

/-! Both quantum sides, supplied latent DAGs, and exact latent coefficient counts. -/
namespace QecReliability.SharedCircuit
open PrefixCNF
namespace LatentEncoding

def quantumWitness {n : ℕ} (rows : List (List (PauliCoord n))) : Bool → ℕ
  | false => BadEncoding.witnessSize n
  | true => GoodEncoding.witnessSize rows

def quantumBlock {n : ℕ} (rows : List (List (PauliCoord n))) :
    (side : Bool) → Block (BadEncoding.projectionSize n + quantumWitness rows side)
  | false => BadEncoding.block rows
  | true => GoodEncoding.block rows

theorem quantumBlock_correct {n : ℕ} (rows : List (List (PauliCoord n))) (side : Bool)
    (a : BitModels (BadEncoding.projectionSize n)) :
    Projected (quantumBlock rows side).projectedFormula a ↔
      BadEncoding.pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Binary.coefficientPredicate (rowSpace rows) id side (BadEncoding.erasures a) (BadEncoding.pauli a) := by
  cases side
  · exact BadEncoding.projected_correct rows a
  · exact GoodEncoding.projected_correct rows a

theorem quantumBlock_size {n : ℕ} (rows : List (List (PauliCoord n))) (side : Bool) :
    quantumWitness rows side + (quantumBlock rows side).aux ≤ 6 * n + 4 * rowIncidences rows + 1 ∧
    (quantumBlock rows side).formula.length ≤ 18 * rowIncidences rows + 18 * n + 5 ∧
    Width 3 (quantumBlock rows side).formula ∧ (quantumBlock rows side).Deterministic := by
  cases side
  · have hg := badBlock_aux rows BadEncoding.eWire BadEncoding.zxWire BadEncoding.zzWire BadEncoding.xxWire BadEncoding.xzWire
    refine ⟨?_, badBlock_length _ _ _ _ _ _, badBlock_width _ _ _ _ _ _, badBlock_deterministic _ _ _ _ _ _⟩
    change (n + n) + (badBlock rows _ _ _ _ _).aux ≤ _
    omega
  · have h := goodBlock_size rows (GoodEncoding.eWire rows) (GoodEncoding.zxWire rows)
      (GoodEncoding.zzWire rows) (GoodEncoding.coeffWire rows)
    have hm := (trimRows_bounds rows).1
    refine ⟨?_, ?_, h.2.2.1, h.2.2.2⟩
    · change (trimRows rows).length + (goodBlock rows _ _ _ _).aux ≤ _
      omega
    · exact h.2.1.trans (by omega)

def quantumLayer {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) : Block (keySize n r + quantumWitness rows i.1) :=
  layerBlock C (quantumBlock rows i.1) i.2

theorem quantumLayer_key {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) (bz : Binary.CoefficientKey n r) :
    Projected (quantumLayer rows C i).projectedFormula (keyBits n r bz) ↔
      bz ∈ Binary.coefficientModels (rowSpace rows) (circuitMap C) i := by
  rw [quantumLayer, layer_projected _ _ _ (by omega), keyBits_causes, keyBits_physical,
    quantumBlock_correct, (BadEncoding.keyBits_decode _).1, (BadEncoding.keyBits_decode _).2]
  simp only [Binary.coefficientModels, Finset.mem_filter, Finset.mem_univ, true_and,
    Binary.coefficientPredicate, id_eq, hammingLayer, Fin.ext_iff]

theorem quantumLayer_projected {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) (a : BitModels (keySize n r)) :
    Projected (quantumLayer rows C i).projectedFormula a ↔
      (keyBits n r).symm a ∈ Binary.coefficientModels (rowSpace rows) (circuitMap C) i := by
  simpa only [Equiv.apply_symm_apply] using quantumLayer_key rows C i ((keyBits n r).symm a)

/-- Uniform bound for either side. True witnesses, latent gate outputs, reconstruction
outputs, and weight-counter auxiliaries all remain existential; only (b,z) is projected. -/
theorem quantumLayer_contract {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) :
    Width 3 (quantumLayer rows C i).projectedFormula ∧
    (quantumLayer rows C i).projectedFormula.length ≤
      18 * rowIncidences rows + 18 * n + 81 * r + 4 * C.gates + 52 ∧
    keySize n r + (quantumWitness rows i.1 + (quantumLayer rows C i).aux) ≤
      21 * r + 8 * n + 4 * rowIncidences rows + C.gates + 12 ∧
    (quantumLayer rows C i).Deterministic := by
  have hb := quantumBlock_size rows i.1
  have hl := layer_contract C (quantumBlock rows i.1) i.2 hb.2.2.1 hb.2.2.2
  refine ⟨Block.projectedFormula_width _ hl.2.2.1, ?_, ?_, hl.2.2.2⟩
  · rw [Block.projectedFormula_length]
    have hlen := hl.2.1
    change (quantumLayer rows C i).formula.length ≤ _ at hlen
    omega
  · change r + (n + n) + (quantumWitness rows i.1 + _) ≤ _
    change (quantumLayer rows C i).aux ≤ _ ∧ _ at hl
    omega

theorem quantumLayer_count {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) :
    PrefixEnumeration.modelCount (Projected (quantumLayer rows C i).projectedFormula) =
      if i.1 then Binary.goodCoefficient (rowSpace rows) (circuitMap C) i.2
      else Binary.badCoefficient (rowSpace rows) (circuitMap C) i.2 := by
  have he : Projected (quantumLayer rows C i).projectedFormula =
      fun a => (keyBits n r).symm a ∈ Binary.coefficientModels (rowSpace rows) (circuitMap C) i := by
    funext a
    exact propext (quantumLayer_projected rows C i a)
  rw [he, encoded_modelCount, Binary.coefficientModels_card]

def quantumCell {n r t : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) (H : Program (keySize n r) t) (target : BitModels t) :=
  (quantumLayer rows C i).hashCell H target

theorem quantumCell_projected {n r t : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) (H : Program (keySize n r) t) (target : BitModels t)
    (a : BitModels (keySize n r)) :
    Projected (quantumCell rows C i H target).projectedFormula a ↔
      (keyBits n r).symm a ∈ Binary.coefficientModels (rowSpace rows) (circuitMap C) i ∧ H.eval a = target := by
  rw [quantumCell, Block.hashCell_projected, quantumLayer_projected]

theorem quantumCell_contract {n r t : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) (H : Program (keySize n r) t) (target : BitModels t) :
    Width 3 (quantumCell rows C i H target).projectedFormula ∧
    (quantumCell rows C i H target).projectedFormula.length ≤
      18 * rowIncidences rows + 18 * n + 81 * r + 4 * C.gates + 4 * H.gates + t + 52 ∧
    keySize n r + (quantumWitness rows i.1 + (quantumCell rows C i H target).aux) ≤
      21 * r + 8 * n + 4 * rowIncidences rows + C.gates + H.gates + 12 ∧
    (quantumCell rows C i H target).Deterministic := by
  have hbase := quantumLayer_contract rows C i
  have hbw := (layer_contract C (quantumBlock rows i.1) i.2
    (quantumBlock_size rows i.1).2.2.1 (quantumBlock_size rows i.1).2.2.2).2.2.1
  have hh := Block.hashCell_contract (quantumLayer rows C i) H target hbw hbase.2.2.2
  refine ⟨Block.projectedFormula_width _ hh.2.2.1, ?_, ?_, hh.2.2.2⟩
  · rw [Block.projectedFormula_length]
    have hl := hbase.2.1
    rw [Block.projectedFormula_length] at hl
    have hlen := hh.2.1
    change (quantumCell rows C i H target).formula.length ≤ _ at hlen
    omega
  · change keySize n r + (quantumWitness rows i.1 + ((quantumLayer rows C i).aux + H.gates)) ≤ _
    omega

end LatentEncoding
end QecReliability.SharedCircuit
