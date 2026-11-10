import QecReliability.TensorCoefficientCounting
import QecReliability.ConcreteQuantumConfidence

/-! Concrete multiclass quantum queries. A supplied latent DAG reads the
concatenation of all class bits. Every class gets its own proved population
counter; only witnesses and circuit/counter auxiliaries are existential. -/

namespace QecReliability.SharedCircuit.TensorEncoding
open PrefixCNF TensorBernstein TensorLatent
open scoped BigOperators

abbrev indexList := TensorLatent.indexList

/-- Conjoin independent Hamming-weight constraints on contiguous class blocks. -/
def weightsBlock {v : ℕ} : (ds : List ℕ) → (Fin ds.sum → Fin v) → Grid ds → Block v
  | [], _, _ => Block.empty v
  | r :: ds, xs, j =>
    (weightBlock (fun i => xs (Fin.castAdd ds.sum i)) j.1.val).and
      (weightsBlock ds (fun i => xs (Fin.natAdd r i)) j.2)

theorem weightsBlock_correct {v : ℕ} (ds : List ℕ) (xs : Fin ds.sum → Fin v)
    (j : Grid ds) (a : BitModels v) :
    (weightsBlock ds xs j).Accepts a ↔
      layerIndex ds ((causesBits ds).symm (a ∘ xs)) = j := by
  induction ds with
  | nil =>
    cases j
    simp [weightsBlock,Block.empty,Block.Accepts,PrefixCNF.eval,layerIndex]
    rfl
  | cons r ds ih =>
    rcases j with ⟨j,js⟩
    change ((weightBlock (fun i => xs (Fin.castAdd ds.sum i)) j.val).and
      (weightsBlock ds (fun i => xs (Fin.natAdd r i)) js)).Accepts a ↔
      (hammingLayer (wiredErasures a (fun i => xs (Fin.castAdd ds.sum i))),
        layerIndex ds ((causesBits ds).symm (a ∘ fun i => xs (Fin.natAdd r i)))) = (j,js)
    rw [Block.and_accepts,
      weightBlock_correct _ _ (Nat.le_of_lt_succ j.isLt),ih]
    change ((∑ i, (a (xs (Fin.castAdd ds.sum i))).toNat) = j.val ∧
      layerIndex ds ((causesBits ds).symm (a ∘ fun i => xs (Fin.natAdd r i))) = js) ↔
      (hammingLayer (wiredErasures a (fun i => xs (Fin.castAdd ds.sum i))),
        layerIndex ds ((causesBits ds).symm (a ∘ fun i => xs (Fin.natAdd r i)))) = (j,js)
    simp only [Prod.mk.injEq,hammingLayer,Fin.ext_iff,wiredErasures_card]

theorem weightsBlock_contract {v : ℕ} (ds : List ℕ) (xs : Fin ds.sum → Fin v) (j : Grid ds) :
    (weightsBlock ds xs j).aux ≤ 20*ds.sum+11*ds.length ∧
    (weightsBlock ds xs j).formula.length ≤ 81*ds.sum+47*ds.length ∧
    Width 3 (weightsBlock ds xs j).formula ∧ (weightsBlock ds xs j).Deterministic := by
  induction ds with
  | nil =>
    refine ⟨by simp [weightsBlock,Block.empty],by simp [weightsBlock,Block.empty],?_,?_⟩
    · intro c hc; cases hc
    · intro a u v _ _
      funext k
      exact Fin.elim0 k
  | cons r ds ih =>
    have hh := weightBlock_size (fun i => xs (Fin.castAdd ds.sum i)) j.1.val
    have ht := ih (fun i => xs (Fin.natAdd r i)) j.2
    refine ⟨?_,?_,Block.and_width _ _ hh.2.2.1 ht.2.2.1,
      Block.and_deterministic _ _ hh.2.2.2 ht.2.2.2⟩
    · change (weightBlock _ _).aux+(weightsBlock ds _ _).aux ≤ _
      simp only [List.sum_cons,List.length_cons]
      omega
    · rw [weightsBlock,Block.and_length]
      simp only [List.sum_cons,List.length_cons]
      omega

def circuitMap {n : ℕ} {ds : List ℕ} (C : Program ds.sum n) (b : CausesGrid ds) : Finset (Fin n) :=
  LatentEncoding.circuitMap C (flattenCauses ds b)

def quantumLayer (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds) :
    Block (LatentEncoding.keySize n ds.sum+LatentEncoding.quantumWitness rows i.1) :=
  (LatentEncoding.pullback C (LatentEncoding.quantumBlock rows i.1)).and
    (weightsBlock ds LatentEncoding.causeWire i.2)

theorem quantumLayer_projected_bits (ds : List ℕ) {n : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program ds.sum n)
    (i : TensorCoefficientCounting.Index ds) (a : BitModels (LatentEncoding.keySize n ds.sum)) :
    Projected (quantumLayer ds rows C i).projectedFormula a ↔
      layerIndex ds ((causesBits ds).symm (LatentEncoding.causes a)) = i.2 ∧
      Projected (LatentEncoding.quantumBlock rows i.1).projectedFormula
        (LatentEncoding.physicalKey C a) := by
  have hw : ∀ b : BitModels (LatentEncoding.quantumWitness rows i.1),
      (weightsBlock ds LatentEncoding.causeWire i.2).Accepts (Fin.append a b) ↔
        layerIndex ds ((causesBits ds).symm (LatentEncoding.causes a)) = i.2 := by
    intro b
    rw [weightsBlock_correct]
    have he : Fin.append a b ∘ LatentEncoding.causeWire = LatentEncoding.causes a := by
      funext k
      exact Fin.append_left _ _ _
    rw [he]
  rw [Block.projectedFormula_correct]
  simp only [quantumLayer,Block.and_accepts]
  simp_rw [hw]
  rw [← LatentEncoding.pullback_projected C (LatentEncoding.quantumBlock rows i.1) a,
    Block.projectedFormula_correct]
  constructor
  · rintro ⟨b,hb,hj⟩; exact ⟨hj,b,hb⟩
  · rintro ⟨hj,b,hb⟩; exact ⟨b,hb,hj⟩

theorem keyBits_causes {n : ℕ} (ds : List ℕ) (bz : TensorCoefficientCounting.Key n ds) :
    LatentEncoding.causes (TensorCoefficientCounting.keyBits n ds bz) = causesBits ds bz.1 := by
  funext k
  change Fin.append (Binary.causeBits ds.sum (flattenCauses ds bz.1)) _
    (Fin.castAdd (n+n) k) = causesBits ds bz.1 k
  rw [Fin.append_left]
  change Binary.causeBits ds.sum ((Binary.causeBits ds.sum).symm (causesBits ds bz.1)) k = _
  rw [Equiv.apply_symm_apply]

theorem quantumLayer_key (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds)
    (bz : TensorCoefficientCounting.Key n ds) :
    Projected (quantumLayer ds rows C i).projectedFormula
      (TensorCoefficientCounting.keyBits n ds bz) ↔
      bz ∈ TensorCoefficientCounting.coefficientModels (rowSpace rows) (circuitMap C) i := by
  classical
  rw [quantumLayer_projected_bits,keyBits_causes,Equiv.symm_apply_apply]
  have hp := LatentEncoding.keyBits_physical C (flattenCauses ds bz.1,bz.2)
  change LatentEncoding.physicalKey C (TensorCoefficientCounting.keyBits n ds bz) =
    BadEncoding.keyBits n (circuitMap C bz.1,bz.2) at hp
  rw [hp,LatentEncoding.quantumBlock_correct,
    (BadEncoding.keyBits_decode _).1,(BadEncoding.keyBits_decode _).2]
  unfold TensorCoefficientCounting.coefficientModels
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and,TensorCoefficientCounting.coefficientPredicate,
    Binary.coefficientPredicate,id_eq]

theorem quantumLayer_projected (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds)
    (a : BitModels (LatentEncoding.keySize n ds.sum)) :
    Projected (quantumLayer ds rows C i).projectedFormula a ↔
      (TensorCoefficientCounting.keyBits n ds).symm a ∈
        TensorCoefficientCounting.coefficientModels (rowSpace rows) (circuitMap C) i := by
  simpa only [Equiv.apply_symm_apply] using
    quantumLayer_key ds rows C i ((TensorCoefficientCounting.keyBits n ds).symm a)

theorem quantumLayer_width (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds) :
    Width 3 (quantumLayer ds rows C i).formula := by
  have hb := LatentEncoding.quantumBlock_size rows i.1
  have hp := LatentEncoding.pullback_contract C (LatentEncoding.quantumBlock rows i.1)
    hb.2.2.1 hb.2.2.2
  have hw := weightsBlock_contract ds
    (LatentEncoding.causeWire (n := n) (w := LatentEncoding.quantumWitness rows i.1)) i.2
  exact Block.and_width _ _ hp.2.2.1 hw.2.2.1

theorem quantumLayer_contract (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds) :
    Width 3 (quantumLayer ds rows C i).projectedFormula ∧
    (quantumLayer ds rows C i).projectedFormula.length ≤
      18*rowIncidences rows+18*n+81*ds.sum+47*ds.length+4*C.gates+5 ∧
    LatentEncoding.keySize n ds.sum+
        (LatentEncoding.quantumWitness rows i.1+(quantumLayer ds rows C i).aux) ≤
      21*ds.sum+8*n+4*rowIncidences rows+C.gates+11*ds.length+1 ∧
    (quantumLayer ds rows C i).Deterministic := by
  have hb := LatentEncoding.quantumBlock_size rows i.1
  have hp := LatentEncoding.pullback_contract C (LatentEncoding.quantumBlock rows i.1)
    hb.2.2.1 hb.2.2.2
  have hw := weightsBlock_contract ds
    (LatentEncoding.causeWire (n := n) (w := LatentEncoding.quantumWitness rows i.1)) i.2
  have hwidth := Block.and_width _ _ hp.2.2.1 hw.2.2.1
  refine ⟨Block.projectedFormula_width _ hwidth,?_,?_,
    Block.and_deterministic _ _ hp.2.2.2 hw.2.2.2⟩
  · rw [Block.projectedFormula_length,quantumLayer,Block.and_length]
    omega
  · change ds.sum+(n+n)+(LatentEncoding.quantumWitness rows i.1+
      ((LatentEncoding.pullback C (LatentEncoding.quantumBlock rows i.1)).aux+
        (weightsBlock ds LatentEncoding.causeWire i.2).aux)) ≤ _
    omega

theorem quantumLayer_count (ds : List ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds) :
    PrefixEnumeration.modelCount (Projected (quantumLayer ds rows C i).projectedFormula) =
      (TensorCoefficientCounting.coefficientModels (rowSpace rows) (circuitMap C) i).card := by
  have he : Projected (quantumLayer ds rows C i).projectedFormula =
      fun a => (TensorCoefficientCounting.keyBits n ds).symm a ∈
        TensorCoefficientCounting.coefficientModels (rowSpace rows) (circuitMap C) i := by
    funext a
    exact propext (quantumLayer_projected ds rows C i a)
  rw [he,encoded_modelCount]

def quantumCell (ds : List ℕ) {n t : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds)
    (H : Program (LatentEncoding.keySize n ds.sum) t) (target : BitModels t) :=
  (quantumLayer ds rows C i).hashCell H target

theorem quantumCell_projected (ds : List ℕ) {n t : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds)
    (H : Program (LatentEncoding.keySize n ds.sum) t) (target : BitModels t)
    (a : BitModels (LatentEncoding.keySize n ds.sum)) :
    Projected (quantumCell ds rows C i H target).projectedFormula a ↔
      (TensorCoefficientCounting.keyBits n ds).symm a ∈
        TensorCoefficientCounting.coefficientModels (rowSpace rows) (circuitMap C) i ∧ H.eval a=target := by
  rw [quantumCell,Block.hashCell_projected,quantumLayer_projected]

theorem quantumCell_width (ds : List ℕ) {n t : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds)
    (H : Program (LatentEncoding.keySize n ds.sum) t) (target : BitModels t) :
    Width 3 (quantumCell ds rows C i H target).projectedFormula := by
  apply Block.projectedFormula_width
  apply Block.and_width
  · have hb := LatentEncoding.quantumBlock_size rows i.1
    have hp := LatentEncoding.pullback_contract C (LatentEncoding.quantumBlock rows i.1)
      hb.2.2.1 hb.2.2.2
    have hw := weightsBlock_contract ds
      (LatentEncoding.causeWire (n := n) (w := LatentEncoding.quantumWitness rows i.1)) i.2
    exact Block.and_width _ _ hp.2.2.1 hw.2.2.1
  · exact Program.matchBlock_width _ _

theorem quantumCell_contract (ds : List ℕ) {n t : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program ds.sum n) (i : TensorCoefficientCounting.Index ds)
    (H : Program (LatentEncoding.keySize n ds.sum) t) (target : BitModels t) :
    Width 3 (quantumCell ds rows C i H target).projectedFormula ∧
    (quantumCell ds rows C i H target).projectedFormula.length ≤
      18*rowIncidences rows+18*n+81*ds.sum+47*ds.length+4*C.gates+4*H.gates+t+5 ∧
    LatentEncoding.keySize n ds.sum+
        (LatentEncoding.quantumWitness rows i.1+(quantumCell ds rows C i H target).aux) ≤
      21*ds.sum+8*n+4*rowIncidences rows+C.gates+H.gates+11*ds.length+1 ∧
    (quantumCell ds rows C i H target).Deterministic := by
  have hb := quantumLayer_contract ds rows C i
  have hh := Block.hashCell_contract (quantumLayer ds rows C i) H target
    (quantumLayer_width ds rows C i) hb.2.2.2
  refine ⟨quantumCell_width ds rows C i H target,?_,?_,hh.2.2.2⟩
  · rw [Block.projectedFormula_length]
    have hl := hb.2.1
    rw [Block.projectedFormula_length] at hl
    have hlen := hh.2.1
    change (quantumCell ds rows C i H target).formula.length ≤ _ at hlen
    omega
  · change LatentEncoding.keySize n ds.sum+
      (LatentEncoding.quantumWitness rows i.1+((quantumLayer ds rows C i).aux+H.gates)) ≤ _
    omega

/-- Actual prefix-restricted width-three CNFs supply every base and hash-cell decision. -/
def queries {Ω : Type*} [Fintype Ω] (ds : List ℕ) {n : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program ds.sum n)
    (H : HashStages Ω (TensorCoefficientCounting.Key n ds) (LatentEncoding.keySize n ds.sum))
    (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))
    (solver : ∀ v, ExactSAT v 3) (i : TensorCoefficientCounting.Index ds) :
    DecisionQueries (TensorCoefficientCounting.keyBits n ds) H
      (TensorCoefficientCounting.coefficientModels (rowSpace rows) (circuitMap C) i) where
  base :=
    { answer pre := (solver _).solve (PrefixCNF.restrict (quantumLayer ds rows C i).projectedFormula pre)
      correct pre := by
        rw [(solver _).correct _ (PrefixCNF.restrict_width (quantumLayer_contract ds rows C i).1 (by omega) pre),
          PrefixCNF.restrict_sat]
        simp only [PrefixEnumeration.PrefixSat,quantumLayer_projected] }
  cell s ω :=
    { answer pre := (solver _).solve (PrefixCNF.restrict
        (quantumCell ds rows C i (K.program s ω) (fun _ => false)).projectedFormula pre)
      correct pre := by
        rw [(solver _).correct _ (PrefixCNF.restrict_width
          (quantumCell_width ds rows C i (K.program s ω) (fun _ => false)) (by omega) pre),
          PrefixCNF.restrict_sat]
        simp only [PrefixEnumeration.PrefixSat,quantumCell_projected,K.zero_correct] }

end QecReliability.SharedCircuit.TensorEncoding
