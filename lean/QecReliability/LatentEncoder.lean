import QecReliability.BlockComposition

/-! Composition of a supplied latent DAG with an existing quantum block.
The projected keys remain latent causes and z, not erased sets. -/
namespace QecReliability.SharedCircuit
open PrefixCNF

namespace LatentEncoding

abbrev keySize (n r : ℕ) := r + (n + n)

def causes {n r : ℕ} (a : BitModels (keySize n r)) : BitModels r := fun i => a (Fin.castAdd (n + n) i)
def zBits {n r : ℕ} (a : BitModels (keySize n r)) : BitModels (n + n) := fun i => a (Fin.natAdd r i)

def physicalKey {n r : ℕ} (C : Program r n) (a : BitModels (keySize n r)) : BitModels (BadEncoding.projectionSize n) :=
  Fin.append (C.eval (causes a)) (zBits a)

def latentProgram {n r : ℕ} (C : Program r n) (w : ℕ) : Program (keySize n r + w) n :=
  C.rewire (fun i => Fin.castAdd w (Fin.castAdd (n + n) i))

def physicalWire {n r : ℕ} (C : Program r n) (w : ℕ) :
    Fin (BadEncoding.projectionSize n + w) → Fin ((keySize n r + w) + C.gates) :=
  Fin.addCases
    (Fin.addCases (latentProgram C w).output
      (fun i => Fin.castAdd C.gates (Fin.castAdd w (Fin.natAdd r i))))
    (fun i => Fin.castAdd C.gates (Fin.natAdd (keySize n r) i))

theorem physical_assignment {n r w : ℕ} (C : Program r n) (a : BitModels (keySize n r)) (b : BitModels w) :
    (latentProgram C w).circuit.run (Fin.append a b) ∘ physicalWire C w =
      Fin.append (physicalKey C a) b := by
  have hp : (latentProgram C w).eval (Fin.append a b) = C.eval (causes a) := by
    rw [latentProgram, Program.rewire_eval]
    congr 1
    funext i
    exact Fin.append_left _ _ _
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) j
    · simp only [Function.comp_apply, physicalWire, Fin.addCases_left, Fin.append_left]
      change (latentProgram C w).eval (Fin.append a b) t = Fin.append _ _ (Fin.castAdd (n + n) t)
      rw [hp, Fin.append_left]
    · simp only [Function.comp_apply, physicalWire, Fin.addCases_left, Fin.addCases_right, Fin.append_left]
      have h := Circuit.run_primary (latentProgram C w).circuit (Fin.append a b)
        (Fin.castAdd w (Fin.natAdd r t))
      rw [show (latentProgram C w).circuit.run (Fin.append a b)
        (Fin.castAdd C.gates (Fin.castAdd w (Fin.natAdd r t))) = a (Fin.natAdd r t) from
          h.trans (Fin.append_left _ _ _)]
      exact (Fin.append_right (C.eval (causes a)) (zBits a) t).symm
  · simp only [Function.comp_apply, physicalWire, Fin.addCases_right, Fin.append_right]
    exact (Circuit.run_primary (latentProgram C w).circuit (Fin.append a b)
      (Fin.natAdd (keySize n r) j)).trans (Fin.append_right _ _ _)

def pullback {n r w : ℕ} (C : Program r n) (B : Block (BadEncoding.projectionSize n + w)) :
    Block (keySize n r + w) :=
  Block.after (latentProgram C w).circuit (B.rewire (physicalWire C w))

theorem pullback_accepts {n r w : ℕ} (C : Program r n) (B : Block (BadEncoding.projectionSize n + w))
    (a : BitModels (keySize n r)) (b : BitModels w) :
    (pullback C B).Accepts (Fin.append a b) ↔ B.Accepts (Fin.append (physicalKey C a) b) := by
  rw [pullback, Block.after_accepts, Block.rewire_accepts, physical_assignment]

theorem pullback_projected {n r w : ℕ} (C : Program r n) (B : Block (BadEncoding.projectionSize n + w))
    (a : BitModels (keySize n r)) :
    Projected (pullback C B).projectedFormula a ↔ Projected B.projectedFormula (physicalKey C a) := by
  rw [Block.projectedFormula_correct, Block.projectedFormula_correct]
  exact exists_congr (fun b => pullback_accepts C B a b)

theorem pullback_contract {n r w : ℕ} (C : Program r n) (B : Block (BadEncoding.projectionSize n + w))
    (hwidth : Width 3 B.formula) (hdet : B.Deterministic) :
    (pullback C B).aux = C.gates + B.aux ∧
    (pullback C B).formula.length ≤ 4 * C.gates + B.formula.length ∧
    Width 3 (pullback C B).formula ∧ (pullback C B).Deterministic := by
  refine ⟨rfl, ?_, Block.after_width _ _ (Block.rewire_width _ _ hwidth),
    Block.after_deterministic _ _ (Block.rewire_deterministic _ _ hdet)⟩
  have h := Block.after_length (latentProgram C w).circuit (B.rewire (physicalWire C w))
  rw [Block.rewire_length] at h
  change (pullback C B).formula.length ≤ 4 * C.gates + B.formula.length at h
  exact h

def causeWire {n r w : ℕ} (i : Fin r) : Fin (keySize n r + w) := Fin.castAdd w (Fin.castAdd (n + n) i)

def layerBlock {n r w : ℕ} (C : Program r n) (B : Block (BadEncoding.projectionSize n + w)) (j : ℕ) :
    Block (keySize n r + w) := (pullback C B).and (weightBlock causeWire j)

def causeSet {n r : ℕ} (a : BitModels (keySize n r)) : Causes r := (Binary.causeBits r).symm (causes a)

theorem layer_projected {n r w : ℕ} (C : Program r n) (B : Block (BadEncoding.projectionSize n + w))
    (j : ℕ) (hj : j ≤ r) (a : BitModels (keySize n r)) :
    Projected (layerBlock C B j).projectedFormula a ↔
      (causeSet a).card = j ∧ Projected B.projectedFormula (physicalKey C a) := by
  have hw : ∀ b : BitModels w, (weightBlock (causeWire (n := n) (r := r)) j).Accepts (Fin.append a b) ↔
      (causeSet a).card = j := by
    intro b
    rw [weightBlock_correct _ _ hj]
    have he : causeSet a = wiredErasures (Fin.append a b) (causeWire (n := n) (r := r)) := by
      ext i
      simp [causeSet, Binary.causeBits, causes, wiredErasures, causeWire]
    rw [he, wiredErasures_card]
  rw [Block.projectedFormula_correct]
  simp only [layerBlock, Block.and_accepts]
  simp_rw [hw]
  rw [← pullback_projected C B a, Block.projectedFormula_correct]
  constructor
  · rintro ⟨b, hb, hc⟩; exact ⟨hc, b, hb⟩
  · rintro ⟨hc, b, hb⟩; exact ⟨b, hb, hc⟩

theorem layer_contract {n r w : ℕ} (C : Program r n) (B : Block (BadEncoding.projectionSize n + w))
    (j : ℕ) (hwidth : Width 3 B.formula) (hdet : B.Deterministic) :
    (layerBlock C B j).aux ≤ C.gates + B.aux + 20 * r + 11 ∧
    (layerBlock C B j).formula.length ≤ 4 * C.gates + B.formula.length + 81 * r + 47 ∧
    Width 3 (layerBlock C B j).formula ∧ (layerBlock C B j).Deterministic := by
  have hp := pullback_contract C B hwidth hdet
  have hw := weightBlock_size (causeWire (n := n) (r := r) (w := w)) j
  refine ⟨?_, ?_, Block.and_width _ _ hp.2.2.1 hw.2.2.1,
    Block.and_deterministic _ _ hp.2.2.2 hw.2.2.2⟩
  · change (pullback C B).aux + (weightBlock causeWire j).aux ≤ _
    omega
  · rw [layerBlock, Block.and_length]
    omega

def keyBits (n r : ℕ) : Binary.CoefficientKey n r ≃ BitModels (keySize n r) :=
  ((Binary.causeBits r).prodCongr
    (((Equiv.piCongrRight (fun _ : Fin n => Binary.bitBool)).prodCongr
      (Equiv.piCongrRight (fun _ : Fin n => Binary.bitBool))).trans (Binary.appendBits n n))).trans
    (Binary.appendBits r (n + n))

def circuitMap {n r : ℕ} (C : Program r n) (b : Causes r) : Finset (Fin n) :=
  (Binary.causeBits n).symm (C.eval (Binary.causeBits r b))

theorem keyBits_causes {n r : ℕ} (bz : Binary.CoefficientKey n r) : causeSet (keyBits n r bz) = bz.1 := by
  have hc : causes (keyBits n r bz) = Binary.causeBits r bz.1 := by
    funext i
    exact Fin.append_left _ _ _
  change (Binary.causeBits r).symm (causes (keyBits n r bz)) = _
  rw [hc, Equiv.symm_apply_apply]

theorem keyBits_physical {n r : ℕ} (C : Program r n) (bz : Binary.CoefficientKey n r) :
    physicalKey C (keyBits n r bz) = BadEncoding.keyBits n (circuitMap C bz.1, bz.2) := by
  have hc : causes (keyBits n r bz) = Binary.causeBits r bz.1 := by
    funext i
    exact Fin.append_left _ _ _
  have hz : zBits (keyBits n r bz) = Fin.append
      (fun i => Binary.bitBool (bz.2.1 i)) (fun i => Binary.bitBool (bz.2.2 i)) := by
    funext i
    exact Fin.append_right _ _ _
  rw [physicalKey, hc, hz]
  change Fin.append _ _ = Fin.append (Binary.causeBits n (circuitMap C bz.1)) _
  unfold circuitMap
  rw [Equiv.apply_symm_apply]
  rfl

end LatentEncoding
end QecReliability.SharedCircuit
