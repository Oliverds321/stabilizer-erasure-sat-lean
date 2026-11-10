import QecReliability.BadEncoder
import QecReliability.WeightEncoder

/-! End-to-end width-three fixed-weight Bad certificate with projected (E,z) inputs. -/
namespace QecReliability.SharedCircuit
open PrefixCNF
open scoped BigOperators

theorem wiredErasures_card {n v : ℕ} (a : BitModels v) (e : Fin n → Fin v) :
    (wiredErasures a e).card = ∑ i, (a (e i)).toNat := by
  simp only [wiredErasures, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases a (e i) <;> rfl

namespace BadEncoding

def layerBlock {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ) : Block (primarySize n) :=
  (block rows).and (weightBlock eWire j)

def layerFormula {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ) :
    Formula (projectionSize n + (witnessSize n + (layerBlock rows j).aux)) :=
  (layerBlock rows j).projectedFormula

theorem layer_projected_correct {n : ℕ} (rows : List (List (PauliCoord n)))
    (j : ℕ) (hj : j ≤ n) (a : BitModels (projectionSize n)) :
    Projected (layerFormula rows j) a ↔ (erasures a).card = j ∧
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Bad (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported (erasures a)) (pauli a) := by
  have hw : ∀ b : BitModels (witnessSize n), (weightBlock eWire j).Accepts (Fin.append a b) ↔
      (erasures a).card = j := by
    intro b
    rw [weightBlock_correct _ _ hj, ← wiredErasures_card, (decode_primary a b).1]
  rw [layerFormula, Block.projectedFormula_correct]
  simp only [layerBlock, Block.and_accepts]
  simp_rw [hw]
  rw [← projected_correct rows a, formula, Block.projectedFormula_correct]
  constructor
  · rintro ⟨b, hb, hj'⟩; exact ⟨hj', b, hb⟩
  · rintro ⟨hj', b, hb⟩; exact ⟨b, hb, hj'⟩

/-- The full quantum Bad layer compiler, including a constructed population counter.
Only E,z are projected. x is existential, and the remaining bits are unique gate outputs
once E,z,x are fixed. No isotropy is needed for this syntactic/algebraic equivalence. -/
theorem layer_compiler_contract {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ) (hj : j ≤ n) :
    Width 3 (layerFormula rows j) ∧
    (layerFormula rows j).length ≤ 18 * rowIncidences rows + 99 * n + 52 ∧
    projectionSize n + (witnessSize n + (layerBlock rows j).aux) ≤
      29 * n + 4 * rowIncidences rows + 12 ∧
    (layerBlock rows j).Deterministic ∧
    ∀ a : BitModels (projectionSize n), Projected (layerFormula rows j) a ↔
      (erasures a).card = j ∧
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Bad (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported (erasures a)) (pauli a) := by
  have hw := weightBlock_size (eWire (n := n)) j
  have hb := compiler_contract rows
  refine ⟨Block.projectedFormula_width _ (Block.and_width _ _ (badBlock_width _ _ _ _ _ _) hw.2.2.1),
    ?_, ?_, Block.and_deterministic _ _ hb.2.2.2.1 hw.2.2.2, layer_projected_correct rows j hj⟩
  · rw [layerFormula, Block.projectedFormula_length, layerBlock, Block.and_length]
    have h := badBlock_length rows eWire zxWire zzWire xxWire xzWire
    change (block rows).formula.length ≤ _ at h
    omega
  · have h := badBlock_aux rows eWire zxWire zzWire xxWire xzWire
    change (block rows).aux ≤ _ at h
    change n + (n + n) + ((n + n) + ((block rows).aux + (weightBlock eWire j).aux)) ≤ _
    omega

def layerDecision {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ) (hj : j ≤ n)
    (solver : ExactSAT (projectionSize n + (witnessSize n + (layerBlock rows j).aux)) 3) :
    PrefixEnumeration.ExactDecision (fun a : BitModels (projectionSize n) =>
      (erasures a).card = j ∧
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Bad (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported (erasures a)) (pauli a)) where
  answer pre := solver.solve (PrefixCNF.restrict (layerFormula rows j) pre)
  correct pre := by
    rw [solver.correct _ (PrefixCNF.restrict_width (layer_compiler_contract rows j hj).1 (by omega) pre),
      PrefixCNF.restrict_sat]
    simp only [PrefixEnumeration.PrefixSat, layer_projected_correct rows j hj]

def keyBits (n : ℕ) : (Finset (Fin n) × Binary.Pauli n) ≃ BitModels (projectionSize n) :=
  ((Binary.causeBits n).prodCongr
    (((Equiv.piCongrRight (fun _ : Fin n => Binary.bitBool)).prodCongr
      (Equiv.piCongrRight (fun _ : Fin n => Binary.bitBool))).trans (Binary.appendBits n n))).trans
    (Binary.appendBits n (n + n))

theorem keyBits_decode {n : ℕ} (bz : Finset (Fin n) × Binary.Pauli n) :
    erasures (keyBits n bz) = bz.1 ∧ pauli (keyBits n bz) = bz.2 := by
  constructor
  · ext i
    simp [erasures, wiredErasures, keyBits, Binary.appendBits, Binary.causeBits]
  · apply Prod.ext <;> funext i
    · change boolBit (Fin.append _ _ (Fin.natAdd n (Fin.castAdd n i))) = _
      rw [Fin.append_right]
      change boolBit (Fin.append (fun i => Binary.bitBool (bz.2.1 i))
        (fun i => Binary.bitBool (bz.2.2 i)) (Fin.castAdd n i)) = _
      rw [Fin.append_left, boolBit_bitBool]
    · change boolBit (Fin.append _ _ (Fin.natAdd n (Fin.natAdd n i))) = _
      rw [Fin.append_right]
      change boolBit (Fin.append (fun i => Binary.bitBool (bz.2.1 i))
        (fun i => Binary.bitBool (bz.2.2 i)) (Fin.natAdd n i)) = _
      rw [Fin.append_right, boolBit_bitBool]

theorem projected_bad_coefficient {n : ℕ} (rows : List (List (PauliCoord n))) (j : Fin (n + 1)) :
    PrefixEnumeration.modelCount (Projected (layerFormula rows j)) =
      Binary.badCoefficient (rowSpace rows) (fun E : Causes n => E) j := by
  classical
  let M := Binary.coefficientModels (rowSpace rows) (fun E : Causes n => E) (false, j)
  have he : ∀ bz : Binary.CoefficientKey n n,
      bz ∈ M ↔ keyBits n bz ∈ PrefixEnumeration.models (Projected (layerFormula rows j)) := by
    intro bz
    simp only [M, Binary.coefficientModels, PrefixEnumeration.models,
      Finset.mem_filter, Finset.mem_univ, true_and,
      layer_projected_correct rows j (by omega), (keyBits_decode bz).1, (keyBits_decode bz).2,
      Binary.coefficientPredicate, Bool.false_eq_true, ↓reduceIte]
    rw [Fin.ext_iff]
    rfl
  have hc := Finset.card_equiv (keyBits n) he
  rw [PrefixEnumeration.modelCount, ← hc]
  exact Binary.coefficientModels_card (rowSpace rows) (fun E : Causes n => E) (false, j)

/-- Concrete exact SAT suffices for capped counting of the actual Bad coefficient;
the query count is instrumented by the existing recursive prefix enumerator. -/
theorem layer_capped_count {n : ℕ} (rows : List (List (PauliCoord n))) (j : Fin (n + 1))
    (solver : ExactSAT (projectionSize n + (witnessSize n + (layerBlock rows j).aux)) 3) (cap : ℕ) :
    (PrefixEnumeration.enumerate (projectionSize n)
      (fun pre => solver.solve (PrefixCNF.restrict (layerFormula rows j) pre)) cap).1 =
        min cap (Binary.badCoefficient (rowSpace rows) (fun E : Causes n => E) j) ∧
    (PrefixEnumeration.enumerate (projectionSize n)
      (fun pre => solver.solve (PrefixCNF.restrict (layerFormula rows j) pre)) cap).2 ≤
        1 + 6 * n * min cap (Binary.badCoefficient (rowSpace rows) (fun E : Causes n => E) j) := by
  have h := PrefixCNF.projected_enumeration solver (layerFormula rows j)
    (layer_compiler_contract rows j (by omega)).1 (by omega) cap
  rw [projected_bad_coefficient] at h
  simpa only [projectionSize, show 2 * (n + (n + n)) = 6 * n by omega] using h

end BadEncoding
end QecReliability.SharedCircuit
