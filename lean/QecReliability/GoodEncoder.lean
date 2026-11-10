import QecReliability.CleaningBlock

/-! Complete fixed-weight Good compiler with existential sparse generator coefficients. -/
namespace QecReliability.SharedCircuit
open PrefixCNF

def goodBlock {n v : ℕ} (rows : List (List (PauliCoord n))) (e zx zz : Fin n → Fin v)
    (coeff : Fin (trimRows rows).length → Fin v) : Block v :=
  (normalizerBlock rows zx zz).and
    ((Reconstruction.synthesize (trimRows rows) coeff).cleaningBlock e zx zz)

theorem goodBlock_correct {n v : ℕ} (rows : List (List (PauliCoord n))) (e zx zz : Fin n → Fin v)
    (coeff : Fin (trimRows rows).length → Fin v) (a : BitModels v) :
    (goodBlock rows e zx zz coeff).Accepts a ↔
      wiredPauli a zx zz ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      ∀ i ∈ wiredErasures a e,
        (combination (trimRows rows) (fun r => boolBit (a (coeff r)))).1 i = boolBit (a (zx i)) ∧
        (combination (trimRows rows) (fun r => boolBit (a (coeff r)))).2 i = boolBit (a (zz i)) := by
  rw [goodBlock, Block.and_accepts, normalizerBlock_correct, Reconstruction.cleaningBlock_correct,
    Reconstruction.synthesize_value]
  simp [wiredErasures]

theorem goodBlock_size {n v : ℕ} (rows : List (List (PauliCoord n))) (e zx zz : Fin n → Fin v)
    (coeff : Fin (trimRows rows).length → Fin v) :
    (goodBlock rows e zx zz coeff).aux ≤ 3 * rowIncidences rows + 1 ∧
    (goodBlock rows e zx zz coeff).formula.length ≤ 13 * rowIncidences rows + 4 * n + 4 ∧
    Width 3 (goodBlock rows e zx zz coeff).formula ∧ (goodBlock rows e zx zz coeff).Deterministic := by
  have hn := normalizerBlock_aux rows zx zz
  have hl := normalizerBlock_length rows zx zz
  have hg := Reconstruction.synthesize_gates (trimRows rows) coeff
  rw [(trimRows_bounds rows).2] at hg
  have hc := Reconstruction.cleaningBlock_length (Reconstruction.synthesize (trimRows rows) coeff) e zx zz
  refine ⟨?_, ?_, Block.and_width _ _ (normalizerBlock_width _ _ _) (Reconstruction.cleaningBlock_width _ _ _ _),
    Block.and_deterministic _ _ (normalizerBlock_deterministic _ _ _) (Reconstruction.cleaningBlock_deterministic _ _ _ _)⟩
  · change (normalizerBlock rows zx zz).aux + (Reconstruction.synthesize (trimRows rows) coeff).gates ≤ _
    omega
  · rw [goodBlock, Block.and_length]
    omega

namespace GoodEncoding
open BadEncoding (projectionSize erasures pauli keyBits keyBits_decode)

abbrev witnessSize {n : ℕ} (rows : List (List (PauliCoord n))) := (trimRows rows).length
abbrev primarySize {n : ℕ} (rows : List (List (PauliCoord n))) := projectionSize n + witnessSize rows

def eWire {n : ℕ} (rows : List (List (PauliCoord n))) (i : Fin n) : Fin (primarySize rows) :=
  Fin.castAdd (witnessSize rows) (Fin.castAdd (n + n) i)
def zxWire {n : ℕ} (rows : List (List (PauliCoord n))) (i : Fin n) : Fin (primarySize rows) :=
  Fin.castAdd (witnessSize rows) (Fin.natAdd n (Fin.castAdd n i))
def zzWire {n : ℕ} (rows : List (List (PauliCoord n))) (i : Fin n) : Fin (primarySize rows) :=
  Fin.castAdd (witnessSize rows) (Fin.natAdd n (Fin.natAdd n i))
def coeffWire {n : ℕ} (rows : List (List (PauliCoord n))) (i : Fin (witnessSize rows)) : Fin (primarySize rows) :=
  Fin.natAdd (projectionSize n) i

def block {n : ℕ} (rows : List (List (PauliCoord n))) : Block (primarySize rows) :=
  goodBlock rows (eWire rows) (zxWire rows) (zzWire rows) (coeffWire rows)

theorem block_correct {n : ℕ} (rows : List (List (PauliCoord n)))
    (a : BitModels (projectionSize n)) (b : BitModels (witnessSize rows)) :
    (block rows).Accepts (Fin.append a b) ↔
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      ∀ i ∈ erasures a, (combination (trimRows rows) (fun r => boolBit (b r))).1 i = (pauli a).1 i ∧
        (combination (trimRows rows) (fun r => boolBit (b r))).2 i = (pauli a).2 i := by
  rw [block, goodBlock_correct]
  simp only [eWire, zxWire, zzWire, coeffWire, Fin.append_left, Fin.append_right,
    wiredPauli, wiredErasures, pauli, erasures]

theorem projected_correct {n : ℕ} (rows : List (List (PauliCoord n))) (a : BitModels (projectionSize n)) :
    Projected (block rows).projectedFormula a ↔
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Good (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported (erasures a)) (pauli a) := by
  rw [Block.projectedFormula_correct, good_iff_generator_agreement]
  simp_rw [block_correct]
  constructor
  · rintro ⟨b, hz, hb⟩
    exact ⟨hz, (fun r => boolBit (b r)), hb⟩
  · rintro ⟨hz, c, hc⟩
    refine ⟨fun r => Binary.bitBool (c r), hz, ?_⟩
    simpa only [BadEncoding.boolBit_bitBool] using hc

def layerBlock {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ) : Block (primarySize rows) :=
  (block rows).and (weightBlock (eWire rows) j)

def layerFormula {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ) :
    Formula (projectionSize n + (witnessSize rows + (layerBlock rows j).aux)) :=
  (layerBlock rows j).projectedFormula

theorem layer_projected_correct {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ) (hj : j ≤ n)
    (a : BitModels (projectionSize n)) : Projected (layerFormula rows j) a ↔
      (erasures a).card = j ∧
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Good (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported (erasures a)) (pauli a) := by
  have hw : ∀ b : BitModels (witnessSize rows), (weightBlock (eWire rows) j).Accepts (Fin.append a b) ↔
      (erasures a).card = j := by
    intro b
    rw [weightBlock_correct _ _ hj, ← wiredErasures_card]
    simp [eWire, wiredErasures, erasures]
  rw [layerFormula, Block.projectedFormula_correct]
  simp only [layerBlock, Block.and_accepts]
  simp_rw [hw]
  rw [← projected_correct rows a, Block.projectedFormula_correct]
  constructor
  · rintro ⟨b, hb, hj'⟩; exact ⟨hj', b, hb⟩
  · rintro ⟨hj', b, hb⟩; exact ⟨b, hb, hj'⟩

/-- Complete Good layer encoding. Isotropy is needed later for the reliability fraction,
not for this equivalence to the defined cleaning predicate. -/
theorem layer_compiler_contract {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ) (hj : j ≤ n) :
    Width 3 (layerFormula rows j) ∧
    (layerFormula rows j).length ≤ 13 * rowIncidences rows + 85 * n + 51 ∧
    projectionSize n + (witnessSize rows + (layerBlock rows j).aux) ≤ 23 * n + 4 * rowIncidences rows + 12 ∧
    (layerBlock rows j).Deterministic ∧
    ∀ a : BitModels (projectionSize n), Projected (layerFormula rows j) a ↔
      (erasures a).card = j ∧
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Good (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported (erasures a)) (pauli a) := by
  have hb := goodBlock_size rows (eWire rows) (zxWire rows) (zzWire rows) (coeffWire rows)
  have hw := weightBlock_size (eWire rows) j
  have hm := (trimRows_bounds rows).1
  refine ⟨Block.projectedFormula_width _ (Block.and_width _ _ hb.2.2.1 hw.2.2.1), ?_, ?_,
    Block.and_deterministic _ _ hb.2.2.2 hw.2.2.2, layer_projected_correct rows j hj⟩
  · rw [layerFormula, Block.projectedFormula_length, layerBlock, Block.and_length]
    have hl := hb.2.1
    change (block rows).formula.length ≤ _ at hl
    omega
  · change n + (n + n) + ((trimRows rows).length + ((block rows).aux + (weightBlock (eWire rows) j).aux)) ≤ _
    change (block rows).aux ≤ _ ∧ _ at hb
    omega

theorem projected_good_coefficient {n : ℕ} (rows : List (List (PauliCoord n))) (j : Fin (n + 1)) :
    PrefixEnumeration.modelCount (Projected (layerFormula rows j)) =
      Binary.goodCoefficient (rowSpace rows) (fun E : Causes n => E) j := by
  classical
  let M := Binary.coefficientModels (rowSpace rows) (fun E : Causes n => E) (true, j)
  have he : ∀ bz : Binary.CoefficientKey n n,
      bz ∈ M ↔ keyBits n bz ∈ PrefixEnumeration.models (Projected (layerFormula rows j)) := by
    intro bz
    simp only [M, Binary.coefficientModels, PrefixEnumeration.models, Finset.mem_filter,
      Finset.mem_univ, true_and, layer_projected_correct rows j (by omega),
      (keyBits_decode bz).1, (keyBits_decode bz).2, Binary.coefficientPredicate, ↓reduceIte]
    rw [Fin.ext_iff]
    rfl
  have hc := Finset.card_equiv (keyBits n) he
  rw [PrefixEnumeration.modelCount, ← hc]
  exact Binary.coefficientModels_card (rowSpace rows) (fun E : Causes n => E) (true, j)

theorem layer_capped_count {n : ℕ} (rows : List (List (PauliCoord n))) (j : Fin (n + 1))
    (solver : ExactSAT (projectionSize n + (witnessSize rows + (layerBlock rows j).aux)) 3) (cap : ℕ) :
    (PrefixEnumeration.enumerate (projectionSize n)
      (fun pre => solver.solve (PrefixCNF.restrict (layerFormula rows j) pre)) cap).1 =
        min cap (Binary.goodCoefficient (rowSpace rows) (fun E : Causes n => E) j) ∧
    (PrefixEnumeration.enumerate (projectionSize n)
      (fun pre => solver.solve (PrefixCNF.restrict (layerFormula rows j) pre)) cap).2 ≤
        1 + 6 * n * min cap (Binary.goodCoefficient (rowSpace rows) (fun E : Causes n => E) j) := by
  have h := PrefixCNF.projected_enumeration solver (layerFormula rows j)
    (layer_compiler_contract rows j (by omega)).1 (by omega) cap
  rw [projected_good_coefficient] at h
  simpa only [projectionSize, show 2 * (n + (n + n)) = 6 * n by omega] using h

end GoodEncoding
end QecReliability.SharedCircuit
