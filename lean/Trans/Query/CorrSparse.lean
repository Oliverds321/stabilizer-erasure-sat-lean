import Trans.Query.CorrBasic

/-!
# Trans.Query.CorrSparse: Bad and Good blocks on plain data

`encBlock (BadEncoding.block rows) = Plain.badBlock n (encRows rows)` and
`encBlock (GoodEncoding.block rows) = Plain.goodBlock n (encRows rows)`, through the sparse
normalizer, parity circuits, pairing/support clauses, and the sparse reconstruction.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Query
open QecReliability.SharedCircuit QecReliability.PrefixCNF QecReliability.OracleCost
open Plain

/-! ## Lists of `Fin` values -/

theorem ofFn_val_eq_range {n : ℕ} (g : ℕ → ℕ × ℕ) :
    List.ofFn (fun i : Fin n => g i.val) = (List.range n).map g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.range_succ, List.map_append, ← ih]
    simp [List.concat_eq_append]

/-! ## Parity circuits and rows -/

theorem encCirc_parity {v : ℕ} (xs : List (Fin v)) :
    encCirc (parityCircuit xs) = parityGates v (xs.map Fin.val) := by
  induction xs with
  | nil => simp [parityCircuit, parityGates, encGate]
  | cons x xs ih => simp [parityCircuit, parityGates, encGate, ih]

theorem encBlock_rowBlock {v : ℕ} (row : List (Fin v)) :
    encBlock (rowBlock row) = Plain.rowBlock v (row.map Fin.val) := by
  simp [SharedCircuit.rowBlock, Plain.rowBlock, encBlock_constrained, encCirc_parity]

theorem rowWires_val {n v : ℕ} (x z : Fin n → Fin v) (ox oz : ℕ)
    (hx : ∀ i, (x i).val = ox + i.val) (hz : ∀ i, (z i).val = oz + i.val)
    (row : List (PauliCoord n)) :
    (SharedCircuit.rowWires x z row).map Fin.val = Plain.rowWires ox oz (row.map encCoord) := by
  induction row with
  | nil => rfl
  | cons c row ih =>
    cases c <;> simp_all [SharedCircuit.rowWires, Plain.rowWires, encCoord]

theorem encBlock_normalizer {n v : ℕ} (rows : List (List (PauliCoord n))) (x z : Fin n → Fin v)
    (ox oz : ℕ) (hx : ∀ i, (x i).val = ox + i.val) (hz : ∀ i, (z i).val = oz + i.val) :
    encBlock (normalizerBlock rows x z) = Plain.normalizer v ox oz (encRows rows) := by
  simp only [normalizerBlock, encBlock_merge, Plain.normalizer, List.map_map]
  congr 1
  have h1 : (fun row => Plain.rowWires ox oz row) ∘ (fun row => row.map encCoord) =
      (fun row : List (Fin v) => row.map Fin.val) ∘ SharedCircuit.rowWires x z := by
    funext row; simp [rowWires_val x z ox oz hx hz]
  simp only [encRows, List.map_map, h1, nonemptyRows, List.filter_map]
  congr 1
  · funext row; simp [Function.comp_def, encBlock_rowBlock]
  · congr 1; funext row; simp [nonempty, Function.comp_def]

/-! ## Pairing and support -/

theorem encCirc_productParity {v : ℕ} (xs : List (Fin v × Fin v)) :
    encCirc (productParityCircuit xs) =
      productParityGates v (xs.map (fun p => (p.1.val, p.2.val))) := by
  induction xs with
  | nil => simp [productParityCircuit, productParityGates, encGate]
  | cons p xs ih =>
    obtain ⟨x, y⟩ := p
    simp [productParityCircuit, productParityGates, encGate, ih]
    omega

theorem pairs_val {n v : ℕ} (a b : Fin n → Fin v) (oa ob : ℕ) (ha : ∀ i, (a i).val = oa + i.val)
    (hb : ∀ i, (b i).val = ob + i.val) :
    (List.ofFn (fun i => (a i, b i))).map (fun p => (p.1.val, p.2.val)) = offsetPairs n oa ob := by
  rw [List.map_ofFn]
  simp only [Function.comp_def, ha, hb]
  exact ofFn_val_eq_range (fun i => (oa + i, ob + i))

theorem encBlock_pairing {n v : ℕ} (x z x' z' : Fin n → Fin v) (ox oz ox' oz' : ℕ)
    (hx : ∀ i, (x i).val = ox + i.val) (hz : ∀ i, (z i).val = oz + i.val)
    (hx' : ∀ i, (x' i).val = ox' + i.val) (hz' : ∀ i, (z' i).val = oz' + i.val) :
    encBlock (pairingBlock x z x' z') = Plain.pairingBlock v (Plain.pairingPairs n ox oz ox' oz') := by
  have hp : (SharedCircuit.pairingPairs x z x' z').map (fun p => (p.1.val, p.2.val)) =
      Plain.pairingPairs n ox oz ox' oz' := by
    simp only [SharedCircuit.pairingPairs, List.map_append, Plain.pairingPairs]
    rw [pairs_val x z' ox oz' hx hz', pairs_val z x' oz ox' hz hx']
  have hl : (Plain.pairingPairs n ox oz ox' oz').length = (SharedCircuit.pairingPairs x z x' z').length := by
    rw [← hp, List.length_map]
  simp only [SharedCircuit.pairingBlock, encBlock_constrained, encCirc_productParity, hp,
    Plain.pairingBlock, hl, Fin.val_last]

theorem encForm_supportClauses {n v : ℕ} (x z e : Fin n → Fin v) (ox oz oe : ℕ)
    (hx : ∀ i, (x i).val = ox + i.val) (hz : ∀ i, (z i).val = oz + i.val)
    (he : ∀ i, (e i).val = oe + i.val) :
    encForm (SharedCircuit.supportClauses (SharedCircuit.supportPairs x z e)) =
      Plain.supportClauses (Plain.supportPairs n ox oz oe) := by
  have hp : (SharedCircuit.supportPairs x z e).map (fun p => (p.1.val, p.2.val)) =
      Plain.supportPairs n ox oz oe := by
    simp only [SharedCircuit.supportPairs, List.map_append, Plain.supportPairs]
    rw [pairs_val x e ox oe hx he, pairs_val z e oz oe hz he]
  rw [← hp]
  simp [SharedCircuit.supportClauses, Plain.supportClauses, encForm_eq]

/-! ## The Bad block -/

theorem encBlock_bad {n : ℕ} (rows : List (List (PauliCoord n))) :
    encBlock (BadEncoding.block rows) = Plain.badBlock n (encRows rows) := by
  have e5 : BadEncoding.primarySize n = 5 * n := by
    simp only [BadEncoding.primarySize, BadEncoding.projectionSize, BadEncoding.witnessSize]; omega
  simp only [BadEncoding.block, SharedCircuit.badBlock, encBlock_and]
  rw [encBlock_normalizer rows _ _ n (2 * n) (fun i => by simp [BadEncoding.zxWire, BadEncoding.projectionSize, BadEncoding.witnessSize])
      (fun i => by simp [BadEncoding.zzWire, BadEncoding.projectionSize, BadEncoding.witnessSize]; omega),
    encBlock_normalizer rows _ _ (3 * n) (4 * n) (fun i => by simp [BadEncoding.xxWire, BadEncoding.projectionSize, BadEncoding.witnessSize]; omega)
      (fun i => by simp [BadEncoding.xzWire, BadEncoding.projectionSize, BadEncoding.witnessSize]; omega),
    encBlock_pairing _ _ _ _ (3 * n) (4 * n) n (2 * n) (fun i => by simp [BadEncoding.xxWire, BadEncoding.projectionSize, BadEncoding.witnessSize]; omega)
      (fun i => by simp [BadEncoding.xzWire, BadEncoding.projectionSize, BadEncoding.witnessSize]; omega) (fun i => by simp [BadEncoding.zxWire, BadEncoding.projectionSize, BadEncoding.witnessSize])
      (fun i => by simp [BadEncoding.zzWire, BadEncoding.projectionSize, BadEncoding.witnessSize]; omega),
    encBlock_direct,
    encForm_supportClauses _ _ _ (3 * n) (4 * n) 0 (fun i => by simp [BadEncoding.xxWire, BadEncoding.projectionSize, BadEncoding.witnessSize]; omega)
      (fun i => by simp [BadEncoding.xzWire, BadEncoding.projectionSize, BadEncoding.witnessSize]; omega) (fun i => by simp [BadEncoding.eWire, BadEncoding.projectionSize, BadEncoding.witnessSize])]
  simp only [Plain.badBlock, e5]

/-! ## Sparse reconstruction -/

/-- A reconstruction as `(gates, x-outputs, z-outputs)`. -/
def encRec {n v : ℕ} (R : Reconstruction n v) : RecP :=
  (encCirc R.circuit, List.ofFn (fun i => (R.output (.inl i)).val),
    List.ofFn (fun i => (R.output (.inr i)).val))

theorem ofFn_update {α : Type} {n : ℕ} (f : Fin n → α) (j : Fin n) (a : α) :
    List.ofFn (fun i => if i = j then a else f i) = (List.ofFn f).set j.val a := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_ofFn, List.getElem_set]
    by_cases hk : j.val = k
    · simp [hk, Fin.ext_iff]
    · rw [if_neg (fun h => hk (by rw [← h])), if_neg hk]

theorem encRec_zero (n v : ℕ) : encRec (Reconstruction.zero n v) = recZero n v := by
  simp [encRec, Reconstruction.zero, recZero, encGate, List.ofFn_const]

theorem getD_ofFn {n : ℕ} (f : Fin n → ℕ) (i : Fin n) : (List.ofFn f).getD i.val 0 = f i := by
  simp

theorem encRec_addIncidence {n v : ℕ} (R : Reconstruction n v) (c : PauliCoord n) (coeff : Fin v) :
    encRec (R.addIncidence c coeff) = recAddInc v (encRec R) (encCoord c) coeff.val := by
  cases c with
  | inl j =>
    simp only [encRec, Reconstruction.addIncidence, recAddInc, encCoord, encCirc_snoc,
      encCirc_length, Bool.false_eq_true, if_false, Prod.mk.injEq]
    refine ⟨by simp [encGate, getD_ofFn], ?_, ?_⟩
    · rw [← ofFn_update]; congr 1; funext i
      by_cases h : i = j <;> simp [h]
    · congr 1
  | inr j =>
    simp only [encRec, Reconstruction.addIncidence, recAddInc, encCoord, encCirc_snoc,
      encCirc_length, if_true, Prod.mk.injEq]
    refine ⟨by simp [encGate, getD_ofFn], ?_, ?_⟩
    · congr 1
    · rw [← ofFn_update]; congr 1; funext i
      by_cases h : i = j <;> simp [h]

theorem encRec_addRow {n v : ℕ} (R : Reconstruction n v) (coeff : Fin v) (row : List (PauliCoord n)) :
    encRec (R.addRow coeff row) = recAddRow v (encRec R) coeff.val (row.map encCoord) := by
  induction row with
  | nil => rfl
  | cons c cs ih =>
    simp only [Reconstruction.addRow, List.map_cons, recAddRow, encRec_addIncidence, ih]

theorem encRec_synthesize {n v : ℕ} (rows : List (List (PauliCoord n))) (coeff : Fin rows.length → Fin v)
    (base : ℕ) (hc : ∀ i, (coeff i).val = base + i.val) :
    encRec (Reconstruction.synthesize rows coeff) = Plain.synthesize n v base (encRows rows) := by
  induction rows generalizing base with
  | nil => simp [Reconstruction.synthesize, encRec_zero, encRows, Plain.synthesize]
  | cons row rows ih =>
    simp only [Reconstruction.synthesize, encRows, List.map_cons, Plain.synthesize]
    rw [encRec_addRow, ih (Fin.tail coeff) (base + 1) (fun i => by simp [Fin.tail, hc]; omega)]
    simp [hc, encRows]

/-! ## Cleaning block -/

theorem condEqs_ofFn (oz : ℕ) {n : ℕ} (f : Fin n → ℕ) (k : ℕ) :
    condEqs oz k (List.ofFn f) = (List.ofFn (fun i : Fin n => condEq (k + i) (f i) (oz + (k + i)))).flatten := by
  induction n generalizing k with
  | zero => simp [condEqs]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, condEqs, ih (fun i => f i.succ) (k + 1)]
    simp only [List.flatten_cons, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 3; funext i; congr 1 <;> omega

theorem encForm_condEq {v : ℕ} (e x y : Fin v) :
    encForm (conditionalEquality e x y) = Plain.condEq e.val x.val y.val := by
  simp [conditionalEquality, Plain.condEq]

theorem encForm_flatten {v : ℕ} (Fs : List (Formula v)) :
    encForm Fs.flatten = (Fs.map encForm).flatten := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simp [ih]

theorem encBlock_cleaning {n v : ℕ} (R : Reconstruction n v) (e zx zz : Fin n → Fin v)
    (he : ∀ i, (e i).val = i.val) (hzx : ∀ i, (zx i).val = n + i.val)
    (hzz : ∀ i, (zz i).val = 2 * n + i.val) :
    encBlock (R.cleaningBlock e zx zz) = Plain.cleaning n v (encRec R) := by
  simp only [Reconstruction.cleaningBlock, encBlock, Plain.cleaning, encRec, encCirc_length,
    encForm_append, encForm_compile, Prod.mk.injEq, true_and]
  congr 1
  simp only [coordinateAgreement, allCoords, List.map_append, List.flatten_append, encForm_append,
    encForm_flatten, List.map_map, condEqs_ofFn, List.map_ofFn]
  congr 1 <;> (congr 1; congr 1; funext i; simp [Function.comp_def, encForm_condEq, he, hzx, hzz])

/-! ## The Good block -/

theorem encRows_trim {n : ℕ} (rows : List (List (PauliCoord n))) :
    encRows (SharedCircuit.trimRows rows) = Plain.trimRows (encRows rows) := by
  simp only [encRows, SharedCircuit.trimRows, Plain.trimRows, List.filter_map]
  congr 1
  apply List.filter_congr
  intro row _
  simp

theorem trim_length {n : ℕ} (rows : List (List (PauliCoord n))) :
    (SharedCircuit.trimRows rows).length = (Plain.trimRows (encRows rows)).length := by
  rw [← encRows_trim]; simp [encRows]

theorem encBlock_good {n : ℕ} (rows : List (List (PauliCoord n))) :
    encBlock (GoodEncoding.block rows) = Plain.goodBlock n (encRows rows) := by
  have ev : GoodEncoding.primarySize rows = 3 * n + (Plain.trimRows (encRows rows)).length := by
    simp only [GoodEncoding.primarySize, BadEncoding.projectionSize, GoodEncoding.witnessSize,
      trim_length]; omega
  simp only [GoodEncoding.block, SharedCircuit.goodBlock, encBlock_and]
  rw [encBlock_normalizer rows _ _ n (2 * n) (fun i => by simp [GoodEncoding.zxWire, BadEncoding.projectionSize])
      (fun i => by simp [GoodEncoding.zzWire, BadEncoding.projectionSize]; omega),
    encBlock_cleaning _ _ _ _ (fun i => by simp [GoodEncoding.eWire, BadEncoding.projectionSize])
      (fun i => by simp [GoodEncoding.zxWire, BadEncoding.projectionSize]) (fun i => by simp [GoodEncoding.zzWire, BadEncoding.projectionSize]; omega),
    encRec_synthesize _ _ (3 * n) (fun i => by simp [GoodEncoding.coeffWire, BadEncoding.projectionSize]; omega),
    encRows_trim]
  simp only [Plain.goodBlock, ev]

end QecReliability.Trans.Query
