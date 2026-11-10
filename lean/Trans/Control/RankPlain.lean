import PhysicalBridge.BoundedRatios
import Trans.Query.Types
import Final.ConcreteExternal

/-!
# Trans.Control.RankPlain: the exact endpoints on plain data

Plain (list) versions of everything `concreteEndpoint` needs, with correspondence theorems:

* `rankL k rows`: column-by-column GF(2) elimination on Boolean lists (`clearL`, `xorL`);
  `rankL_eq : rankL n (rows.map toL) = BinaryElimination.rank n rows`.
* `par`, `denseRow n mask row`: a sparse Pauli row (encoded coordinates) as a dense masked
  `2n`-bit row; `denseRow_eq`: it is `toL` of the source's masked, flattened `decodeRow`.
* `gateVal`, `runGates`, `maskOf r side P`: evaluation of an encoded program on the constant
  input `side`; `maskOf_eq : maskOf r b (encProg C) = maskL (circuitMap C (∅ / univ))`.
* `ambP n rows mask` (`= ambiguityRank`, `ambP_eq`), `scoreP` and **`endpointP_eq`**:
  `endpointP n r (encRows rows) (encProg C) side = toR (concreteEndpoint rows C side).value`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Control.RankP
open QecReliability.BinaryElimination QecReliability.Binary QecReliability.SharedCircuit
open QecReliability.SharedCircuit.LatentEncoding QecReliability.Trans.Query

/-! ## Elimination -/

def xorL : List Bool → List Bool → List Bool
  | a :: as, b :: bs => Bool.xor a b :: xorL as bs
  | _, _ => []

def clearL (p x : List Bool) : List Bool := if x.headD false then xorL x.tail p.tail else x.tail

def rankL : ℕ → List (List Bool) → ℕ
  | 0, _ => 0
  | k + 1, rows =>
    match rows.find? (fun x => x.headD false) with
    | none => rankL k (rows.map List.tail)
    | some p => rankL k (rows.map (clearL p)) + 1

def toL {n : ℕ} (x : Row n) : List Bool := List.ofFn (fun i => decide (x i = 1))

theorem bit_one_iff (a : ZMod 2) : (a = 1) ↔ (a ≠ 0) := by revert a; decide
theorem bit_sub (a b : ZMod 2) : decide (a - b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1)) := by
  revert a b; decide
theorem bit_add (a b : ZMod 2) : decide (a + b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1)) := by
  revert a b; decide
theorem bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem xorL_ofFn {n : ℕ} (f g : Fin n → Bool) :
    xorL (List.ofFn f) (List.ofFn g) = List.ofFn (fun i => Bool.xor (f i) (g i)) := by
  induction n with
  | zero => simp [xorL]
  | succ n ih => simp [List.ofFn_succ, xorL, ih]

theorem toL_head {n : ℕ} (x : Row (n + 1)) : (toL x).headD false = decide (x 0 ≠ 0) := by
  simp [toL, List.ofFn_succ, bit_one_iff]

theorem toL_tail {n : ℕ} (x : Row (n + 1)) : (toL x).tail = toL (cacheRow (tailMap n x)) := by
  simp [toL, List.ofFn_succ, tailMap]

theorem toL_clear {n : ℕ} (p x : Row (n + 1)) :
    clearL (toL p) (toL x) = toL (cacheRow (clearTail p x)) := by
  unfold clearL
  rw [toL_head, toL_tail, toL_tail]
  rcases bit_cases (x 0) with h | h
  · simp [h, toL, clearTail, tailMap]
  · simp only [h, ne_eq, one_ne_zero, not_false_eq_true, decide_true, if_true]
    simp [toL, xorL_ofFn, clearTail, tailMap, h, bit_sub]

theorem rankL_eq : ∀ (n : ℕ) (rows : List (Row n)), rankL n (rows.map toL) = rank n rows
  | 0, _ => rfl
  | n + 1, rows => by
    have hc : ((fun x : List Bool => x.headD false) ∘ toL) =
        (fun x : Row (n + 1) => decide (x 0 ≠ 0)) := by funext x; exact toL_head x
    have hf : (rows.map toL).find? (fun x => x.headD false) =
        (rows.find? (fun x => decide (x 0 ≠ 0))).map toL := by rw [List.find?_map, hc]
    unfold rankL rank
    rw [hf]
    rcases h : rows.find? (fun x => decide (x 0 ≠ 0)) with _ | p
    · rw [h]; simp only [Option.map_none]
      rw [List.map_map, ← rankL_eq n, List.map_map]
      congr 1; apply List.map_congr_left; intro x _; simp [toL_tail]
    · rw [h]; simp only [Option.map_some]
      rw [List.map_map, ← rankL_eq n, List.map_map]
      congr 2; apply List.map_congr_left; intro x _; simp [toL_clear]

/-! ## Dense masked rows -/

def par (z : Bool) (i : ℕ) : List (Bool × ℕ) → Bool
  | [] => false
  | c :: cs => Bool.xor (decide (c = (z, i))) (par z i cs)

def denseRow (n : ℕ) (mask : List Bool) (row : List (Bool × ℕ)) : List Bool :=
  (List.range n).map (fun i => mask.getD i false && par false i row) ++
    (List.range n).map (fun i => mask.getD i false && par true i row)

def maskL {n : ℕ} (E : Finset (Fin n)) : List Bool := List.ofFn (fun i => decide (i ∈ E))

theorem maskL_getD {n : ℕ} (E : Finset (Fin n)) (i : Fin n) :
    (maskL E).getD i.val false = decide (i ∈ E) := by
  simp [maskL, List.getD_eq_getElem?_getD]

theorem maskL_getElem {n : ℕ} (E : Finset (Fin n)) (i : Fin n) :
    (maskL E)[i.val]?.getD false = decide (i ∈ E) := by
  simp [maskL]

theorem decode_fst {n : ℕ} (row : List (PauliCoord n)) (i : Fin n) :
    decide ((decodeRow row).1 i = 1) = par false i.val (row.map encCoord) := by
  induction row with
  | nil => simp [decodeRow, par]
  | cons c cs ih =>
    have e : decodeRow (c :: cs) = coordPauli c + decodeRow cs := by simp [decodeRow]
    rw [e, Prod.fst_add, Pi.add_apply, bit_add, ih]
    cases c with
    | inl j =>
      by_cases h : j = i
      · subst h; simp [coordPauli, xUnit, encCoord, par]
      · have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e)
        simp [coordPauli, xUnit, encCoord, par, h, h', Pi.single_apply, Ne.symm h]
    | inr j => simp [coordPauli, zUnit, encCoord, par]

theorem decode_snd {n : ℕ} (row : List (PauliCoord n)) (i : Fin n) :
    decide ((decodeRow row).2 i = 1) = par true i.val (row.map encCoord) := by
  induction row with
  | nil => simp [decodeRow, par]
  | cons c cs ih =>
    have e : decodeRow (c :: cs) = coordPauli c + decodeRow cs := by simp [decodeRow]
    rw [e, Prod.snd_add, Pi.add_apply, bit_add, ih]
    cases c with
    | inl j => simp [coordPauli, xUnit, encCoord, par]
    | inr j =>
      by_cases h : j = i
      · subst h; simp [coordPauli, zUnit, encCoord, par]
      · have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e)
        simp [coordPauli, zUnit, encCoord, par, h, h', Pi.single_apply, Ne.symm h]

theorem ofFn_val {α : Type} {n : ℕ} (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem <;> simp

theorem mask_bit (b : Prop) [Decidable b] (a : ZMod 2) :
    decide ((if b then a else 0) = 1) = (decide b && decide (a = 1)) := by
  by_cases h : b <;> simp [h]

theorem denseRow_eq {n : ℕ} (E : Finset (Fin n)) (row : List (PauliCoord n)) :
    toL (cacheRow (flatten n (mask n E (decodeRow row)))) = denseRow n (maskL E) (row.map encCoord) := by
  have hcl : ∀ (h : n ≤ n + n) (i : Fin n), Fin.castLE h i = Fin.castAdd n i := fun _ _ => rfl
  rw [cacheRow_eq, toL, List.ofFn_add]
  simp only [hcl, flatten, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Fin.addCases_left,
    Fin.addCases_right, mask, mask_bit, decode_fst, decode_snd]
  unfold denseRow
  rw [← ofFn_val, ← ofFn_val]
  simp [maskL_getD, maskL_getElem]

/-! ## Constant-input evaluation of an encoded program -/

def gateVal (vals : List Bool) (g : Bool × Bool × ℕ × ℕ) : Bool :=
  if g.1 then (if g.2.1 then decide (g.2.2.1 ≠ 0) else !(vals.getD g.2.2.1 false))
  else if g.2.1 then Bool.xor (vals.getD g.2.2.1 false) (vals.getD g.2.2.2 false)
  else (vals.getD g.2.2.1 false && vals.getD g.2.2.2 false)

def runGates : List Bool → List (Bool × Bool × ℕ × ℕ) → List Bool
  | vals, [] => vals
  | vals, g :: gs => runGates (vals ++ [gateVal vals g]) gs

theorem runGates_append (vals : List Bool) (gs hs : List (Bool × Bool × ℕ × ℕ)) :
    runGates vals (gs ++ hs) = runGates (runGates vals gs) hs := by
  induction gs generalizing vals with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem getD_ofFn {v : ℕ} (a : Fin v → Bool) (x : Fin v) : (List.ofFn a).getD x.val false = a x := by
  simp [List.getD_eq_getElem?_getD]

theorem gateVal_enc {v : ℕ} (gate : Gate v) (a : BitModels v) :
    gateVal (List.ofFn a) (encGate gate) = gate.eval a := by
  cases gate with
  | andGate x y => simp [gateVal, encGate, Gate.eval, getD_ofFn]
  | xorGate x y => simp [gateVal, encGate, Gate.eval, getD_ofFn]
  | notGate x => simp [gateVal, encGate, Gate.eval, getD_ofFn]
  | constGate b => cases b <;> simp [gateVal, encGate, Gate.eval, Plain.constGate]

theorem ofFn_snoc {α : Type} {n : ℕ} (f : Fin n → α) (x : α) :
    List.ofFn (Fin.snoc f x : Fin (n + 1) → α) = List.ofFn f ++ [x] := by
  rw [List.ofFn_succ']; simp

theorem runGates_enc {n g : ℕ} (C : Circuit n g) (a : BitModels n) :
    runGates (List.ofFn a) (encCirc C) = List.ofFn (C.run a) := by
  induction C with
  | nil => rfl
  | snoc C gate ih =>
    rw [encCirc_snoc, runGates_append, ih]
    simp only [runGates, Circuit.run, gateVal_enc, ofFn_snoc]

def maskOf (r : ℕ) (b : Bool) (P : List (Bool × Bool × ℕ × ℕ) × List ℕ) : List Bool :=
  P.2.map (fun o => (runGates (List.replicate r b) P.1).getD o false)

theorem maskOf_eq {n r : ℕ} (C : Program r n) (b : Bool) :
    maskOf r b (encProg C) = maskL (circuitMap C (if b then Finset.univ else ∅)) := by
  have hr : List.replicate r b = List.ofFn (fun _ : Fin r => b) := by simp
  simp only [maskOf, encProg, hr, runGates_enc, List.map_ofFn, maskL]
  congr 1; funext i
  simp only [Function.comp_apply, getD_ofFn]
  cases b <;> simp [circuitMap, causeBits, Program.eval]

/-! ## Ambiguity rank and score -/

def rrP (n : ℕ) (rows : List (List (Bool × ℕ))) (mask : List Bool) : ℕ :=
  rankL (n + n) (rows.map (denseRow n mask))

def cardP (mask : List Bool) : ℕ := (mask.map (fun b => if b then 1 else 0)).sum

def ambP (n : ℕ) (rows : List (List (Bool × ℕ))) (mask : List Bool) : ℕ :=
  (2 * cardP mask - rrP n rows mask) - (rrP n rows (List.replicate n true) - rrP n rows (mask.map not))

theorem rrP_eq {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    rrP n (encRows rows) (maskL E) = restrictedRank rows E := by
  rw [restrictedRank, ← rankL_eq, rrP, restrictedRows, encRows, List.map_map, List.map_map]
  congr 1; apply List.map_congr_left; intro row _
  simp only [Function.comp_apply]
  rw [← denseRow_eq]

theorem mask_univ (n : ℕ) (y : Pauli n) : mask n Finset.univ y = y := by
  simp [mask]

theorem maskL_univ (n : ℕ) : maskL (Finset.univ : Finset (Fin n)) = List.replicate n true := by
  simp [maskL]

theorem maskL_compl {n : ℕ} (E : Finset (Fin n)) : maskL Eᶜ = (maskL E).map not := by
  simp [maskL, List.map_ofFn, Function.comp_def]

theorem cardP_eq {n : ℕ} (E : Finset (Fin n)) : cardP (maskL E) = E.card := by
  rw [cardP, maskL, List.map_ofFn, List.sum_ofFn]
  simp [Function.comp_def, Finset.sum_boole]

theorem sparse_eq {n : ℕ} (rows : List (List (PauliCoord n))) :
    rrP n (encRows rows) (List.replicate n true) = sparseRank rows := by
  rw [← maskL_univ, rrP_eq, restrictedRank, sparseRank, restrictedRows, decodedRows]
  simp [mask_univ]

theorem ambP_eq {n : ℕ} (rows : List (List (PauliCoord n))) (E : Finset (Fin n)) :
    ambP n (encRows rows) (maskL E) = ambiguityRank rows E := by
  rw [ambP, ambiguityRank, cardP_eq, rrP_eq, sparse_eq, ← maskL_compl, rrP_eq]

/-- The endpoint ratio `(1, 2^ambiguity)` on plain data. -/
def endpointP (n r : ℕ) (rows : List (List (Bool × ℕ))) (P : List (Bool × Bool × ℕ × ℕ) × List ℕ)
    (side : Bool) : ℕ × ℕ := (1, 2 ^ ambP n rows (maskOf r side P))

/-- **Exact endpoints**: the plain endpoint is the controller's `concreteEndpoint`. -/
theorem endpointP_eq {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n) (side : Bool) :
    endpointP n r (encRows rows) (encProg C) side =
      ((Final.concreteEndpoint rows C side).value.num,
        (Final.concreteEndpoint rows C side).value.den) := by
  rw [endpointP, maskOf_eq, ambP_eq]
  cases side <;> rfl

end QecReliability.Trans.Control.RankP
