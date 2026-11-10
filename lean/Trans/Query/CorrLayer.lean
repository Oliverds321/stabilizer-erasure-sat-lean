import Trans.Query.CorrSparse
import Trans.Query.CorrPop
import Final.ConcreteExternal

/-!
# Trans.Query.CorrLayer: latent layer, hash cell, requests and the query bits

Main results:
* `encBlock_quantumLayer`, `encBlock_quantumCell`: the blocks of the construction;
* `encReq_baseRequest`, `encReq_cellRequest`: the SAT requests;
* `encode_padRequest`: `QueryCodec.encode (padRequest D req) = Plain.query D (encReq req)`;
* `concreteQuery_base`, `concreteQuery_cell`: the controller's query bits
  (`Final.concreteQuery`) are `Plain.baseQuery`/`Plain.cellQuery` of the encoded inputs; the
  cell query takes the already computed hash program `K.program s ω` as an input.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Query
open QecReliability.SharedCircuit QecReliability.PrefixCNF QecReliability.OracleCost
open QecReliability.SharedCircuit.LatentEncoding
open Plain

/-! ## Latent program and physical wiring -/

theorem encProg_latent {n r : ℕ} (C : Program r n) (w : ℕ) :
    encProg (latentProgram C w) =
      (gatesS (r, 2 * n + w) (encProg C).1, wiresS (r, 2 * n + w) (encProg C).2) := by
  have hl : liftσ (fun i : Fin r => Fin.castAdd w (Fin.castAdd (n + n) i)) = shiftWire (r, 2 * n + w) := by
    rw [liftσ_shift (fun i : Fin r => Fin.castAdd w (Fin.castAdd (n + n) i)) (fun _ => rfl) (by omega)]
    congr 2; omega
  rw [latentProgram, encProg_rewire, hl, gatesS_eq, wiresS_eq]

theorem latent_gates {n r : ℕ} (C : Program r n) (w : ℕ) : (latentProgram C w).gates = C.gates := rfl

/-- The table of `physicalWire C w`. -/
def physTable {n r : ℕ} (C : Program r n) (w : ℕ) : List ℕ :=
  wiresS (r, 2 * n + w) (encProg C).2 ++ List.range' r (2 * n + w)

theorem liftσ_physical {n r : ℕ} (C : Program r n) (w : ℕ) :
    liftσ (physicalWire C w) = tableWire (physTable C w, 3 * n + w, r + 2 * n + w + C.gates) := by
  funext i
  unfold liftσ tableWire
  have hlen : (wiresS (r, 2 * n + w) (encProg C).2).length = n := by simp [wiresS_eq]
  by_cases hi : i < 3 * n + w
  · have hi' : i < BadEncoding.projectionSize n + w := by
      simp only [BadEncoding.projectionSize]; omega
    rw [dif_pos hi', if_pos hi]
    simp only [physicalWire]
    rw [addCases_val]
    by_cases h1 : i < n + (n + n)
    · rw [dif_pos h1, addCases_val]
      by_cases h2 : i < n
      · rw [dif_pos h2, physTable, List.getD_append _ _ _ _ (by omega)]
        have ho := congrArg (fun p => p.2) (encProg_latent C w)
        simp only [encProg] at ho
        have := congrArg (fun l => l.getD i 0) ho
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at this ⊢
        simpa [h2, encProg] using this
      · rw [dif_neg h2, physTable, List.getD_append_right _ _ _ _ (by omega), hlen]
        simp [List.getD_eq_getElem?_getD, show i - n < 2 * n + w by omega]
    · rw [dif_neg h1, physTable, List.getD_append_right _ _ _ _ (by omega), hlen]
      simp [List.getD_eq_getElem?_getD, show i - n < 2 * n + w by omega,
        LatentEncoding.keySize, BadEncoding.projectionSize] <;> omega
  · have hi' : ¬ i < BadEncoding.projectionSize n + w := by
      simp only [BadEncoding.projectionSize]; omega
    rw [dif_neg hi', if_neg hi]
    simp only [LatentEncoding.keySize, BadEncoding.projectionSize]
    omega

theorem encBlock_pullback {n r w : ℕ} (C : Program r n) (B : Block (BadEncoding.projectionSize n + w)) :
    encBlock (pullback C B) = Plain.pullback n r w (encProg C) (encBlock B) := by
  have hg : (gatesS (r, 2 * n + w) (encProg C).1).length = C.gates := by simp [gatesS_eq]
  rw [LatentEncoding.pullback, encBlock_after]
  simp only [Block.rewire]
  rw [encForm_rename _ (liftσ (physicalWire C w)) (liftWire_val _ _), liftσ_physical]
  have hc : encCirc (latentProgram C w).circuit = gatesS (r, 2 * n + w) (encProg C).1 :=
    congrArg Prod.fst (encProg_latent C w)
  simp only [Plain.pullback, hc, hg, latent_gates, encBlock, formT_eq, physTable,
    LatentEncoding.keySize]
  congr 3; omega

theorem encBlock_layer {n r w : ℕ} (C : Program r n) (B : Block (BadEncoding.projectionSize n + w))
    (j : ℕ) : encBlock (LatentEncoding.layerBlock C B j) =
      Plain.layerBlock n r w (encProg C) (encBlock B) j := by
  rw [LatentEncoding.layerBlock, encBlock_and, encBlock_pullback, encBlock_weight, Plain.layerBlock]
  simp only [LatentEncoding.keySize]
  rw [show r + (n + n) + w = r + 2 * n + w by omega]

/-! ## Quantum blocks, layers and cells -/

theorem witness_eq {n : ℕ} (rows : List (List (PauliCoord n))) (side : Bool) :
    quantumWitness rows side = Plain.witness n (encRows rows) side := by
  cases side
  · simp [quantumWitness, Plain.witness, BadEncoding.witnessSize]; omega
  · simp [quantumWitness, Plain.witness, GoodEncoding.witnessSize, trim_length]

theorem encBlock_quantumBlock {n : ℕ} (rows : List (List (PauliCoord n))) (side : Bool) :
    encBlock (quantumBlock rows side) = Plain.quantumBlock n (encRows rows) side := by
  cases side
  · exact encBlock_bad rows
  · exact encBlock_good rows

theorem encBlock_quantumLayer {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) :
    encBlock (quantumLayer rows C i) = Plain.quantumLayer n r (encRows rows) (encProg C) i.1 i.2.val := by
  rw [LatentEncoding.quantumLayer, encBlock_layer, encBlock_quantumBlock, witness_eq, Plain.quantumLayer]

theorem encBlock_quantumCell {n r t : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) (H : Program (keySize n r) t) (target : BitModels t) :
    encBlock (quantumCell rows C i H target) =
      Plain.quantumCell n r (encRows rows) (encProg C) i.1 i.2.val (encProg H) (List.ofFn target) := by
  rw [LatentEncoding.quantumCell, encBlock_hashCell, encBlock_quantumLayer, witness_eq, Plain.quantumCell]
  simp only [LatentEncoding.keySize]
  congr 1; omega

/-! ## Prefix units, requests, padding and serialization -/

theorem units_shift (k q : ℕ) (pre : List Bool) :
    Plain.units (k + 1) q pre = fmap (· + 1) (Plain.units k q pre) := by
  induction q generalizing k pre with
  | zero => cases pre <;> simp [Plain.units, fmap]
  | succ q ih =>
    cases pre with
    | nil => simp [Plain.units, fmap]
    | cons b pre =>
      simp only [Plain.units, ih (k + 1) pre]
      simp [fmap]

theorem encForm_units (q w : ℕ) (pre : List Bool) :
    encForm (PrefixCNF.units q w pre) = Plain.units 0 q pre := by
  induction q generalizing pre with
  | zero => cases pre <;> simp [PrefixCNF.units, Plain.units]
  | succ q ih =>
    cases pre with
    | nil => simp [PrefixCNF.units, Plain.units]
    | cons b pre =>
      simp only [PrefixCNF.units, Plain.units, units_shift, ← ih, encForm_cons, List.map_cons,
        List.map_nil, Fin.val_zero]
      simp [encForm_eq, PrefixCNF.shift, fmap]

theorem encForm_restrict {q w : ℕ} (F : Formula (q + w)) (pre : List Bool) :
    encForm (PrefixCNF.restrict F pre) = encForm F ++ Plain.units 0 q pre := by
  rw [PrefixCNF.restrict, encForm_append, encForm_units]

theorem encReq_baseRequest {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (i : Binary.CoefficientIndex r) (pre : List Bool) :
    encReq (QuantumService.baseRequest rows C i pre) =
      Plain.request (r + 2 * n) (Plain.witness n (encRows rows) i.1)
        (Plain.quantumLayer n r (encRows rows) (encProg C) i.1 i.2.val) pre := by
  rw [show r + 2 * n = r + (n + n) by omega]
  simp only [encReq, QuantumService.baseRequest, encForm_restrict, encForm_projectedFormula,
    Plain.request, ← encBlock_quantumLayer, ← witness_eq, LatentEncoding.keySize]
  simp only [encBlock]

theorem encReq_cellRequest {Ω : Type*} [Fintype Ω] {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (i : Binary.CoefficientIndex r)
    (s : Fin (keySize n r + 1)) (ω : Ω) (pre : List Bool) :
    encReq (QuantumService.cellRequest rows C H K i s ω pre) =
      Plain.request (r + 2 * n) (Plain.witness n (encRows rows) i.1)
        (Plain.quantumCell n r (encRows rows) (encProg C) i.1 i.2.val (encProg (K.program s ω))
          (List.replicate s.val false)) pre := by
  rw [show r + 2 * n = r + (n + n) by omega]
  have ht : List.ofFn (fun _ : Fin s.val => false) = List.replicate s.val false := List.ofFn_const _ _
  simp only [encReq, QuantumService.cellRequest, encForm_restrict, encForm_projectedFormula,
    Plain.request, ← ht, ← encBlock_quantumCell, ← witness_eq, LatentEncoding.keySize]
  simp only [encBlock]

theorem encode_padRequest (D : ℕ) (req : SATRequest) :
    QueryCodec.encode (padRequest D req) = Plain.query D (encReq req) := by
  rw [encode_eq_encodePlain]
  simp only [padRequest, paddedVariables, Plain.query, encReq, encForm_length]
  congr 1
  exact encForm_rename_id (Fin.castLE (Nat.le_max_left _ _)) (fun _ => rfl) _

/-! ## The controller's query bits -/

section Final
open QecReliability.OracleCost.WholeWrapperCandidate

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (Binary.CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))
    (m : ℕ) (ω : Fin (2 * m + 1) → Ω) (D : ℕ)

theorem concreteQuery_base (side : Bool) (j rep : ℕ)
    (valid : ValidKey (keySize n r) r m (.base side j rep)) :
    Final.concreteQuery rows C H K m ω D (.base side j rep) =
      Plain.baseQuery n r (encRows rows) (encProg C) side j [] D := by
  rw [Final.concreteQuery_valid rows C H K m ω D _ valid, resolveRequest, encode_padRequest,
    encReq_baseRequest]
  rfl

theorem concreteQuery_cell (side : Bool) (j rep scale : ℕ) (pre : List Bool)
    (valid : ValidKey (keySize n r) r m (.cell side j rep scale pre)) :
    Final.concreteQuery rows C H K m ω D (.cell side j rep scale pre) =
      Plain.cellQuery n r (encRows rows) (encProg C) side j
        (encProg (K.program ⟨scale, valid.2.2.1⟩ (ω ⟨rep, valid.2.1⟩)))
        (List.replicate scale false) pre D := by
  rw [Final.concreteQuery_valid rows C H K m ω D _ valid, resolveRequest, encode_padRequest,
    encReq_cellRequest]
  rfl

end Final

end QecReliability.Trans.Query
