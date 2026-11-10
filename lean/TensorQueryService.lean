import TensorQueryPlain
import OracleCost.QuantumQueryBound

namespace QecReliability.TensorQuery.Service
open SharedCircuit SharedCircuit.TensorEncoding TensorCoefficientCounting
open OracleCost Trans.Query

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (LatentEncoding.keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))

def baseRequest (i : Index ds) (pre : List Bool) : SATRequest :=
  ⟨_,PrefixCNF.restrict (TensorEncoding.quantumLayer ds rows C i).projectedFormula pre,
    PrefixCNF.restrict_width (quantumLayer_contract ds rows C i).1 (by omega) pre⟩

def cellRequest (i : Index ds) (s : Fin (LatentEncoding.keySize n ds.sum+1))
    (ω : Ω) (pre : List Bool) : SATRequest :=
  ⟨_,PrefixCNF.restrict
    (TensorEncoding.quantumCell ds rows C i (K.program s ω) (fun _ => false)).projectedFormula pre,
    PrefixCNF.restrict_width (quantumCell_width ds rows C i (K.program s ω) (fun _ => false))
      (by omega) pre⟩

theorem base_answer (service : SATService) (i : Index ds) (pre : List Bool) :
    (TensorEncoding.queries ds rows C H K service.solver i).base.answer pre =
      (service.run (baseRequest rows C i pre)).value :=
  service.solve_width _ _

theorem cell_answer (service : SATService) (i : Index ds)
    (s : Fin (LatentEncoding.keySize n ds.sum+1)) (ω : Ω) (pre : List Bool) :
    ((TensorEncoding.queries ds rows C H K service.solver i).cell s ω).answer pre =
      (service.run (cellRequest rows C H K i s ω pre)).value :=
  service.solve_width _ _

theorem encReq_base (i : Index ds) (pre : List Bool) :
    encReq (baseRequest rows C i pre) =
      Plain.request (ds.sum+2*n) (Plain.witness n (encRows rows) i.1)
        (TensorQuery.quantumLayer n ds (encRows rows) (encProg C) i.1
          (TensorLatent.indexList ds i.2)) pre := by
  rw [show ds.sum+2*n = ds.sum+(n+n) by omega]
  simp only [encReq,baseRequest,encForm_restrict,encForm_projectedFormula,
    Plain.request,← TensorQuery.encBlock_quantumLayer,← witness_eq,LatentEncoding.keySize]
  simp only [encBlock]

theorem encReq_cell (i : Index ds) (s : Fin (LatentEncoding.keySize n ds.sum+1))
    (ω : Ω) (pre : List Bool) :
    encReq (cellRequest rows C H K i s ω pre) =
      Plain.request (ds.sum+2*n) (Plain.witness n (encRows rows) i.1)
        (TensorQuery.quantumCell n ds (encRows rows) (encProg C) i.1
          (TensorLatent.indexList ds i.2) (encProg (K.program s ω))
          (List.replicate s.val false)) pre := by
  rw [show ds.sum+2*n = ds.sum+(n+n) by omega]
  have ht : List.ofFn (fun _ : Fin s.val => false) = List.replicate s.val false := List.ofFn_const _ _
  simp only [encReq,cellRequest,encForm_restrict,encForm_projectedFormula,
    Plain.request,← ht,← TensorQuery.encBlock_quantumCell,← witness_eq,LatentEncoding.keySize]
  simp only [encBlock]

theorem query_base (i : Index ds) (pre : List Bool) (D : ℕ)
    (unusedH : Plain.ProgP) (unusedTarget : List Bool) :
    TensorQuery.query false n ds (encRows rows) (encProg C) i.1
      (TensorLatent.indexList ds i.2) unusedH unusedTarget pre D =
        QueryCodec.encode (padRequest D (baseRequest rows C i pre)) := by
  rw [encode_padRequest,encReq_base]
  rfl

theorem query_cell (i : Index ds) (s : Fin (LatentEncoding.keySize n ds.sum+1))
    (ω : Ω) (pre : List Bool) (D : ℕ) :
    TensorQuery.query true n ds (encRows rows) (encProg C) i.1
      (TensorLatent.indexList ds i.2) (encProg (K.program s ω))
      (List.replicate s.val false) pre D =
        QueryCodec.encode (padRequest D (cellRequest rows C H K i s ω pre)) := by
  rw [encode_padRequest,encReq_cell]
  rfl

def variableBound (hashGates : ℕ) : ℕ :=
  21*ds.sum+8*n+4*rowIncidences rows+C.gates+hashGates+11*ds.length+1

def clauseBound (hashGates : ℕ) : ℕ :=
  18*rowIncidences rows+22*n+83*ds.sum+47*ds.length+4*C.gates+4*hashGates+6

theorem base_dimensions (g : ℕ) (i : Index ds) (pre : List Bool) :
    (baseRequest rows C i pre).varCount ≤ variableBound rows C g ∧
    (baseRequest rows C i pre).formula.length ≤ clauseBound rows C g := by
  have hc := quantumLayer_contract ds rows C i
  have hp := PrefixCNF.restrict_length_bound
    (TensorEncoding.quantumLayer ds rows C i).projectedFormula pre
  change _ ≤ variableBound rows C g ∧ _ ≤ clauseBound rows C g
  dsimp only [variableBound,clauseBound]
  simp only [LatentEncoding.keySize] at hc hp
  constructor <;> dsimp only [baseRequest,LatentEncoding.keySize] <;> omega

theorem cell_dimensions (g : ℕ) (i : Index ds)
    (s : Fin (LatentEncoding.keySize n ds.sum+1)) (ω : Ω) (pre : List Bool)
    (hg : (K.program s ω).gates ≤ g) :
    (cellRequest rows C H K i s ω pre).varCount ≤ variableBound rows C g ∧
    (cellRequest rows C H K i s ω pre).formula.length ≤ clauseBound rows C g := by
  have hc := quantumCell_contract ds rows C i (K.program s ω) (fun _ => false)
  have hp := PrefixCNF.restrict_length_bound
    (TensorEncoding.quantumCell ds rows C i (K.program s ω) (fun _ => false)).projectedFormula pre
  have hs := s.isLt
  simp only [LatentEncoding.keySize] at hc hp hs
  change _ ≤ variableBound rows C g ∧ _ ≤ clauseBound rows C g
  dsimp only [variableBound,clauseBound]
  constructor <;> dsimp only [cellRequest,LatentEncoding.keySize] <;> omega

/-- Concrete serialized request sizes, linear dimensions followed by the
existing binary CNF codec's explicit bound. -/
theorem encoded_requests (g : ℕ) (hg : ∀ s ω, (K.program s ω).gates ≤ g) :
    (∀ i pre, (QueryCodec.encode (baseRequest rows C i pre)).length ≤
      QueryCodec.sizeBound (variableBound rows C g) (clauseBound rows C g)) ∧
    (∀ i s ω pre, (QueryCodec.encode (cellRequest rows C H K i s ω pre)).length ≤
      QueryCodec.sizeBound (variableBound rows C g) (clauseBound rows C g)) := by
  constructor
  · intro i pre
    exact QueryCodec.encode_length_le _ _ _ (base_dimensions rows C g i pre).1
      (base_dimensions rows C g i pre).2
  · intro i s ω pre
    exact QueryCodec.encode_length_le _ _ _ (cell_dimensions rows C H K g i s ω pre (hg s ω)).1
      (cell_dimensions rows C H K g i s ω pre (hg s ω)).2

end QecReliability.TensorQuery.Service
