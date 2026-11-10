import TensorQueryService
import TensorGridEnumeration
import TensorCountingInitial
import ResourceConcreteExternal

/-! Concrete SAT boundary for ordinal-indexed tensor coefficients. The only
semantic SAT input is the same resource-certified machine service used by the
finite-tape assembly. No tensor count or cache correctness is assumed. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.Boundary
open SharedCircuit TensorCoefficientCounting
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate

theorem slots_pred_succ (ds : List ℕ) : slots ds - 1 + 1 = slots ds := by
  have := slots_pos ds
  omega

def index (ds : List ℕ) (j : Fin (slots ds - 1 + 1)) : TensorBernstein.Grid ds :=
  ordinalIndex ds ⟨j.val, by simpa only [slots_pred_succ] using j.isLt⟩

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (LatentEncoding.keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))
  (m : ℕ) (ω : Fin (2*m+1) → Ω) (density : ℕ)

def resolve (key : RequestKey)
    (valid : ValidKey (LatentEncoding.keySize n ds.sum) (slots ds-1) m key) : SATRequest :=
  match key with
  | .base side j _ => TensorQuery.Service.baseRequest rows C (side,index ds ⟨j,valid.1⟩) []
  | .cell side j rep scale pre => TensorQuery.Service.cellRequest rows C H K
      (side,index ds ⟨j,valid.1⟩) ⟨scale,valid.2.2.1⟩ (ω ⟨rep,valid.2.1⟩) pre

def query (key : RequestKey) : List Bool := by
  classical
  exact if h : ValidKey (LatentEncoding.keySize n ds.sum) (slots ds-1) m key
    then QueryCodec.encode (padRequest density (resolve rows C H K m ω key h)) else []

theorem query_valid (key : RequestKey)
    (valid : ValidKey (LatentEncoding.keySize n ds.sum) (slots ds-1) m key) :
    query rows C H K m ω density key =
      QueryCodec.encode (padRequest density (resolve rows C H K m ω key valid)) := by
  simp only [query, dif_pos valid]

variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  {resource : SATRequest → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T resource)

def external : External where
  compileQuery key := ⟨query rows C H K m ω density key,0,0⟩
  sat := Final.Resource.satReply spec
  endpoint := Final.concreteEndpoint rows C

theorem answer (key : RequestKey)
    (valid : ValidKey (LatentEncoding.keySize n ds.sum) (slots ds-1) m key) :
    (external rows C H K m ω density spec).sat
      ((external rows C H K m ω density spec).compileQuery key).bits =
        spec.service.run (resolve rows C H K m ω key valid) := by
  change Final.Resource.satReply spec (query rows C H K m ω density key) = _
  rw [query_valid rows C H K m ω density key valid]
  exact Final.Resource.satReply_encode spec _

theorem coefficient_eq (B : ℕ) (s : Config) (hj : s.coefficient < slots ds-1+1) :
    operationalCoefficient (LatentEncoding.keySize n ds.sum) B m
      (external rows C H K m ω density spec) s =
      (TensorEncoding.queries ds rows C H K spec.service.solver
        (s.good,index ds ⟨s.coefficient,hj⟩)).cachedMedian B m ω := by
  apply CountingTrace.coefficient_eq_cached
  · intro rep
    have h := answer rows C H K m ω density spec (baseKey s rep.val) ⟨hj,rep.isLt⟩
    exact (congrArg SATReply.value h).trans
      (TensorQuery.Service.base_answer rows C H K spec.service _ []).symm
  · intro rep scale pre hpre
    have h := answer rows C H K m ω density spec
      (cellKey { trialAnchor s rep.val with scale := scale.val } pre)
      ⟨hj,rep.isLt,scale.isLt,hpre⟩
    exact (congrArg SATReply.value h).trans
      (TensorQuery.Service.cell_answer rows C H K spec.service _ scale (ω rep) pre).symm

theorem entry_eq (B : ℕ) (side : Bool) (j : Fin (slots ds-1+1)) :
    CountingTrace.entry (LatentEncoding.keySize n ds.sum) (slots ds-1) B m
      (external rows C H K m ω density spec) side j =
      (TensorEncoding.queries ds rows C H K spec.service.solver
        (side,index ds j)).cachedMedian B m ω :=
  coefficient_eq rows C H K m ω density spec B _ j.isLt

end QecReliability.TensorMachine.Boundary
