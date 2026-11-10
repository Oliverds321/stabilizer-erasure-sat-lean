import TensorFactoryResourceBounds
import TensorMachinePathTrace

/-! The actual retained tensor query is sent to the embedded resource-certified
SAT engine. Oracle cleanup is charged by its visited cells. -/

set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.Boundary
open SharedCircuit SharedCircuit.LatentEncoding TensorCoefficientCounting
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))
  (m : ℕ) (ω : Fin (2*m+1) → Ω) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent)

theorem invoke_correct (g : ℕ) (hg : ∀ scale seed, (K.program scale seed).gates ≤ g)
    {B : ℕ} {s : Config}
    (hs : Reachable (keySize n ds.sum) (slots ds-1) B m false
      (external rows C H K m ω density spec) s) (hpc : s.pc = .invoke) :
    let cap := extentCap rows C density g
    let O := RegMachine.resourceSatOracle E density requestExtent cap
    O.qok s.query ∧
      O.oracle s.query = ((external rows C H K m ω density spec).sat s.query).value ∧
      O.ocost s.query ≤ ((external rows C H K m ω density spec).sat s.query).time + Ps.eval cap := by
  let cap := extentCap rows C density g
  let O := RegMachine.resourceSatOracle E density requestExtent cap
  have hk := (reachable_request_invariant hs).request
  have hq := Final.reachable_invoke_query hs hpc
  change s.query = query rows C H K m ω density s.request at hq
  have hok : O.qok s.query := by
    rw [hq]
    exact query_resource_qok rows C H K E m ω density g hg s.request hk
  have hpadded : Final.IsPaddedQuery density s.query := by
    rw [hq,query_valid rows C H K m ω density s.request hk]
    exact ⟨_,rfl⟩
  obtain ⟨run,hanswer,_,hcells⟩ := RegMachine.resourceSatOracle_realizes spec cap s.query hok
  have hrun := RegMachine.resourceSatOracle_run E density requestExtent cap run
  have hobs := Final.Resource.satReply_of_completed spec hpadded run
  refine ⟨hok,?_,?_⟩
  · change O.oracle s.query = (Final.Resource.satReply spec s.query).value
    exact hanswer.symm.trans hobs.1.symm
  · change O.ocost s.query ≤ (Final.Resource.satReply spec s.query).time + Ps.eval cap
    rw [hrun.2,hobs.2.1]
    exact Nat.add_le_add_left hcells _

end QecReliability.TensorMachine.Boundary
end
