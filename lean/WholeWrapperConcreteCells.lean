import WholeWrapperCellBatch
import Mathlib.Data.List.FinRange

/-! The actual ext-backed all-scales records and service
time are literally the frozen cached evaluator's cell table. Boundary equality
is needed only on valid prefixes, and execution locality supplies that restriction.
-/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open PrefixEnumeration

/-- Execution reads only pre++tail with |tail|≤depth. This prevents illicit
function extensionality over out-of-range prefixes when resolving requests. -/
theorem execute_eq_on_extensions (a b : List Bool → SATReply) (depth : ℕ)
    (pre : List Bool) (cap : ℕ)
    (h : ∀ tail, tail.length≤depth → a (pre++tail)=b (pre++tail)) :
    PrefixMachine.execute depth a pre cap=PrefixMachine.execute depth b pre cap := by
  induction depth generalizing pre cap with
  | zero =>
      have hh : a pre=b pre := by simpa using h [] (by simp)
      simp [PrefixMachine.execute,hh]
  | succ depth ih =>
      have hh : a pre=b pre := by simpa using h [] (by simp)
      by_cases hc : cap=0
      · simp [PrefixMachine.execute,hc]
      · cases hv : (b pre).value with
        | false => simp [PrefixMachine.execute,hc,hh,hv]
        | true =>
            have hl := ih (pre++[false]) cap (by
              intro tail ht
              simpa [List.append_assoc] using h (false::tail) (by simp; omega))
            have hr := ih (pre++[true])
              (cap-(PrefixMachine.execute depth b (pre++[false]) cap).control.count) (by
                intro tail ht
                simpa [List.append_assoc] using h (true::tail) (by simp; omega))
            simp only [PrefixMachine.execute,if_neg hc,hh,hv,↓reduceIte]
            rw [hl,hr]

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (D : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)
    (anchor : Config) (hj : anchor.coefficient<r+1) (hrep : anchor.repetition<2*m+1)

include hboundary in
/-- Each operational cell's complete measured control equals the SAME source
cell, including count, calls, oracleTime, visits and stack-depth accounting. -/
theorem concrete_cellResult (scale : Fin (keySize n r+1)) :
    cellResult (keySize n r) B ext anchor scale.val=
      PrefixControl.run (keySize n r)
        ((queries rows C H K service.solver (anchor.good,⟨anchor.coefficient,hj⟩)).cell
          scale (ω ⟨anchor.repetition,hrep⟩)).answer
        (fun pre => (service.run (QuantumService.cellRequest rows C H K
          (anchor.good,⟨anchor.coefficient,hj⟩) scale (ω ⟨anchor.repetition,hrep⟩) pre)).time)
        (4*B+1) := by
  let oracle := fun pre => service.run (QuantumService.cellRequest rows C H K
    (anchor.good,⟨anchor.coefficient,hj⟩) scale (ω ⟨anchor.repetition,hrep⟩) pre)
  have ha := concrete_cell_agreement rows C H K service m ω D ext hboundary
    { anchor with scale := scale.val } hj hrep scale.isLt
  have hx : PrefixMachine.execute (keySize n r) (cellOracle ext anchor scale.val) [] (4*B+1)=
      PrefixMachine.execute (keySize n r) oracle [] (4*B+1) := by
    apply execute_eq_on_extensions
    intro tail ht
    simpa [PrefixAgreement,cellOracle,oracle,cellKey] using ha tail ht
  unfold cellResult
  rw [hx]
  exact concrete_cell_control_eq rows C H K service B
    (anchor.good,⟨anchor.coefficient,hj⟩) scale (ω ⟨anchor.repetition,hrep⟩)

include hboundary in
/-- Ascending NAT opcode order is proved equal to ascending Fin/ofFn order. -/
theorem concrete_cell_controls :
    (List.range (keySize n r+1)).map (cellResult (keySize n r) B ext anchor)=
      CachedControl.cells (queries rows C H K service.solver (anchor.good,⟨anchor.coefficient,hj⟩))
        B (ω ⟨anchor.repetition,hrep⟩)
        (fun scale pre => (service.run (QuantumService.cellRequest rows C H K
          (anchor.good,⟨anchor.coefficient,hj⟩) scale (ω ⟨anchor.repetition,hrep⟩) pre)).time) := by
  unfold CachedControl.cells
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact concrete_cellResult rows C H K service B m ω D ext hboundary anchor hj hrep
      ⟨i,by simpa using hi⟩

include hboundary in
/-- Literal SAME cached all-scales table, not just equal estimates or calls. -/
theorem concrete_cellEntries :
    cellEntries (keySize n r) B ext anchor (List.range (keySize n r+1))=
      (CountTable.build (fun scale => enumerate (keySize n r)
        ((queries rows C H K service.solver (anchor.good,⟨anchor.coefficient,hj⟩)).cell
          scale (ω ⟨anchor.repetition,hrep⟩)).answer (4*B+1))).entries := by
  have hc := concrete_cell_controls rows C H K service B m ω D ext hboundary anchor hj hrep
  have ht := CachedControl.table_eq
    (queries rows C H K service.solver (anchor.good,⟨anchor.coefficient,hj⟩)) B
    (ω ⟨anchor.repetition,hrep⟩)
    (fun scale pre => (service.run (QuantumService.cellRequest rows C H K
      (anchor.good,⟨anchor.coefficient,hj⟩) scale (ω ⟨anchor.repetition,hrep⟩) pre)).time)
  have hm := congrArg (fun xs : List PrefixControl.Result => xs.map (fun x => (x.count,x.calls))) hc
  have he := congrArg CountTable.entries ht
  simpa [cellEntries,CachedControl.table,List.map_map,Function.comp_def] using hm.trans he

include hboundary in
/-- The actual invoke-time sum across the constructed cell block equals the
same measured source all-scales traversal; no time of an unexecuted call added. -/
theorem concrete_cellTimeSum :
    cellTimeSum (keySize n r) B ext anchor (List.range (keySize n r+1))=
      ((CachedControl.cells (queries rows C H K service.solver
          (anchor.good,⟨anchor.coefficient,hj⟩)) B (ω ⟨anchor.repetition,hrep⟩)
        (fun scale pre => (service.run (QuantumService.cellRequest rows C H K
          (anchor.good,⟨anchor.coefficient,hj⟩) scale (ω ⟨anchor.repetition,hrep⟩) pre)).time)).map
          PrefixControl.Result.oracleTime).sum := by
  have hc := concrete_cell_controls rows C H K service B m ω D ext hboundary anchor hj hrep
  simpa [cellTimeSum,List.map_map,Function.comp_def] using
    congrArg (fun xs : List PrefixControl.Result => (xs.map PrefixControl.Result.oracleTime).sum) hc

theorem cellCallSum_entries (q B : ℕ) (ext : External) (anchor : Config) (scales : List ℕ) :
    cellCallSum q B ext anchor scales=((cellEntries q B ext anchor scales).map Prod.snd).sum := by
  simp [cellCallSum,cellEntries,List.map_map,Function.comp_def]

end QecReliability.OracleCost.WholeWrapperCandidate
