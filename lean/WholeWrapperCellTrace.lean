import WholeWrapperPrefixLift

/-! Complete actual cell-loop execution and its
single terminal commit, with persistent Config framing, native request order,
exact count/calls/service time, and dispatch bound. No cell-run success premise.
-/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open RationalOutput PrefixEnumeration

theorem prefixFrame_cellsRev {s t : Config} (h : prefixFrame s=prefixFrame t) :
    s.cellsRev=t.cellsRev := by simpa [prefixFrame] using congrArg Config.cellsRev h

theorem prefixFrame_trialCalls {s t : Config} (h : prefixFrame s=prefixFrame t) :
    s.trialCalls=t.trialCalls := by simpa [prefixFrame] using congrArg Config.trialCalls h

/-- The actual terminal native-return case commits precisely once. -/
theorem prefix_terminal_commit (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (count : ℕ) (hpc : s.pc=.prefix)
    (hstate : s.prefixState=⟨.ret count,[]⟩) :
    LocalTrace q r B m shape ext s 1
      { s with
        pc := .fetch,cellsRev := (count,s.cellCalls)::s.cellsRev,
        trialCalls := s.trialCalls+s.cellCalls } := by
  apply LocalTrace.single
  simp [step,hpc,hstate,PrefixTransitions.step,localEdge]

/-- Native halting supplies the execution; every actual intercepted query and
its returned cell value are connected to the OLD recursive PrefixMachine. -/
theorem cell_run_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (oracle : List Bool → SATReply)
    (hpc : s.pc=.prefix) (hstate : s.prefixState=⟨.enter q [] (4*B+1),[]⟩)
    (hzero : s.cellCalls=0) (hagrees : PrefixAgreement q ext s oracle) :
    let result := (PrefixMachine.execute q oracle [] (4*B+1)).control
    ∃ n pres t,
      PrefixTransitions.EmissionTrace oracle ⟨.enter q [] (4*B+1),[]⟩ n pres
        ⟨.ret result.count,[]⟩ ∧
      Trace q r B m shape ext s (prefixTraceTotals ext s oracle (n+1) pres)
        (pres.map (cellKey s)) t ∧
      t.pc=.fetch ∧ t.prefixState=⟨.ret result.count,[]⟩ ∧
      t.cellCalls=result.calls ∧
      t.cellsRev=(result.count,result.calls)::s.cellsRev ∧
      t.trialCalls=s.trialCalls+result.calls ∧
      prefixFrame t=prefixFrame
        { s with
          cellsRev := (result.count,result.calls)::s.cellsRev,
          trialCalls := s.trialCalls+result.calls } ∧
      pres.length=result.calls ∧
      (pres.map (fun pre => (oracle pre).time)).sum=result.oracleTime ∧
      (prefixTraceTotals ext s oracle (n+1) pres).dispatches≤8*result.calls+2 := by
  let result := (PrefixMachine.execute q oracle [] (4*B+1)).control
  obtain ⟨n,hnative,hn⟩ := PrefixTransitions.halts q oracle (4*B+1)
  change PrefixTransitions.Trace oracle _ n result.calls result.oracleTime _ at hnative
  obtain ⟨pres,hemissions,hlen,htime⟩ := hnative.emissions
  obtain ⟨mid,hpath,hmidpc,hmidstate,hmidcalls,hframe⟩ :=
    prefix_emission_trace q r B m shape ext s oracle hemissions s hpc hstate rfl
      (PrefixTransitions.initial_valid q (4*B+1)) hagrees
  have hcalls : mid.cellCalls=result.calls := by rw [hmidcalls,hzero,hlen]; omega
  have hcells := prefixFrame_cellsRev hframe
  have htrial := prefixFrame_trialCalls hframe
  let t : Config := { mid with
    pc := .fetch,
    cellsRev := (result.count,mid.cellCalls)::mid.cellsRev,
    trialCalls := mid.trialCalls+mid.cellCalls }
  have hcommit : LocalTrace q r B m shape ext mid 1 t :=
    prefix_terminal_commit q r B m shape ext mid result.count hmidpc hmidstate
  refine ⟨n,pres,t,hemissions,?_,rfl,?_,?_,?_,?_,?_,hlen,htime,?_⟩
  · have path := hpath.trans hcommit.toTrace
    simpa [prefixTraceTotals,Totals.append,localTotals,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using path
  · exact hmidstate
  · exact hcalls
  · simp [t,hcalls,hcells,result]
  · simp [t,hcalls,htrial,result]
  · have hf := congrArg (fun a : Config =>
        { a with
          cellsRev := (result.count,result.calls)::a.cellsRev,
          trialCalls := a.trialCalls+result.calls }) hframe
    simpa [prefixFrame,t,hcalls,result] using hf
  · change n+1+3*pres.length≤8*result.calls+2
    change n≤5*result.calls+1 at hn
    omega

/-- Includes the actual scheduled cell opcode fetch. Its result preserves
all persistent fields literally, except consumed code, current scale, and the
single appended cell/call record. No native-run premise is assumed. -/
theorem active_cell_opcode_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (scale : ℕ) (rest : List Opcode) (oracle : List Bool → SATReply)
    (hpc : s.pc=.fetch) (hcode : s.code=.cell scale::rest) (hnonempty : s.nonempty=true)
    (hagrees : PrefixAgreement q ext { s with scale := scale } oracle) :
    let result := (PrefixMachine.execute q oracle [] (4*B+1)).control
    ∃ n pres t,
      Trace q r B m shape ext s
        (prefixTraceTotals ext { s with scale := scale } oracle (n+2) pres)
        (pres.map (cellKey { s with scale := scale })) t ∧
      t.pc=.fetch ∧ t.code=rest ∧ t.scale=scale ∧
      t.cellsRev=(result.count,result.calls)::s.cellsRev ∧
      t.trialCalls=s.trialCalls+result.calls ∧
      prefixFrame t=prefixFrame
        { s with
          code := rest,scale := scale,
          cellsRev := (result.count,result.calls)::s.cellsRev,
          trialCalls := s.trialCalls+result.calls } ∧
      pres.length=result.calls ∧
      (pres.map (fun pre => (oracle pre).time)).sum=result.oracleTime ∧
      (prefixTraceTotals ext { s with scale := scale } oracle (n+2) pres).dispatches≤
        8*result.calls+3 ∧
      PrefixTransitions.EmissionTrace oracle ⟨.enter q [] (4*B+1),[]⟩ n pres
        ⟨.ret result.count,[]⟩ := by
  let start : Config := { s with
    pc := .prefix,code := rest,scale := scale,
    cellCalls := 0,prefixState := ⟨.enter q [] (4*B+1),[]⟩ }
  have hstart : step q r B m shape ext s=localEdge start := by
    simp [step,hpc,hcode,hnonempty,start,localEdge]
  have hagrees' : PrefixAgreement q ext start oracle := by
    simpa [PrefixAgreement,cellKey,start] using hagrees
  obtain ⟨n,pres,t,hemissions,hpath,htpc,htstate,htcalls,htcells,httrial,htframe,
      hlen,htime,hsteps⟩ := cell_run_trace q r B m shape ext start oracle rfl rfl rfl hagrees'
  have hcode' := congrArg Config.code htframe
  have hscale' := congrArg Config.scale htframe
  refine ⟨n,pres,t,?_,htpc,?_,?_,?_,?_,?_,hlen,htime,?_,hemissions⟩
  · have path := (LocalTrace.single hstart).toTrace.trans hpath
    have hkey : cellKey start=cellKey { s with scale := scale } := rfl
    rw [hkey] at path
    convert path using 1 <;>
      simp [start,prefixTraceTotals,prefixBoundaryPeak,cellKey,Totals.append,localTotals] <;> omega
  · simpa [prefixFrame,start] using hcode'
  · simpa [prefixFrame,start] using hscale'
  · simpa [start] using htcells
  · simpa [start] using httrial
  · simpa [prefixFrame,start] using htframe
  · simp only [prefixTraceTotals] at hsteps ⊢
    omega

/-- Exact count/call erasure for the original arbitrary-callback evaluator;
source exactness is needed only for its sharper CALL bound, not this identity. -/
theorem cell_execute_erases (q cap : ℕ) (oracle : List Bool → SATReply) :
    ((PrefixMachine.execute q oracle [] cap).control.count,
     (PrefixMachine.execute q oracle [] cap).control.calls)=
      enumerate q (fun pre => (oracle pre).value) cap := by
  have hc := PrefixMachine.control_eq q oracle [] cap
  simp only [List.nil_append] at hc
  rw [hc]
  exact Prod.ext (PrefixControl.erase _ _ _ _).1 (PrefixControl.erase _ _ _ _).2

/-- The FALSE branch is an actual local opcode fetch and makes no invocation. -/
theorem skipped_cell_opcode (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (scale : ℕ) (rest : List Opcode)
    (hpc : s.pc=.fetch) (hcode : s.code=.cell scale::rest) (hnonempty : s.nonempty=false) :
    LocalTrace q r B m shape ext s 1 { s with code := rest } := by
  apply LocalTrace.single
  simp [step,hpc,hcode,hnonempty,localEdge]

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- The generic agreement used by the actual-step lift is discharged by the
concrete existing request resolver on precisely the valid current indices. -/
theorem concrete_cell_agreement {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (m : ℕ) (ω : Fin (2*m+1) → Ω) (D : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)
    (s : Config) (hj : s.coefficient<r+1) (hrep : s.repetition<2*m+1)
    (hscale : s.scale<keySize n r+1) :
    PrefixAgreement (keySize n r) ext s
      (fun pre => service.run (QuantumService.cellRequest rows C H K
        (s.good,⟨s.coefficient,hj⟩) ⟨s.scale,hscale⟩ (ω ⟨s.repetition,hrep⟩) pre)) := by
  intro pre hp
  have hv : ValidKey (keySize n r) r m (cellKey s pre) := ⟨hj,hrep,hscale,hp⟩
  simpa [cellKey,resolveRequest] using hboundary.answer (cellKey s pre) hv

/-- The resulting record is literally the existing all-scales cached cell
record. No independently defined estimator replaces it. -/
theorem concrete_cell_execute_erases {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B : ℕ) (i : CoefficientIndex r) (scale : Fin (keySize n r+1)) (seed : Ω) :
    let oracle := fun pre => service.run (QuantumService.cellRequest rows C H K i scale seed pre)
    ((PrefixMachine.execute (keySize n r) oracle [] (4*B+1)).control.count,
     (PrefixMachine.execute (keySize n r) oracle [] (4*B+1)).control.calls)=
      enumerate (keySize n r) ((queries rows C H K service.solver i).cell scale seed).answer (4*B+1) := by
  dsimp only
  rw [cell_execute_erases]
  congr 1
  funext pre
  exact (QuantumService.cell_answer rows C H K service i scale seed pre).symm

/-- Full measured control, including exact service time, is the same cell
entry consumed by CachedControl.cells / QuantumService.prepareMeasured. -/
theorem concrete_cell_control_eq {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B : ℕ) (i : CoefficientIndex r) (scale : Fin (keySize n r+1)) (seed : Ω) :
    let oracle := fun pre => service.run (QuantumService.cellRequest rows C H K i scale seed pre)
    (PrefixMachine.execute (keySize n r) oracle [] (4*B+1)).control=
      PrefixControl.run (keySize n r)
        ((queries rows C H K service.solver i).cell scale seed).answer
        (fun pre => (service.run (QuantumService.cellRequest rows C H K i scale seed pre)).time)
        (4*B+1) := by
  dsimp only
  rw [PrefixMachine.control_eq]
  simp only [List.nil_append]
  congr 1
  funext pre
  exact (QuantumService.cell_answer rows C H K service i scale seed pre).symm

end QecReliability.OracleCost.WholeWrapperCandidate
