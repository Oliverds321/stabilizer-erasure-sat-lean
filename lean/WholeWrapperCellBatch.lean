import WholeWrapperBaseTrace

/-! Every scheduled cell is executed, in order,
before selection. Exact records/call/service-time sums and persistent framing
are derived from actual opcode traces, not assumed as a batch contract. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

def CellContextEq (s anchor : Config) : Prop :=
  s.good=anchor.good ∧ s.coefficient=anchor.coefficient ∧ s.repetition=anchor.repetition

def batchFrame (s : Config) : Config := prefixFrame { s with scale := 0 }

def cellOracle (ext : External) (anchor : Config) (scale : ℕ) : List Bool → SATReply :=
  fun pre => ext.sat (ext.compileQuery (cellKey { anchor with scale := scale } pre)).bits

def cellResult (q B : ℕ) (ext : External) (anchor : Config) (scale : ℕ) : PrefixControl.Result :=
  (PrefixMachine.execute q (cellOracle ext anchor scale) [] (4*B+1)).control

def cellEntries (q B : ℕ) (ext : External) (anchor : Config) (scales : List ℕ) : List Entry :=
  scales.map (fun j => ((cellResult q B ext anchor j).count,(cellResult q B ext anchor j).calls))

def cellCallSum (q B : ℕ) (ext : External) (anchor : Config) (scales : List ℕ) : ℕ :=
  (scales.map (fun j => (cellResult q B ext anchor j).calls)).sum

def cellTimeSum (q B : ℕ) (ext : External) (anchor : Config) (scales : List ℕ) : ℕ :=
  (scales.map (fun j => (cellResult q B ext anchor j).oracleTime)).sum

theorem cellKey_context {s anchor : Config} (h : CellContextEq s anchor)
    (j : ℕ) (pre : List Bool) :
    cellKey { s with scale := j } pre=cellKey { anchor with scale := j } pre := by
  rcases h with ⟨hg,hj,hr⟩
  simp [cellKey,hg,hj,hr]

theorem context_from_prefixFrame {s anchor : Config}
    (h : prefixFrame s=prefixFrame anchor) : CellContextEq s anchor := by
  exact ⟨by simpa [prefixFrame] using congrArg Config.good h,
    by simpa [prefixFrame] using congrArg Config.coefficient h,
    by simpa [prefixFrame] using congrArg Config.repetition h⟩

theorem CellContextEq.trans {s t u : Config} (h : CellContextEq s t)
    (g : CellContextEq t u) : CellContextEq s u :=
  ⟨h.1.trans g.1,h.2.1.trans g.2.1,h.2.2.trans g.2.2⟩

/-- Ordered native cell histories are ghost proof data, never Config fields. -/
inductive BatchCellEvents (q B : ℕ) (ext : External) (anchor : Config) :
    List ℕ → List RequestKey → Prop
  | nil : BatchCellEvents q B ext anchor [] []
  | cons {j js n pres tailEvents}
      (native : PrefixTransitions.EmissionTrace (cellOracle ext anchor j)
        ⟨.enter q [] (4*B+1),[]⟩ n pres ⟨.ret (cellResult q B ext anchor j).count,[]⟩)
      (tail : BatchCellEvents q B ext anchor js tailEvents) :
      BatchCellEvents q B ext anchor (j::js)
        (pres.map (cellKey { anchor with scale := j })++tailEvents)

/-- The whole active cell opcode block. All scales run; no acceptance test
can short-circuit construction because there is no selection phase here. -/
theorem active_cells_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (anchor : Config) (scales : List ℕ) (s : Config) (rest : List Opcode)
    (hpc : s.pc=.fetch) (hcode : s.code=scales.map Opcode.cell++rest)
    (hnonempty : s.nonempty=true) (hcontext : CellContextEq s anchor) :
    ∃ t totals events,
      Trace q r B m shape ext s totals events t ∧
      t.pc=.fetch ∧ t.code=rest ∧
      t.cellsRev=(cellEntries q B ext anchor scales).reverse++s.cellsRev ∧
      t.trialCalls=s.trialCalls+cellCallSum q B ext anchor scales ∧
      batchFrame t=batchFrame { s with
        code := rest,
        cellsRev := (cellEntries q B ext anchor scales).reverse++s.cellsRev,
        trialCalls := s.trialCalls+cellCallSum q B ext anchor scales } ∧
      totals.calls=cellCallSum q B ext anchor scales ∧
      totals.oracleTime=cellTimeSum q B ext anchor scales ∧ totals.endpointTime=0 ∧
      totals.dispatches≤8*cellCallSum q B ext anchor scales+3*scales.length ∧
      BatchCellEvents q B ext anchor scales events := by
  induction scales generalizing s with
  | nil =>
      have hc : s.code=rest := by simpa using hcode
      refine ⟨s,{},[],Trace.nil s,hpc,hc,?_,?_,?_,rfl,rfl,rfl,by simp,.nil⟩
      · simp [cellEntries]
      · simp [cellCallSum]
      · simp [batchFrame,cellEntries,cellCallSum,hc]
  | cons j js ih =>
      have hagrees : PrefixAgreement q ext { s with scale := j } (cellOracle ext anchor j) := by
        intro pre _
        simp only [cellOracle,cellKey_context hcontext]
      obtain ⟨n,pres,mid,hhead,hmidpc,hmidcode,hmidscale,hmidcells,hmidtrial,hmidframe,
          hlen,htime,hdispatch,hnative⟩ :=
        active_cell_opcode_trace q r B m shape ext s j (js.map Opcode.cell++rest)
          (cellOracle ext anchor j) hpc (by simpa using hcode) hnonempty hagrees
      have hmidnonempty : mid.nonempty=true := by
        have h := congrArg Config.nonempty hmidframe
        simpa [prefixFrame,hnonempty] using h
      have hmidcontext : CellContextEq mid anchor := by
        have h := context_from_prefixFrame hmidframe
        have h' : CellContextEq mid s := by simpa [CellContextEq] using h
        exact h'.trans hcontext
      obtain ⟨t,totals,events,ht,htpc,htcode,htcells,httrial,htframe,
          hcalls,hservice,hendpoint,hticks,hevents⟩ :=
        ih mid hmidpc hmidcode hmidnonempty hmidcontext
      let headTotals := prefixTraceTotals ext { s with scale := j }
        (cellOracle ext anchor j) (n+2) pres
      have hkeys : cellKey { s with scale := j }=cellKey { anchor with scale := j } :=
        funext (cellKey_context hcontext j)
      refine ⟨t,Totals.append headTotals totals,
        pres.map (cellKey { anchor with
        scale := j })++events,
        ?_,htpc,htcode,?_,?_,?_,?_,?_,?_,?_,.cons hnative hevents⟩
      · simpa [headTotals,hkeys] using hhead.trans ht
      · simpa [cellEntries,List.reverse_cons,List.append_assoc,hmidcells,cellResult]
          using htcells
      · simpa [cellCallSum,hmidtrial,cellResult,Nat.add_assoc] using httrial
      · have hf := congrArg (fun a : Config =>
            { a with
              scale := 0,code := rest,
              cellsRev := (cellEntries q B ext anchor js).reverse++a.cellsRev,
              trialCalls := a.trialCalls+cellCallSum q B ext anchor js }) hmidframe
        have hf' : batchFrame { mid with
              code := rest,
              cellsRev := (cellEntries q B ext anchor js).reverse++mid.cellsRev,
              trialCalls := mid.trialCalls+cellCallSum q B ext anchor js }=
            batchFrame { s with
              code := rest,
              cellsRev := (cellEntries q B ext anchor (j::js)).reverse++s.cellsRev,
              trialCalls := s.trialCalls+cellCallSum q B ext anchor (j::js) } := by
          simpa [batchFrame,prefixFrame,cellEntries,cellCallSum,cellResult,
            List.reverse_cons,List.append_assoc,Nat.add_assoc] using hf
        exact htframe.trans hf'
      · simp [Totals.append,headTotals,prefixTraceTotals,cellCallSum,cellResult,hlen,hcalls]
      · simp [Totals.append,headTotals,prefixTraceTotals,cellTimeSum,cellResult,htime,hservice]
      · simp [Totals.append,headTotals,prefixTraceTotals,hendpoint]
      · simp only [Totals.append,headTotals,prefixTraceTotals] at hdispatch ⊢
        simp only [cellCallSum,List.map_cons,List.sum_cons,List.length_cons]
        change n+2+3*pres.length+totals.dispatches≤
          8*((cellResult q B ext anchor j).calls+cellCallSum q B ext anchor js)+3*(js.length+1)
        change n+2+3*pres.length≤8*(cellResult q B ext anchor j).calls+3 at hdispatch
        omega

end QecReliability.OracleCost.WholeWrapperCandidate
