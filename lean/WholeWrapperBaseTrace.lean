import WholeWrapperCellTrace

/-! Exact literal base-call state update and false-trial
skip loop; these are actual WholeWrapperCandidate steps, not oracle macros. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

def baseKey (s : Config) (rep : ℕ) : RequestKey := .base s.good s.coefficient rep

def baseAfter (ext : External) (s : Config) (rep : ℕ) (rest : List Opcode) : Config :=
  let key := baseKey s rep
  let reply := ext.sat (ext.compileQuery key).bits
  { s with
    pc := .fetch,code := rest,repetition := rep,returnTag := .base,
    request := key,query := [],reply := reply.value,nonempty := reply.value,
    cellsRev := [],trialCalls := 1 }

def baseTotals (ext : External) (s : Config) (rep : ℕ) : Totals :=
  let built := ext.compileQuery (baseKey s rep)
  let reply := ext.sat built.bits
  { dispatches := 4,calls := 1,oracleTime := reply.time,
    frontendTime := built.constructionTime,boundaryPeak := max built.constructionSpace reply.workspace }

/-- One actual opcode fetch followed by compile, invoke, resume. The returned
SAT bit, saved request, table clearing, and all unaffected registers are exact. -/
theorem base_opcode_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (rep : ℕ) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=.base rep::rest) :
    Trace q r B m shape ext s (baseTotals ext s rep) [baseKey s rep]
      (baseAfter ext s rep rest) := by
  let key := baseKey s rep
  let built := ext.compileQuery key
  let reply := ext.sat built.bits
  let s1 : Config := { s with
    pc := .compile,code := rest,repetition := rep,
    returnTag := .base,request := key,cellsRev := [],trialCalls := 0,nonempty := false }
  let s2 : Config := { s1 with pc := .invoke,query := built.bits }
  let s3 : Config := { s2 with pc := .resume,reply := reply.value }
  let t := baseAfter ext s rep rest
  let e0 : Edge := ⟨s1,0,0,0,0,0,none⟩
  let e1 : Edge := ⟨s2,0,0,built.constructionTime,0,built.constructionSpace,none⟩
  let e2 : Edge := ⟨s3,1,reply.time,0,0,reply.workspace,some key⟩
  let e3 : Edge := ⟨t,0,0,0,0,0,none⟩
  have h0 : step q r B m shape ext s=some e0 := by
    simp [step,hpc,hcode,e0,s1,key,baseKey,localEdge]
  have h1 : step q r B m shape ext s1=some e1 := by
    simp [step,e1,s1,s2,built]
  have h2 : step q r B m shape ext s2=some e2 := by
    simp [step,e2,s3,s2,s1,built,reply]
  have h3 : step q r B m shape ext s3=some e3 := by
    simp [step,e3,s3,s2,s1,t,baseAfter,key,built,reply,localEdge]
  have path := Trace.cons h0 (Trace.cons h1 (Trace.cons h2 (Trace.cons h3 (Trace.nil t))))
  simpa [e0,e1,e2,e3,t,key,built,reply,Totals.cons,baseTotals] using path

/-- False-base trials still consume every cell opcode, with no query or table
entry; the exact continuation and every data register remain framed. -/
theorem skipped_cells_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (scales : List ℕ) (s : Config) (rest : List Opcode)
    (hpc : s.pc=.fetch) (hcode : s.code=scales.map Opcode.cell++rest)
    (hnonempty : s.nonempty=false) :
    LocalTrace q r B m shape ext s scales.length { s with code := rest } := by
  induction scales generalizing s with
  | nil =>
      have hs : s.code=rest := by simpa using hcode
      rw [← hs]
      exact LocalTrace.nil s
  | cons scale scales ih =>
      let nxt : Config := { s with code := scales.map Opcode.cell++rest }
      have hs : LocalTrace q r B m shape ext s 1 nxt :=
        skipped_cell_opcode q r B m shape ext s scale _ hpc (by simpa using hcode) hnonempty
      have ht := ih nxt (by simpa [nxt] using hpc) rfl (by simpa [nxt] using hnonempty)
      simpa [nxt,Nat.add_comm] using hs.trans ht

/-- Explicit false selection and commit, preserving coefficient call totals. -/
theorem false_select_commit_trace (q r B m : ℕ) (shape : Bool) (ext : External)
    (s : Config) (rest : List Opcode) (hpc : s.pc=.fetch)
    (hcode : s.code=.select::rest) (hnonempty : s.nonempty=false) :
    LocalTrace q r B m shape ext s 2
      { s with
        pc := .fetch,code := rest,selected := 0,
        trialsRev := (0,s.trialCalls)::s.trialsRev,
        coefficientCalls := s.coefficientCalls+s.trialCalls } := by
  let mid : Config := { s with pc := .trialCommit,code := rest,selected := 0 }
  have h0 : step q r B m shape ext s=localEdge mid := by
    simp [step,hpc,hcode,hnonempty,mid,localEdge]
  have h1 : step q r B m shape ext mid=localEdge
      { s with
        pc := .fetch,code := rest,selected := 0,
        trialsRev := (0,s.trialCalls)::s.trialsRev,
        coefficientCalls := s.coefficientCalls+s.trialCalls } := by
    simp [step,mid,localEdge]
  exact (LocalTrace.single h0).trans (LocalTrace.single h1)

end QecReliability.OracleCost.WholeWrapperCandidate
