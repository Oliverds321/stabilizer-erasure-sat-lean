import Trans.Control.StepA

/-!
# Trans.Control.StepB: fetch (one function per opcode), compile, endpoints, repair

* `fopK` (`K = 0 … 6`, argument `(op, (ctx, t))` with `t` = the configuration whose code is
  already the tail): the seven opcode cases of the `.fetch` phase; `fetchF` pops the opcode
  and dispatches on its tag.
* `compilePF`: `query := compile (X, request)` (the external parameter).
* `endpointZeroF`, `endpointOneF`: `endpoint (X, false/true)` (the external parameter).
* `repairAccF` (one scan step, reusing `entryF`, `ctrF`, `mdF` of `FL/Lib/LinearRepair.lean`)
  and `repairF` (the `.repair` phase).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Control
open QecReliability.FL QecReliability.FL.Lib QecReliability.FL.Lib.LinearRepairFL Tm

variable {TX : Ty}

/-- Argument of an opcode case: `(op, (ctx, t))`. -/
abbrev TFA (TX : Ty) : Ty := .prod TOp (TArg TX)

namespace FA
variable {Γ : List Ty}
/-- Opcode flag and argument of `w = (op, (ctx, t))`. -/
abbrev flag (w : Tm Γ (TFA TX)) : Tm Γ .bool := .fst (.snd (.fst w))
abbrev arg (w : Tm Γ (TFA TX)) : Tm Γ .nat := .snd (.snd (.fst w))
end FA

/-! ## Opcode cases (`.letE (A.cfg (.snd v0))`: `t` is `v0`, `w` is `v1`) -/

def fop0Body : Tm [TFA TX] TCfg :=
  .letE (A.cfg (.snd v0)) <|
    F.cfgWith v0 (g0 := F.g0With v0 (good := FA.flag v1) (coef := FA.arg v1))
      (g1 := F.g1With v0 (coefCalls := .zero)) (g2 := F.g2With v0 (trialsRev := .lnil))

def fop1Body : Tm [TFA TX] TCfg :=
  .letE (A.cfg (.snd v0)) <|
    F.cfgWith v0
      (g0 := F.g0With v0 (pc := .lit (2 : ℕ)) (rep := FA.arg v1) (tag := .ff) (nonempty := .ff))
      (g1 := F.g1With v0 (request := mk6 .ff (F.good v0) (F.coef v0) (FA.arg v1) .zero .lnil)
        (trialCalls := .zero))
      (g2 := F.g2With v0 (cellsRev := .lnil))

def fop2Body : Tm [TFA TX] TCfg :=
  .letE (A.cfg (.snd v0)) <|
    .ite (F.nonempty v0)
      (F.cfgWith v0 (g0 := F.g0With v0 (pc := .lit (1 : ℕ)) (scale := FA.arg v1))
        (g1 := F.g1With v0 (cellCalls := .zero)
          (pre := .pair (.pair .zero (.pair (A.q (.snd v1)) (.pair .lnil (Tm.fourOne (A.B (.snd v1))))))
            .lnil)))
      v0

def fop3Body : Tm [TFA TX] TCfg :=
  .letE (A.cfg (.snd v0)) <|
    .ite (F.nonempty v0)
      (F.cfgWith v0 (g0 := setPc v0 5)
        (g2 := F.g2With v0 (pairSrc := F.cellsRev v0) (pairDst := .lnil) (cellsRev := .lnil)))
      (F.cfgWith v0 (g0 := setPc v0 7) (g2 := F.g2With v0 (selected := .zero)))

def fop4Body (x : Ix TX) : Tm [TFA TX] TCfg :=
  .letE (A.cfg (.snd v0)) <|
    F.cfgWith v0 (g0 := setPc v0 8)
      (g3 := F.g3With v0 (sortTodo := .app (mapF (fstEF x.fstE) x.mapFst) (F.trialsRev v0))
        (sorted := .lnil))

def fop5Body : Tm [TFA TX] TCfg :=
  .letE (A.cfg (.snd v0)) <|
    .ite (F.good v0)
      (F.cfgWith v0 (g4 := F.g4With v0
        (goodRev := .lcons (.pair (F.selected v0) (F.coefCalls v0)) (F.goodRev v0))))
      (F.cfgWith v0 (g4 := F.g4With v0
        (badRev := .lcons (.pair (F.selected v0) (F.coefCalls v0)) (F.badRev v0))))

def fop6Body : Tm [TFA TX] TCfg :=
  .letE (A.cfg (.snd v0)) <|
    F.cfgWith v0 (g0 := setPc v0 12)
      (g2 := F.g2With v0 (pairSrc := F.goodRev v0) (pairDst := .lnil))
      (g4 := F.g4With v0 (goodRev := .lnil))

def fop0F (x : Ix TX) : FnSig (TFA TX) TCfg := bodySig x.fop0 fop0Body
def fop1F (x : Ix TX) : FnSig (TFA TX) TCfg := bodySig x.fop1 fop1Body
def fop2F (x : Ix TX) : FnSig (TFA TX) TCfg := bodySig x.fop2 fop2Body
def fop3F (x : Ix TX) : FnSig (TFA TX) TCfg := bodySig x.fop3 fop3Body
def fop4F (x : Ix TX) : FnSig (TFA TX) TCfg := bodySig x.fop4 (fop4Body x)
def fop5F (x : Ix TX) : FnSig (TFA TX) TCfg := bodySig x.fop5 fop5Body
def fop6F (x : Ix TX) : FnSig (TFA TX) TCfg := bodySig x.fop6 fop6Body

/-- `n = k` for a literal `k` (via `eqF`). -/
abbrev Tm.eqLit {Γ : List Ty} (x : Ix TX) (n : Tm Γ .nat) (k : ℕ) : Tm Γ .bool :=
  .app (eqF x.eq) (.pair n (.lit k))

/-- `.fetch`: pop the opcode (`[]` faults) and dispatch on its tag. Environment of the cons
branch after the `letE`: `v0 = w = (op, (ctx, t))`, `v1 = op`. -/
def fetchBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.code v0)
    (F.cfgWith v0 (g0 := setPc v0 19))
    (.letE (.pair v0 (.pair (.fst v3) (F.cfgWith v2 (g0 := F.g0With v2 (code := v1))))) <|
      .letE (.fst v1) <|
      .ite (.isZero v0) (.app (fop0F x) v1) <|
      .ite (Tm.eqLit x v0 1) (.app (fop1F x) v1) <|
      .ite (Tm.eqLit x v0 2) (.app (fop2F x) v1) <|
      .ite (Tm.eqLit x v0 3) (.app (fop3F x) v1) <|
      .ite (Tm.eqLit x v0 4) (.app (fop4F x) v1) <|
      .ite (Tm.eqLit x v0 5) (.app (fop5F x) v1) (.app (fop6F x) v1))

def fetchF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.fetch (fetchBody x)

/-! ## Compile and endpoints -/

def compilePBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <|
    F.cfgWith v0 (g0 := setPc v0 3)
      (g1 := F.g1With v0 (query := .app x.compile (.pair (A.X v1) (F.request v0))))

def endpointZeroBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <|
    F.cfgWith v0 (g0 := setPc v0 15)
      (g5 := F.g5With v0 (endpoint0 := .app x.endpoint (.pair (A.X v1) .ff)))

def endpointOneBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <|
    F.cfgWith v0 (g0 := setPc v0 16)
      (g4 := F.g4With v0 (repairGood := F.goodTable v0) (repairBad := F.badTable v0))
      (g5 := F.g5With v0 (endpoint1 := .app x.endpoint (.pair (A.X v1) .tt))
        (previous := F.endpoint0 v0) (repairIndex := .zero) (outputRev := .lnil))
      (g6 := F.g6With v0 (mad := .snd (F.endpoint0 v0)))

def compilePF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.compileP (compilePBody x)
def endpointZeroF (x : Ix TX) : FnSig (TArg TX) TCfg :=
  bodySig x.endpointZero (endpointZeroBody x)
def endpointOneF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.endpointOne (endpointOneBody x)

/-! ## Repair -/

/-- Argument of one repair step: `(r, cfg, g, gs, b, bs)`. -/
abbrev TRA : Ty := .prod .nat (.prod TCfg (.prod TEnt (.prod (.list TEnt) (.prod TEnt (.list TEnt)))))

abbrev mk4' {Γ : List Ty} (a : Tm Γ .bool) (b : Tm Γ .nat) (c d : Tm Γ TR) :
    Tm Γ (.prod .bool (.prod .nat (.prod TR TR))) := .pair a (.pair b (.pair c d))

/-- One repair step. Environment after the three `letE`s: `v0` counters, `v1 = (e, cur, out)`,
`v2` cfg, `v3` argument. -/
def repairAccBody (x : Ix TX) : Tm [TRA] TCfg :=
  .letE (p1 v0) <|
  .letE (.app (entryF x.entry)
      (.pair (mk4' .tt (p0 v1) (F.endpoint0 v0) (F.endpoint1 v0))
        (.pair (F.repairIndex v0) (.pair (F.previous v0) (.pair (p2 v1) (p4 v1)))))) <|
  .letE (.app (ctrF x.ctr) (mk7 (F.repairIndex v1) (p0 v2) .tt (F.pairVisits v1)
      (F.ratioBuilds v1) (F.orderComparisons v1) (F.endpointTests v1))) <|
    F.cfgWith v2 (g4 := F.g4With v2 (repairGood := p3 v3) (repairBad := q5 v3))
      (g5 := F.g5With v2 (previous := p1 v1)
        (repairIndex := .app (succF x.succ) (F.repairIndex v2))
        (outputRev := .lcons (q2 v1) (F.outputRev v2)))
      (g6 := mk5 (p0 v0) (p1 v0) (p2 v0) (q3 v0)
        (.app (mdF x.md) (mk5 (F.mad v2) (.snd (F.previous v2)) (.snd (p0 v1)) (.snd (p1 v1))
          (.snd (q2 v1)))))

def repairAccF (x : Ix TX) : FnSig TRA TCfg := bodySig x.repairAcc (repairAccBody x)

/-- `.repair`. Environments: `[cfg, arg]`; cons/nil: `[b, bs, cfg, arg]`; cons/cons:
`[b, bs, g, gs, cfg, arg]`. -/
def repairBody (x : Ix TX) : Tm [TArg TX] TCfg :=
  .letE (A.cfg v0) <| .lcase (F.repairGood v0)
    (.lcase (F.repairBad v0)
      (F.cfgWith v0 (g0 := setPc v0 17) (g5 := F.g5With v0 (output := .lnil)))
      (F.cfgWith v2 (g0 := setPc v2 19)))
    (.lcase (F.repairBad v2)
      (F.cfgWith v2 (g0 := setPc v2 19))
      (.app (repairAccF x) (mk6 (A.r v5) v4 v2 v3 v0 v1)))

def repairF (x : Ix TX) : FnSig (TArg TX) TCfg := bodySig x.repair (repairBody x)

/-! ## Validity -/

section Valid
variable {P : Program} {x : Ix TX} (h : LibOK P x)
include h

theorem fop_valid (h0 : P[x.fop0]? = some (fop0Body (TX := TX)).compile)
    (h1 : P[x.fop1]? = some (fop1Body (TX := TX)).compile)
    (h2 : P[x.fop2]? = some (fop2Body (TX := TX)).compile)
    (h3 : P[x.fop3]? = some (fop3Body (TX := TX)).compile)
    (h4 : P[x.fop4]? = some (fop4Body x).compile)
    (h5 : P[x.fop5]? = some (fop5Body (TX := TX)).compile)
    (h6 : P[x.fop6]? = some (fop6Body (TX := TX)).compile) :
    (∀ a, (fop0F x).ValidAt P a) ∧ (∀ a, (fop1F x).ValidAt P a) ∧ (∀ a, (fop2F x).ValidAt P a) ∧
    (∀ a, (fop3F x).ValidAt P a) ∧ (∀ a, (fop4F x).ValidAt P a) ∧ (∀ a, (fop5F x).ValidAt P a) ∧
    (∀ a, (fop6F x).ValidAt P a) := by
  refine ⟨fun a => bodySig_valid h0 ?_, fun a => bodySig_valid h1 ?_, fun a => bodySig_valid h2 ?_,
    fun a => bodySig_valid h3 ?_, fun a => bodySig_valid h4 ?_, fun a => bodySig_valid h5 ?_,
    fun a => bodySig_valid h6 ?_⟩ <;>
  simp [tm_simp, fop0Body, fop1Body, fop2Body, fop3Body, fop4Body, fop5Body, fop6Body,
    h.mapFst]

theorem fetch_valid (hf : (∀ a, (fop0F x).ValidAt P a) ∧ (∀ a, (fop1F x).ValidAt P a) ∧
      (∀ a, (fop2F x).ValidAt P a) ∧ (∀ a, (fop3F x).ValidAt P a) ∧
      (∀ a, (fop4F x).ValidAt P a) ∧ (∀ a, (fop5F x).ValidAt P a) ∧ (∀ a, (fop6F x).ValidAt P a))
    (hP : P[x.fetch]? = some (fetchBody x).compile) : ∀ a, (fetchF x).ValidAt P a := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := hf
  intro a; apply bodySig_valid hP
  simp only [tm_simp, fetchBody]
  split
  · simp
  · simp [h.eq, f0, f1, f2, f3, f4, f5, f6]

theorem compileP_valid (hP : P[x.compileP]? = some (compilePBody x).compile) :
    ∀ a, (compilePF x).ValidAt P a := by
  intro a; apply bodySig_valid hP; simp [tm_simp, compilePBody, h.compile]

theorem endpointZero_valid (hP : P[x.endpointZero]? = some (endpointZeroBody x).compile) :
    ∀ a, (endpointZeroF x).ValidAt P a := by
  intro a; apply bodySig_valid hP; simp [tm_simp, endpointZeroBody, h.endpoint]

theorem endpointOne_valid (hP : P[x.endpointOne]? = some (endpointOneBody x).compile) :
    ∀ a, (endpointOneF x).ValidAt P a := by
  intro a; apply bodySig_valid hP; simp [tm_simp, endpointOneBody, h.endpoint]

theorem repairAcc_valid (hP : P[x.repairAcc]? = some (repairAccBody x).compile) :
    ∀ a, (repairAccF x).ValidAt P a := by
  intro a; apply bodySig_valid hP; simp [tm_simp, repairAccBody, h.entry, h.ctr, h.md, h.succ]

theorem repair_valid (ha : ∀ a, (repairAccF x).ValidAt P a)
    (hP : P[x.repair]? = some (repairBody x).compile) : ∀ a, (repairF x).ValidAt P a := by
  intro a; apply bodySig_valid hP
  simp only [tm_simp, repairBody]
  split <;> split <;> simp [ha]

end Valid

end QecReliability.Trans.Control
