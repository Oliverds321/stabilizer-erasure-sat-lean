import Trans.Control.StepMain

/-! Endpoint-only repair for arbitrary latent circuits. Exactly the two shape
flags in the pinned repair accumulator are false; the surrounding controller
record and list traversal are unchanged. No antitonicity promise is required. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.EndpointControllerFL
open FL FL.Lib FL.Lib.LinearRepairFL FL.Tm
open Trans.Control Trans.Control.Tm
open OracleCost OracleCost.WholeWrapperCandidate RationalOutput
variable {TX : Ty}

def repairAccBody (x : Ix TX) : Tm [TRA] TCfg :=
  .letE (p1 v0) <|
  .letE (.app (entryF x.entry)
      (.pair (mk4' .ff (p0 v1) (F.endpoint0 v0) (F.endpoint1 v0))
        (.pair (F.repairIndex v0) (.pair (F.previous v0) (.pair (p2 v1) (p4 v1)))))) <|
  .letE (.app (ctrF x.ctr) (mk7 (F.repairIndex v1) (p0 v2) .ff (F.pairVisits v1)
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


theorem repairAcc_valid {P : FL.Program} {x : Ix TX} (h : LibOK P x)
    (hi : P[x.repairAcc]? = some (repairAccBody x).compile) :
    ∀ a, (repairAccF x).ValidAt P a := by
  intro a
  apply bodySig_valid hi
  simp [tm_simp,repairAccBody,h.entry,h.ctr,h.md,h.succ]

theorem repair_valid {P : FL.Program} {x : Ix TX}
    (ha : ∀ a, (repairAccF x).ValidAt P a)
    (hi : P[x.repair]? = some (repairBody x).compile) :
    ∀ a, (repairF x).ValidAt P a := by
  intro a
  apply bodySig_valid hi
  simp only [tm_simp,repairBody]
  split <;> split <;> simp [ha]

/-- Only the repair phase can observe the shape-mode flag. -/
theorem step_mode_eq_of_not_repair (q r B m : ℕ) (ext : External) (s : Config)
    (h : s.pc ≠ .repair) :
    WholeWrapperCandidate.step q r B m false ext s =
      WholeWrapperCandidate.step q r B m true ext s := by
  cases hp : s.pc <;> try { exact False.elim (h hp) }
  all_goals simp only [WholeWrapperCandidate.step,hp]

/-- Representation of an endpoint-only entry; the emitted ratio is e, not a
running-minimum/clamped ratio. The internal previous field still stores cur. -/
theorem entryR_false_toR (r j : ℕ) (a ell prev : Ratio) (g b : ℕ × ℕ) :
    entryR (false,r,(a.num,a.den),(ell.num,ell.den)) j (prev.num,prev.den) g b =
      let e := LinearRepair.sourceEntry r a ell j g b
      let cur := if j = 0 then e else Ratio.lesser prev e
      ((e.num,e.den),(cur.num,cur.den),(e.num,e.den)) := by
  have h1 := toR_lesser
  have h2 := toR_counts
  simp only [LinearRepairFL.toR] at h1 h2
  simp only [entryR,LinearRepair.sourceEntry]
  split_ifs <;> simp_all

/-- Literal false-mode successor equality, including every malformed-list case. -/
theorem repair_correct (x : Ix TX) (q r B m : ℕ) (X : TX.den)
    (ext : External) (s : Config) (hpc : s.pc = .repair) :
    (WholeWrapperCandidate.step q r B m false ext s).map (fun e => encCfg e.next) =
      some ((repairF x).den (encCtx q r B m X,encCfg s)) := by
  rcases hg : s.repairGood with _ | ⟨g,gs⟩ <;> rcases hb : s.repairBad with _ | ⟨b,bs⟩
  · simp [repairF,repairBody,repairAccF,repairAccBody,ctl_simp,tm_simp,hpc,hg,hb]
  · simp [repairF,repairBody,repairAccF,repairAccBody,ctl_simp,tm_simp,hpc,hg,hb]
  · simp [repairF,repairBody,repairAccF,repairAccBody,ctl_simp,tm_simp,hpc,hg,hb]
  · simp only [repairF,repairBody,repairAccF,repairAccBody,ctl_simp,tm_simp,hpc,hg,hb,
      Option.map_some,entryF_den,ctrF_den,mdF_den,succF_den,toR_eq,LinearRepairFL.toR]
    rw [entryR_false_toR]
    simp [ctrR,toR_eq,LinearRepairFL.toR]

end QecReliability.LatentMachine.EndpointControllerFL

