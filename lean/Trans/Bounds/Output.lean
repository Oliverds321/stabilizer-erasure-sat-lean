import Trans.Wire.Facts
import Trans.Query.Codec

/-!
# Trans.Bounds.Output: the output function and the loop-interface contract lemmas

* `ratHdrF : (num, den) ↦ natHeader num ++ natHeader den` (`Query.natHeaderF` twice, one
  `appendF`), `outWordF = flatMapF ratHdrF`, and **`outputF : (ctx, cfg) ↦ ratioWord output`**
  (`outputF_den`: `= Assembly.ratioWord s.output` on `encCfg s`), `output_valid`.
* `resumeTopF : (answer, (ctx, cfg)) ↦ answerSTF ((ctx, cfg), answer)` — the argument order of
  `Assembly.PositiveFacts.resume` (`Val.cons (Enc.bool answer) (enc s)`).
* `instReachable_ne_fault`: reachable states of an instance never have `pc = .fault`
  (from `PositiveRun.on_path`), so `isDoneF` decides `pc = .done` there (`isDone_den`).
* Contract form (validity + budget inequalities ⇒ `Assembly.Budget.Computes`), mirroring
  `Wire.init_computes`/`step_computes`: `isDone_computes`, `isInvoke_computes`,
  `query_computes`, `resume_computes`, `output_computes`, `output_zero_computes`
  (third conjunct of `ZeroFacts`), and `zeroFacts_of` (all of `ZeroFacts`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Bounds
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (TKey TR encKey encCfg encCtx IxR TArg TCfg TCtx bodySig
  bodySig_den bodySig_valid toR toR_eq)
open QecReliability.Trans.Wire (TX instX instEnc wireX zeroCfg)
open QecReliability.Trans.Hash (params)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

/-! ## The output function -/

/-- Indices of the output functions (and of the library functions they call). -/
structure OIx where
  pred : ℕ
  bitLen : ℕ
  replicate : ℕ
  append : ℕ
  word : ℕ
  natHeader : ℕ
  ratHdr : ℕ
  outWord : ℕ
  output : ℕ
  resumeTop : ℕ

section Defs
variable (o : OIx)

/-- `(num, den) ↦ natHeader num ++ natHeader den`. -/
def ratHdrBody : Tm [TR] (.list .bool) :=
  .app (appendF .bool o.append) (.pair (.app (Query.natHeaderF o.natHeader) (.fst v0))
    (.app (Query.natHeaderF o.natHeader) (.snd v0)))

def ratHdrF : FnSig TR (.list .bool) := bodySig o.ratHdr (ratHdrBody o)

/-- `ratioWord` on the ratio representation. -/
abbrev outWordF : FnSig (.list TR) (.list .bool) := flatMapF (ratHdrF o) o.outWord

/-- The output function on the loop state `(ctx, cfg)`. -/
def outputBody (TX' : Ty) : Tm [TArg TX'] (.list .bool) :=
  .app (outWordF o) (Control.F.output (Control.A.cfg v0))

def outputF (TX' : Ty) : FnSig (TArg TX') (.list .bool) := bodySig o.output (outputBody o TX')

/-- The resume function with the argument order of the contract: `(answer, (ctx, cfg))`. -/
def resumeTopBody {TX' : Ty} (x : Control.Ix TX') : Tm [.prod .bool (TArg TX')] (TArg TX') :=
  .app (Control.answerSTF x) (.pair (.snd v0) (.fst v0))

def resumeTopF {TX' : Ty} (x : Control.Ix TX') : FnSig (.prod .bool (TArg TX')) (TArg TX') :=
  bodySig o.resumeTop (resumeTopBody x)

end Defs

/-! ## Meaning -/

theorem ratHdrF_den (o : OIx) (p : ℕ × ℕ) :
    (ratHdrF o).den p = QueryCodec.natHeader p.1 ++ QueryCodec.natHeader p.2 := rfl

theorem outWord_map_toR (o : OIx) (xs : List RationalOutput.Ratio) :
    (xs.map toR).flatMap (ratHdrF o).den = Assembly.ratioWord xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.flatMap_cons, ih, ratHdrF_den, toR_eq, Assembly.ratioWord]

/-- **The output function computes the raw output word.** -/
theorem outputF_den (o : OIx) {TX' : Ty} (c : (TCtx TX').den) (s : Config) :
    (outputF o TX').den (c, encCfg s) = Assembly.ratioWord s.output := by
  rw [← outWord_map_toR o s.output]
  rfl

theorem resumeTopF_den (o : OIx) {TX' : Ty} (x : Control.Ix TX') (q r B m : ℕ) (X : TX'.den)
    (s : Config) (b : Bool) :
    (resumeTopF o x).den (b, (encCtx q r B m X, encCfg s)) =
      (encCtx q r B m X, encCfg { s with pc := .resume, reply := b }) := rfl

/-! ## Validity -/

/-- The output package installed in `P` (library functions valid, bodies at the indices). -/
structure OIx.OK (o : OIx) (P : Program) (TX' : Ty) (x : Control.Ix TX') : Prop where
  pred : ∀ n, (predF o.pred).ValidAt P n
  bitLen : ∀ n, (bitLenF o.bitLen).ValidAt P n
  replicate : ∀ y, (replicateF .bool o.replicate).ValidAt P y
  append : ∀ y, (appendF .bool o.append).ValidAt P y
  word : P[o.word]? = some (Query.wordBody o.pred o.word).compile
  natHeader : P[o.natHeader]? =
    some (Query.natHeaderBody o.bitLen o.replicate o.append o.word).compile
  ratHdr : P[o.ratHdr]? = some (ratHdrBody o).compile
  outWord : P[o.outWord]? = some (flatMapBody (ratHdrF o) o.append o.outWord).compile
  output : P[o.output]? = some (outputBody o TX').compile
  resumeTop : P[o.resumeTop]? = some (resumeTopBody x).compile

section Valid
variable {o : OIx} {P : Program} {TX' : Ty} {x : Control.Ix TX'} (h : o.OK P TX' x)
include h

theorem OIx.OK.natHeader_valid : ∀ n, (Query.natHeaderF o.natHeader).ValidAt P n :=
  Query.natHeader_valid h.bitLen h.replicate h.append (Query.word_valid h.pred h.word) h.natHeader

theorem OIx.OK.ratHdr_valid : ∀ p, (ratHdrF o).ValidAt P p := by
  intro p
  apply bodySig_valid h.ratHdr
  simp [tm_simp, ratHdrBody, h.natHeader_valid, h.append]

theorem OIx.OK.outWord_valid : ∀ xs, (outWordF o).ValidAt P xs :=
  fun xs => flatMap_valid h.append h.outWord xs (fun p _ => h.ratHdr_valid p)

theorem OIx.OK.output_valid : ∀ a, (outputF o TX').ValidAt P a := by
  intro a
  apply bodySig_valid h.output
  simp [tm_simp, outputBody, h.outWord_valid]

theorem OIx.OK.resumeTop_valid (hA : ∀ a, (Control.answerSTF x).ValidAt P a) :
    ∀ a, (resumeTopF o x).ValidAt P a := by
  intro a
  apply bodySig_valid h.resumeTop
  simp [tm_simp, resumeTopBody, hA]

end Valid

/-- `answerSTF` is valid once `answerF` is (its body is a pair with one call). -/
theorem answerST_valid {P : Program} {TX' : Ty} {x : Control.Ix TX'}
    (ha : ∀ a, (Control.answerF x).ValidAt P a)
    (hP : P[x.answerST]? = some (Control.answerSTBody x).compile) :
    ∀ a, (Control.answerSTF x).ValidAt P a := by
  intro a
  apply bodySig_valid hP
  simp [tm_simp, Control.answerSTBody, ha]

/-! ## Reachable states are never `.fault` -/

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : CertifiedParity (512*t) (64*t) t)

section Instance
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : MultiTape.Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT E density PtE PsE T)

theorem instReachable_ne_fault (hT : Monotone T) {a b c d k : ℕ}
    (rows : List (List (PauliCoord (k+1)))) (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd' : 0 < d) {s : Config}
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) : s.pc ≠ .fault := by
  obtain ⟨final, totals, PR⟩ := (macro_main hD hd A spec hT a b c d ha
    (lt_of_lt_of_le ha hab) hc hd' hab).positive k rows (coinWord hD hd A c d (k+1) coins)
  obtain ⟨rest, ev, tr⟩ := PR.on_path s hs
  intro hf
  cases tr with
  | nil =>
    have h1 := PR.done
    rw [hf] at h1
    cases h1
  | cons he _ =>
    rw [(Control.step_none_iff _ _ _ _ _ s true).mpr (.inr hf)] at he
    cases he

end Instance

/-- `isDoneF` decides `pc = .done` away from `.fault`. -/
theorem isDone_den {TX' : Ty} (x : Control.Ix TX') (q r B m : ℕ) (X : TX'.den) (s : Config)
    (hf : s.pc ≠ .fault) :
    (Control.isDoneF x).den (encCtx q r B m X, encCfg s) = decide (s.pc = .done) := by
  cases hp : s.pc <;>
    simp_all [Control.isDoneF, bodySig_den, Control.isDoneBody, tm_simp, encCfg, Control.pcCode]

theorem isInvoke_den {TX' : Ty} (x : Control.Ix TX') (q r B m : ℕ) (X : TX'.den) (s : Config) :
    (Control.isInvokeF x).den (encCtx q r B m X, encCfg s) = decide (s.pc = .invoke) := by
  cases hp : s.pc <;>
    simp [Control.isInvokeF, bodySig_den, Control.isInvokeBody, tm_simp, encCfg, hp,
      Control.pcCode]

theorem queryOf_den {TX' : Ty} (x : Control.Ix TX') (q r B m : ℕ) (X : TX'.den) (s : Config) :
    (Control.queryOfF x).den (encCtx q r B m X, encCfg s) = s.query := rfl

/-- The `.invoke` edge's successor. -/
theorem invoke_edge_next (q r B m : ℕ) (ext : External) (s : Config) (e : Edge)
    (hpc : s.pc = .invoke) (he : WholeWrapperCandidate.step q r B m true ext s = some e) :
    e.next = { s with pc := .resume, reply := (ext.sat s.query).value } := by
  have h := Control.invoke_next q r B m ext s hpc
  rw [he, Option.map_some, Option.some.injEq] at h
  exact h

/-! ## Contract form -/

/-- The context of an instance (the first component of `instEnc`). -/
noncomputable abbrev ictx (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) : (TCtx TX).den :=
  encCtx (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
    (instX hD hd A c d k rows coins)

theorem instEnc_eq (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (s : Config) :
    instEnc hD hd A a b c d k rows coins s =
      (TArg TX).enc (ictx hD hd A a b c d k rows coins, encCfg s) := rfl

section Contract
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : MultiTape.Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT E density PtE PsE T) (Bd : Assembly.Budget) {P : Program}
    {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)

/-- **`PositiveFacts.isDone`** from validity and the budget inequalities at the state. -/
theorem isDone_computes (hT : Monotone T) (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd' : 0 < d)
    (x : Control.Ix TX) (s : Config)
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s)
    (hv : (Control.isDoneF x).ValidAt P (ictx hD hd A a b c d k rows coins, encCfg s))
    (hm : (Control.isDoneF x).msize (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.value.eval (paperL rows a b c d))
    (harg : (instEnc hD hd A a b c d k rows coins s).size ≤ Bd.value.eval (paperL rows a b c d))
    (ht : (Control.isDoneF x).cost (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.cost.eval (paperL rows a b c d))
    (hdep : (Control.isDoneF x).depth (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.depth.eval (paperL rows a b c d)) :
    Bd.Computes P (paperL rows a b c d) x.isDone (instEnc hD hd A a b c d k rows coins s)
      (Enc.bool (decide (s.pc = .done))) := by
  have e := Assembly.Budget.computes_of_validAt hv hm harg ht hdep
  rw [isDone_den x _ _ _ _ _ s (instReachable_ne_fault hD hd A spec hT rows coins ha hab hc hd' hs)]
    at e
  exact e

/-- **`PositiveFacts.isInvoke`** (holds at every state). -/
theorem isInvoke_computes (x : Control.Ix TX) (s : Config)
    (hv : (Control.isInvokeF x).ValidAt P (ictx hD hd A a b c d k rows coins, encCfg s))
    (hm : (Control.isInvokeF x).msize (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.value.eval (paperL rows a b c d))
    (harg : (instEnc hD hd A a b c d k rows coins s).size ≤ Bd.value.eval (paperL rows a b c d))
    (ht : (Control.isInvokeF x).cost (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.cost.eval (paperL rows a b c d))
    (hdep : (Control.isInvokeF x).depth (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.depth.eval (paperL rows a b c d)) :
    Bd.Computes P (paperL rows a b c d) x.isInvoke (instEnc hD hd A a b c d k rows coins s)
      (Enc.bool (decide (s.pc = .invoke))) := by
  have e := Assembly.Budget.computes_of_validAt hv hm harg ht hdep
  rw [isInvoke_den] at e
  exact e

/-- **`PositiveFacts.query`** (holds at every state). -/
theorem query_computes (x : Control.Ix TX) (s : Config)
    (hv : (Control.queryOfF x).ValidAt P (ictx hD hd A a b c d k rows coins, encCfg s))
    (hm : (Control.queryOfF x).msize (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.value.eval (paperL rows a b c d))
    (harg : (instEnc hD hd A a b c d k rows coins s).size ≤ Bd.value.eval (paperL rows a b c d))
    (ht : (Control.queryOfF x).cost (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.cost.eval (paperL rows a b c d))
    (hdep : (Control.queryOfF x).depth (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.depth.eval (paperL rows a b c d)) :
    Bd.Computes P (paperL rows a b c d) x.queryOf (instEnc hD hd A a b c d k rows coins s)
      (Assembly.bitsVal s.query) := by
  have e := Assembly.Budget.computes_of_validAt hv hm harg ht hdep
  rw [queryOf_den] at e
  exact e

/-- **`PositiveFacts.resume`** from validity and the budget inequalities at
`(answer, state)`. -/
theorem resume_computes (o : OIx) (x : Control.Ix TX) (s : Config) (e : Edge)
    (hpc : s.pc = .invoke) (he : Assembly.instStep hD hd A spec a b c d k rows coins s = some e)
    (hv : (resumeTopF o x).ValidAt P
      (((Assembly.instExt hD hd A spec c d k rows coins).sat s.query).value,
        (ictx hD hd A a b c d k rows coins, encCfg s)))
    (hm : (resumeTopF o x).msize
      (((Assembly.instExt hD hd A spec c d k rows coins).sat s.query).value,
        (ictx hD hd A a b c d k rows coins, encCfg s)) ≤ Bd.value.eval (paperL rows a b c d))
    (harg : (Val.cons (Enc.bool ((Assembly.instExt hD hd A spec c d k rows coins).sat
        s.query).value) (instEnc hD hd A a b c d k rows coins s)).size ≤
      Bd.value.eval (paperL rows a b c d))
    (ht : (resumeTopF o x).cost
      (((Assembly.instExt hD hd A spec c d k rows coins).sat s.query).value,
        (ictx hD hd A a b c d k rows coins, encCfg s)) ≤ Bd.cost.eval (paperL rows a b c d))
    (hdep : (resumeTopF o x).depth
      (((Assembly.instExt hD hd A spec c d k rows coins).sat s.query).value,
        (ictx hD hd A a b c d k rows coins, encCfg s)) ≤ Bd.depth.eval (paperL rows a b c d)) :
    Bd.Computes P (paperL rows a b c d) o.resumeTop
      (Val.cons (Enc.bool ((Assembly.instExt hD hd A spec c d k rows coins).sat s.query).value)
        (instEnc hD hd A a b c d k rows coins s))
      (instEnc hD hd A a b c d k rows coins e.next) := by
  have e' := Assembly.Budget.computes_of_validAt hv hm harg ht hdep
  rw [resumeTopF_den, ← invoke_edge_next _ _ _ _ _ s e hpc he] at e'
  exact e'

/-- **`PositiveFacts.output`** (holds at every state). -/
theorem output_computes (o : OIx) (s : Config)
    (hv : (outputF o TX).ValidAt P (ictx hD hd A a b c d k rows coins, encCfg s))
    (hm : (outputF o TX).msize (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.value.eval (paperL rows a b c d))
    (harg : (instEnc hD hd A a b c d k rows coins s).size ≤ Bd.value.eval (paperL rows a b c d))
    (ht : (outputF o TX).cost (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.cost.eval (paperL rows a b c d))
    (hdep : (outputF o TX).depth (ictx hD hd A a b c d k rows coins, encCfg s) ≤
      Bd.depth.eval (paperL rows a b c d)) :
    Bd.Computes P (paperL rows a b c d) o.output (instEnc hD hd A a b c d k rows coins s)
      (Assembly.bitsVal (Assembly.ratioWord s.output)) := by
  have e := Assembly.Budget.computes_of_validAt hv hm harg ht hdep
  rw [outputF_den] at e
  exact e

end Contract

/-! ## `n = 0` -/

/-- The encoded zero-length state produced by `init` on the `n = 0` input. -/
noncomputable abbrev zeroArg (rows : List (List (PauliCoord 0))) (a b c d : ℕ) : (TArg TX).den :=
  (encCtx (keySize 0 0) 0 (rationalCellBudget a b) (rationalRepetitionBudget (2 * (0 + 1)) c d)
    (wireX (data hD hd A).base (data hD hd A).den rows []), encCfg zeroCfg)

/-- **`ZeroFacts`, third conjunct**: `output` at the zero-length state. -/
theorem output_zero_computes (o : OIx) (Bd : Assembly.Budget) {P : Program}
    (rows : List (List (PauliCoord 0))) (a b c d : ℕ)
    (hv : (outputF o TX).ValidAt P (zeroArg hD hd A rows a b c d))
    (hm : (outputF o TX).msize (zeroArg hD hd A rows a b c d) ≤ Bd.value.eval (paperL rows a b c d))
    (harg : ((TArg TX).enc (zeroArg hD hd A rows a b c d)).size ≤
      Bd.value.eval (paperL rows a b c d))
    (ht : (outputF o TX).cost (zeroArg hD hd A rows a b c d) ≤ Bd.cost.eval (paperL rows a b c d))
    (hdep : (outputF o TX).depth (zeroArg hD hd A rows a b c d) ≤
      Bd.depth.eval (paperL rows a b c d)) :
    Bd.Computes P (paperL rows a b c d) o.output ((TArg TX).enc (zeroArg hD hd A rows a b c d))
      (Assembly.bitsVal (outputWord ZeroLengthDispatch.zeroVector)) := by
  have e := Assembly.Budget.computes_of_validAt hv hm harg ht hdep
  rw [outputF_den, Wire.zero_output_word] at e
  exact e

/-- **All of `ZeroFacts`** from the three functions' validity and budget inequalities at the
`n = 0` input / state (the init and isDone parts are Wire's `init_zero_computes`,
`isDone_zero_computes`). -/
theorem zeroFacts_of (L : Wire.Lib) (h : Wire.HIx) (p : Wire.PIx) (aI : Wire.AIx)
    (yI : Control.IxI) (Fp : FnSig (.prod .nat (.prod .nat .nat)) Hash.TParams)
    (x : Control.Ix TX) (o : OIx) (I : Assembly.Indices) (Bd : Assembly.Budget) {P : Program}
    (hIi : I.init = aI.init) (hId : I.isDone = x.isDone) (hIo : I.output = o.output)
    (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple)
    (hvI : ∀ x, (Wire.initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).ValidAt P x)
    (rows : List (List (PauliCoord 0))) (a b c d : ℕ)
    (hmI : (Wire.initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).msize
      (machineInput rows a b c d []) ≤ Bd.value.eval (paperL rows a b c d))
    (hargI : (Ty.enc (.list .bool) (machineInput rows a b c d [])).size ≤
      Bd.value.eval (paperL rows a b c d))
    (htI : (Wire.initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).cost
      (machineInput rows a b c d []) ≤ Bd.cost.eval (paperL rows a b c d))
    (hdI : (Wire.initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).depth
      (machineInput rows a b c d []) ≤ Bd.depth.eval (paperL rows a b c d))
    (hvD : (Control.isDoneF x).ValidAt P (zeroArg hD hd A rows a b c d))
    (hmD : (Control.isDoneF x).msize (zeroArg hD hd A rows a b c d) ≤
      Bd.value.eval (paperL rows a b c d))
    (harg : ((TArg TX).enc (zeroArg hD hd A rows a b c d)).size ≤
      Bd.value.eval (paperL rows a b c d))
    (htD : (Control.isDoneF x).cost (zeroArg hD hd A rows a b c d) ≤
      Bd.cost.eval (paperL rows a b c d))
    (hdD : (Control.isDoneF x).depth (zeroArg hD hd A rows a b c d) ≤
      Bd.depth.eval (paperL rows a b c d))
    (hvO : (outputF o TX).ValidAt P (zeroArg hD hd A rows a b c d))
    (hmO : (outputF o TX).msize (zeroArg hD hd A rows a b c d) ≤
      Bd.value.eval (paperL rows a b c d))
    (htO : (outputF o TX).cost (zeroArg hD hd A rows a b c d) ≤ Bd.cost.eval (paperL rows a b c d))
    (hdO : (outputF o TX).depth (zeroArg hD hd A rows a b c d) ≤
      Bd.depth.eval (paperL rows a b c d)) :
    Assembly.ZeroFacts P I Bd rows a b c d := by
  refine ⟨(TArg TX).enc (zeroArg hD hd A rows a b c d), ?_, ?_, ?_⟩
  · rw [hIi]
    exact Wire.init_zero_computes hD hd A L h p aI yI Fp Bd hFp hvI rows a b c d hmI hargI htI hdI
  · rw [hId]
    have e := Assembly.Budget.computes_of_validAt hvD hmD harg htD hdD
    rw [isDone_den x _ _ _ _ _ zeroCfg (by simp [Wire.zeroCfg_pc])] at e
    exact e
  · rw [hIo]
    exact output_zero_computes hD hd A o Bd rows a b c d hvO hmO harg htO hdO

end QecReliability.Trans.Bounds
