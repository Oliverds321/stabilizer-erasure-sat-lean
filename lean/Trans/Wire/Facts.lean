import Trans.Wire.Agree

/-!
# Trans.Wire.Facts: the wire package in the form of `Assembly.PositiveFacts` / `ZeroFacts`

Given the validity of the FL functions in the final program `P` and the budget inequalities
at the argument (the closed-form bounds are a separate package), these theorems produce
the `Assembly.Budget.Computes` facts of the contract (`Assembly/Spec.lean`) with the state
encoding `instEnc` (`enc s = Ty.enc (TArg TX) (encCtx q r B m X, encCfg s)`):

* `init_computes` — the `init` field of `PositiveFacts`;
* `step_computes` — the `step` field of `PositiveFacts` (every non-invoke edge);
* `init_zero_computes`, `isDone_zero_computes` — the first two conjuncts of `ZeroFacts`
  (the third needs the output function of `Trans/Control`);
* `libOK_compile`, `libOK_endpoint` — the two external fields of Control's `LibOK` from
  the wrappers' validity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Wire
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Control (TKey TR encKey encCfg encCtx IxR TArg)
open QecReliability.Trans.Hash (THashArg params)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : CertifiedParity (512*t) (64*t) t)

/-! ## Control's external fields -/

/-- Plug the wire wrappers into a controller index table. -/
def withWire (x : Control.Ix TX) (L : Lib) (c : CIx) (Q : FnSig WQArg (.list .bool))
    (H : FnSig THashArg WProg) (base den density : ℕ) (y : IxR) : Control.Ix TX :=
  { x with compile := compileF L c Q H base den density, endpoint := endpointWF c y }

@[simp] theorem withWire_compile (x : Control.Ix TX) (L : Lib) (c : CIx)
    (Q : FnSig WQArg (.list .bool)) (H : FnSig THashArg WProg) (base den density : ℕ) (y : IxR) :
    (withWire x L c Q H base den density y).compile = compileF L c Q H base den density := rfl

@[simp] theorem withWire_endpoint (x : Control.Ix TX) (L : Lib) (c : CIx)
    (Q : FnSig WQArg (.list .bool)) (H : FnSig THashArg WProg) (base den density : ℕ) (y : IxR) :
    (withWire x L c Q H base den density y).endpoint = endpointWF c y := rfl

theorem libOK_compile {P : Program} {L : Lib} {c : CIx} {Q : FnSig WQArg (.list .bool)}
    {H : FnSig THashArg WProg} {base den density : ℕ} {y : IxR} (hL : L.OK P)
    (hQ : ∀ x, Q.ValidAt P x) (hH : ∀ x, H.ValidAt P x) (hC : c.OK L Q H base den density y P)
    (x : Control.Ix TX) (hxc : x.compile = compileF L c Q H base den density) :
    ∀ z, x.compile.ValidAt P z := by
  rw [hxc]; exact compile_valid hL hQ hH hC

theorem libOK_endpoint {P : Program} {c : CIx} {y : IxR} (hR : Control.LibR y P)
    (hE : P[c.endpointW]? = some (endpointWBody y).compile)
    (x : Control.Ix TX) (hxe : x.endpoint = endpointWF c y) :
    ∀ z, x.endpoint.ValidAt P z := by
  rw [hxe]; exact endpointW_valid hR hE

/-! ## Bundled indices and installation -/

/-- All indices of the wire package. -/
structure WIx where
  L : Lib
  h : HIx
  p : PIx
  a : AIx
  c : CIx

/-- Everything of the wire package installed in `P` (`yI`: Control's init indices, `Fp`: the
hash parameter function, `Q`/`H`: query/hash functions, `y`: Control's endpoint indices). -/
structure WIx.OK (w : WIx) (P : Program) (yI : Control.IxI)
    (Fp : FnSig (.prod .nat (.prod .nat .nat)) Hash.TParams) (Q : FnSig WQArg (.list .bool))
    (H : FnSig THashArg WProg) (base den density : ℕ) (y : IxR) : Prop where
  lib : w.L.OK P
  hdr : w.h.OK w.L P
  parse : w.p.OK w.L w.h P
  init : w.a.OK w.L w.h w.p yI Fp base den P
  wrap : w.c.OK w.L Q H base den density y P

section Bundled
variable {w : WIx} {P : Program} {yI : Control.IxI}
    {Fp : FnSig (.prod .nat (.prod .nat .nat)) Hash.TParams} {Q : FnSig WQArg (.list .bool)}
    {H : FnSig THashArg WProg} {base den density : ℕ} {y : IxR}
    (hw : w.OK P yI Fp Q H base den density y)
include hw

theorem WIx.OK.initTop_valid (hFpv : ∀ x, Fp.ValidAt P x) (hI : Control.LibI yI P) :
    ∀ x, (initTopF w.L w.h w.p w.a yI Fp base den).ValidAt P x :=
  Wire.initTop_valid hw.lib hFpv hw.init hw.hdr hw.parse hI

theorem WIx.OK.compile_valid (hQ : ∀ x, Q.ValidAt P x) (hH : ∀ x, H.ValidAt P x) :
    ∀ x, (compileF w.L w.c Q H base den density).ValidAt P x :=
  Wire.compile_valid hw.lib hQ hH hw.wrap

theorem WIx.OK.endpointW_valid (hR : Control.LibR y P) : ∀ x, (endpointWF w.c y).ValidAt P x :=
  Wire.endpointW_valid hR hw.wrap.endpointW

end Bundled

/-! ## Init -/

section Init
variable (L : Lib) (h : HIx) (p : PIx) (aI : AIx) (yI : Control.IxI)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Hash.TParams) (Bd : Assembly.Budget) {P : Program}

/-- **`PositiveFacts.init`** from validity and the budget inequalities at the input. -/
theorem init_computes (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple)
    (hv : ∀ x, (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).ValidAt P x)
    (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)
    (hm : (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).msize
      (machineInput rows a b c d (List.ofFn coins)) ≤ Bd.value.eval (paperL rows a b c d))
    (harg : (Ty.enc (.list .bool) (machineInput rows a b c d (List.ofFn coins))).size ≤
      Bd.value.eval (paperL rows a b c d))
    (ht : (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).cost
      (machineInput rows a b c d (List.ofFn coins)) ≤ Bd.cost.eval (paperL rows a b c d))
    (hdep : (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).depth
      (machineInput rows a b c d (List.ofFn coins)) ≤ Bd.depth.eval (paperL rows a b c d)) :
    Bd.Computes P (paperL rows a b c d) aI.init
      (Assembly.bitsVal (machineInput rows a b c d (List.ofFn coins)))
      (instEnc hD hd A a b c d k rows coins (Assembly.instInitial c d k)) := by
  have e := Assembly.Budget.computes_of_validAt (hv _) hm harg ht hdep
  rw [init_pos_enc hD hd A L h p aI yI Fp hFp] at e
  exact e

/-- **`ZeroFacts`, first conjunct**: `init` on the `n = 0` input. -/
theorem init_zero_computes (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple)
    (hv : ∀ x, (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).ValidAt P x)
    (rows : List (List (PauliCoord 0))) (a b c d : ℕ)
    (hm : (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).msize
      (machineInput rows a b c d []) ≤ Bd.value.eval (paperL rows a b c d))
    (harg : (Ty.enc (.list .bool) (machineInput rows a b c d [])).size ≤
      Bd.value.eval (paperL rows a b c d))
    (ht : (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).cost
      (machineInput rows a b c d []) ≤ Bd.cost.eval (paperL rows a b c d))
    (hdep : (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).depth
      (machineInput rows a b c d []) ≤ Bd.depth.eval (paperL rows a b c d)) :
    Bd.Computes P (paperL rows a b c d) aI.init (Assembly.bitsVal (machineInput rows a b c d []))
      ((TArg TX).enc (encCtx (keySize 0 0) 0 (rationalCellBudget a b)
        (rationalRepetitionBudget (2 * (0 + 1)) c d)
        (wireX (data hD hd A).base (data hD hd A).den rows []), encCfg zeroCfg)) := by
  have e := Assembly.Budget.computes_of_validAt (hv _) hm harg ht hdep
  rw [init_zero hD hd A L h p aI yI Fp hFp] at e
  exact e

end Init

/-- **`ZeroFacts`, second conjunct**: `isDone` answers `true` at the zero-length state. -/
theorem isDone_zero_computes {TX' : Ty} (x : Control.Ix TX') (Bd : Assembly.Budget)
    {P : Program} (Lp : ℕ) (q r B m : ℕ) (X : TX'.den) (ext : External)
    (hv : (Control.isDoneF x).ValidAt P (encCtx q r B m X, encCfg zeroCfg))
    (hm : (Control.isDoneF x).msize (encCtx q r B m X, encCfg zeroCfg) ≤ Bd.value.eval Lp)
    (harg : (Ty.enc (TArg TX') (encCtx q r B m X, encCfg zeroCfg)).size ≤ Bd.value.eval Lp)
    (ht : (Control.isDoneF x).cost (encCtx q r B m X, encCfg zeroCfg) ≤ Bd.cost.eval Lp)
    (hdep : (Control.isDoneF x).depth (encCtx q r B m X, encCfg zeroCfg) ≤ Bd.depth.eval Lp) :
    Bd.Computes P Lp x.isDone ((TArg TX').enc (encCtx q r B m X, encCfg zeroCfg))
      (Enc.bool true) := by
  have e := Assembly.Budget.computes_of_validAt hv hm harg ht hdep
  rw [zero_isDone x q r B m X ext] at e
  exact e

/-! ## Step -/

section Step
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : MultiTape.Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT E density PtE PsE T)
    (L : Lib) (cI : CIx) (Q : FnSig WQArg (.list .bool)) (H : FnSig THashArg WProg) (y : IxR)
    (Bd : Assembly.Budget) {P : Program}

/-- **`PositiveFacts.step`** from validity and the budget inequalities at the state. -/
theorem step_computes (hQd : ∀ p, Q.den p = Query.queryBits p)
    (hHd : ∀ x, H.den x = instHashDen hD hd A x) (x : Control.Ix TX)
    (hxc : x.compile = compileF L cI Q H (data hD hd A).base (data hD hd A).den density)
    (hxe : x.endpoint = endpointWF cI y)
    {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (s : Config) (e : Edge)
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) (hpc : s.pc ≠ .invoke)
    (he : Assembly.instStep hD hd A spec a b c d k rows coins s = some e)
    (hv : (Control.stepF x).ValidAt P (encCtx (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b)
      (macroM c d k) (instX hD hd A c d k rows coins), encCfg s))
    (hm : (Control.stepF x).msize (encCtx (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b)
      (macroM c d k) (instX hD hd A c d k rows coins), encCfg s) ≤
        Bd.value.eval (paperL rows a b c d))
    (harg : (instEnc hD hd A a b c d k rows coins s).size ≤ Bd.value.eval (paperL rows a b c d))
    (ht : (Control.stepF x).cost (encCtx (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b)
      (macroM c d k) (instX hD hd A c d k rows coins), encCfg s) ≤
        Bd.cost.eval (paperL rows a b c d))
    (hdep : (Control.stepF x).depth (encCtx (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b)
      (macroM c d k) (instX hD hd A c d k rows coins), encCfg s) ≤
        Bd.depth.eval (paperL rows a b c d)) :
    Bd.Computes P (paperL rows a b c d) x.step (instEnc hD hd A a b c d k rows coins s)
      (instEnc hD hd A a b c d k rows coins e.next) := by
  have e' := Assembly.Budget.computes_of_validAt hv hm harg ht hdep
  rw [wire_step_correct hD hd A spec L cI Q H y hQd hHd x hxc hxe rows coins e hs hpc he] at e'
  exact e'

end Step

end QecReliability.Trans.Wire
