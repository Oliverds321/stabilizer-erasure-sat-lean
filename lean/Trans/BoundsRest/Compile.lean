import Trans.BoundsRest.Mag
import Trans.BoundsEnc.Main

/-!
# Trans.BoundsRest.Compile: the compile callee within one polynomial envelope

`BoundsQH.compile_poly` bounds `compileF … (queryFnF stdIx) H base den D` by `G K C M` whenever
`mag (X, key) ≤ M`; `Mag.arg_mag_le` gives `mag (instX …, encKey key) ≤ magK sc L` for every
valid key, and `G K C ∘ magK sc` is polynomially bounded (`G_poly`). Hence:

* `G_comp_pb`: `L ↦ G K C (f L)` is `PolyBounded` when `f` is;
* `compile_envelope`: one `PolynomialEnvelope` `P` with cost/depth/msize `≤ P.eval L` whenever
  `mag y ≤ magK sc L` (any hash function `H` bounded at the constant-`(base, den)` arguments);
* **`compile_budget`**: at every reachable state of an instance,
  `cost/depth/msize of compileF at (instX …, encKey s.request) ≤ P.eval (paperL …)` — the
  `hcomp` hypothesis of `BoundsStep.step_budget` (for any `x` with `x.compile = compileF …`);
* **`compile_budget_concrete`**: the same with `H := hashF C (encProg ∘ program) (gNbr actualMGG) i`
  for any `HashCallees` record `C` satisfying the hypotheses of `BoundsEnc.hash_concrete_bound`
  (concrete encoder oracle `progF`, encoder-output map `encOutsF`, and the data-independent
  combinators `PolyB` with their meanings — `paramsF_on padF_P pselectF_P affF_P seedRowsF_P
  transF_P pcomposeF_P divModF_P` of BoundsQH).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.BoundsRest
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH (G G_poly FnBAt PolyB)
open QecReliability.Trans.Control (TKey encKey)
open QecReliability.Trans.Wire (TX instX wireX TRowsW TCoordW WProg seedB CIx compileF)
open QecReliability.Trans.Hash (THashArg HashCallees hashF gNbr params padP pselect affP seedRows
  transP pcompose)
open QecReliability.Trans.HashCallees (progF encOutsF encConsts EncIx RotIx)
open QecReliability.Trans.Bounds (coinPoly)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

/-- `L ↦ G K C (f L)` is polynomially bounded when `f` is (degree `2^K`, `G_poly`). -/
theorem G_comp_pb (K C : ℕ) {f : ℕ → ℕ} (hf : Assembly.PolyBounded f) :
    Assembly.PolyBounded (fun L => G K C (f L)) := by
  have h : Assembly.PolyBounded (fun L => 26 ^ (2 ^ K - 1) * (f L + C + 4) ^ (2 ^ K)) := by
    poly_bounded
  exact h.mono (fun L => by have := G_poly K C (f L); omega)

/-- **One envelope for the compile wrapper** on arguments of magnitude `≤ magK sc L`. -/
theorem compile_envelope (WL : Wire.Lib) (cI : CIx) (H : FnSig THashArg WProg)
    (base den density sc : ℕ) {kH cH : ℕ}
    (hH : ∀ q r bits, FnBAt (G kH cH) H (base, den, q, r, bits)) :
    ∃ P : PolynomialEnvelope, ∀ (L : ℕ) (y : (Ty.prod TX TKey).den),
      mag (.prod TX TKey) y ≤ magK sc L →
      (compileF WL cI (Query.queryFnF Query.stdIx) H base den density).cost y ≤ P.eval L ∧
      (compileF WL cI (Query.queryFnF Query.stdIx) H base den density).depth y ≤ P.eval L ∧
      (compileF WL cI (Query.queryFnF Query.stdIx) H base den density).msize y ≤ P.eval L := by
  obtain ⟨K, C, h⟩ := BoundsQH.compile_poly WL cI H base den density hH
  obtain ⟨P, hP⟩ := (G_comp_pb K C (magK_pb sc)).envelope
  refine ⟨P, fun L y hy => ?_⟩
  obtain ⟨h1, h2, h3, -, -⟩ := h _ y hy
  have := hP L
  exact ⟨h1.trans this, h2.trans this, h3.trans this⟩

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : CertifiedParity (512*t) (64*t) t)

section Reach
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : MultiTape.Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT E density PtE PsE T)

/-- **Compile envelope.** For any hash function `H` bounded at the arguments with the instance's
hash constants, one envelope bounds the compile callee at the request of every reachable state
(the `hcomp` hypothesis of `BoundsStep.step_budget`, for `x.compile = compileF …`). -/
theorem compile_budget (WL : Wire.Lib) (cI : CIx) (H : FnSig THashArg WProg) {kH cH : ℕ}
    (hH : ∀ q r bits, FnBAt (G kH cH) H ((data hD hd A).base, (data hD hd A).den, q, r, bits)) :
    ∃ P : PolynomialEnvelope, ∀ (x : Control.Ix TX),
      x.compile = compileF WL cI (Query.queryFnF Query.stdIx) H (data hD hd A).base
        (data hD hd A).den density →
      ∀ {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
        (coins : Fin (coinBits hD hd A c d (k+1)) → Bool), 0 < a → 0 < c → ∀ {s : Config},
      Assembly.InstReachable hD hd A spec a b c d k rows coins s →
      x.compile.cost (instX hD hd A c d k rows coins, encKey s.request) ≤
          P.eval (paperL rows a b c d) ∧
        x.compile.depth (instX hD hd A c d k rows coins, encKey s.request) ≤
          P.eval (paperL rows a b c d) ∧
        x.compile.msize (instX hD hd A c d k rows coins, encKey s.request) ≤
          P.eval (paperL rows a b c d) := by
  obtain ⟨P, hP⟩ := compile_envelope WL cI H (data hD hd A).base (data hD hd A).den density
    (seedConstant hD hd A) hH
  refine ⟨P, fun x hx a b c d k rows coins ha hc s hs => ?_⟩
  rw [hx]
  exact hP _ _ (reach_arg_mag_le hD hd A spec rows coins ha hc hs)

/-- **Compile envelope, concrete hash program.** `compile_budget` with
`H = hashF C (encProg ∘ (data hD hd A).program) (gNbr actualMGG) i` for a `HashCallees` record
whose encoder oracle and encoder-output map are the concrete `progF`/`encOutsF` and whose
data-independent combinators satisfy `hash_concrete_bound`'s hypotheses. -/
theorem compile_budget_concrete (WL : Wire.Lib) (cI : CIx) (HL : HashCallees.Lib) (I : EncIx)
    (R : RotIx) (inbr ivs ifo iidx imap : ℕ) (C : HashCallees)
    (hCp : C.prog = progF HL I (encConsts D A))
    (hCe : C.encOuts = encOutsF HL R inbr ivs ifo iidx imap) (i : ℕ)
    {kp cp : ℕ}
    (hparams : ∀ q, FnBAt (G kp cp) C.params ((data hD hd A).base, (data hD hd A).den, q))
    (hparamsd : ∀ x, C.params.den x = (params x.1 x.2.1 x.2.2).tuple)
    (hpad : PolyB C.pad) (hsel : PolyB C.sel) (haff : PolyB C.aff)
    (hrows : PolyB C.rows) (htrans : PolyB C.trans) (hcomp : PolyB C.comp) (hdm : PolyB C.dm)
    (hpadd : ∀ x, C.pad.den x = padP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hseld : ∀ x, C.sel.den x = pselect x.1 x.2)
    (haffd : ∀ x, C.aff.den x = affP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hrowsd : ∀ x, C.rows.den x = seedRows x.1 x.2.1 x.2.2)
    (htransd : ∀ x, C.trans.den x = transP x.1 x.2)
    (hcompd : ∀ x, C.comp.den x = pcompose x.1 x.2.1 x.2.2)
    (hdmd : ∀ x, C.dm.den x = (x.1 / x.2, x.1 % x.2)) :
    ∃ P : PolynomialEnvelope, ∀ (x : Control.Ix TX),
      x.compile = compileF WL cI (Query.queryFnF Query.stdIx)
        (hashF C (fun ell => Query.encProg ((data hD hd A).program ell)) (gNbr actualMGG) i)
        (data hD hd A).base (data hD hd A).den density →
      ∀ {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
        (coins : Fin (coinBits hD hd A c d (k+1)) → Bool), 0 < a → 0 < c → ∀ {s : Config},
      Assembly.InstReachable hD hd A spec a b c d k rows coins s →
      x.compile.cost (instX hD hd A c d k rows coins, encKey s.request) ≤
          P.eval (paperL rows a b c d) ∧
        x.compile.depth (instX hD hd A c d k rows coins, encKey s.request) ≤
          P.eval (paperL rows a b c d) ∧
        x.compile.msize (instX hD hd A c d k rows coins, encKey s.request) ≤
          P.eval (paperL rows a b c d) := by
  have hb : 1 ≤ (data hD hd A).base := le_trans (by omega) (base_ge_eight hD hd A)
  obtain ⟨K, C', hH⟩ := BoundsEnc.hash_concrete_bound hD hd A HL I R inbr ivs ifo iidx imap C
    hCp hCe i _ _ hb hparams hparamsd hpad hsel haff hrows htrans hcomp hdm hpadd hseld haffd
    hrowsd htransd hcompd hdmd
  exact compile_budget hD hd A spec WL cI _ hH

end Reach

end QecReliability.Trans.BoundsRest
