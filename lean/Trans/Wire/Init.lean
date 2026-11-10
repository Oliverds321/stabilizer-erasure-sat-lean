import Trans.Wire.Parse
import Trans.Control.Init
import Trans.Hash.Main

/-!
# Trans.Wire.Init: the initial loop state from the raw machine input

`initTopF : FnSig (list bool) (TArg TX)` maps the FL encoding of
`problemBits rows (iidProgram n) a b c d ++ coins` to the encoded initial loop state
`(ctx, encCfg s₀)`:

* the context `ctx = ((q, r, B, m), X)` with `q = keySize n n`, `r = n`,
  `B = rationalCellBudget a b`, `m = rationalRepetitionBudget (2 (n+1)) c d`, and the
  external data `X = (n, encRows rows, encProg (iidProgram n), q, SB, coins)` where
  `SB = L·(k+2)` for `(params base den q)` (= the seed length `seedBits L t`, see
  `Trans/Wire/Agree.lean`);
* `s₀ = initial q r m` if `n > 0`, and `zeroCfg` (`pc = .done`, `output = zeroVector`) if `n = 0`.

Arithmetic (library compositions, all `bodySig`): `ceilDivF` (total: `0` for divisor `0`),
`cellBF` (`rationalCellBudget`), `repBF` (`rationalRepetitionBudget (2(n+1))`), `seedBF`
(seed length through the hash parameter function `Fp`, e.g. `HashCallees.params`).

Main results: `initTopF_den_pos`, `initTopF_den_zero`, `initTop_valid` (every argument).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Wire
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_valid TCtx TArg TCfg encCfg encCtx
  IxI initF initF_den LibI init_valid)
open QecReliability.Trans.Hash (TParams params Params.tuple pK pL)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding

/-! ## Types -/

/-- FL type of a plain program (`Plain.ProgP`, the `encProg` encoding). -/
abbrev WProg : Ty := .prod (.list (.prod .bool (.prod .bool (.prod .nat .nat)))) (.list .nat)

/-- External data of the controller context: `(n, rows, C, q, SB, coins)`. -/
abbrev TX : Ty := .prod .nat (.prod TRowsW (.prod WProg (.prod .nat (.prod .nat (.list .bool)))))

/-! ## Plain values -/

/-- The seed length computed from the hash parameters. -/
def seedB (base den q : ℕ) : ℕ := (params base den q).L * ((params base den q).k + 1 + 1)

/-- The external data of an instance. -/
def wireX (base den : ℕ) {n : ℕ} (rows : List (List (PauliCoord n))) (coins : List Bool) : TX.den :=
  (n, Query.encRows rows, Query.encProg (ZeroLengthDispatch.iidProgram n), keySize n n,
    seedB base den (keySize n n), coins)

/-- The terminal configuration of the zero-length dispatch. -/
def zeroCfg : Config :=
  { pc := .done, output := ZeroLengthDispatch.zeroVector.entries.toList }

theorem encProg_iid (n : ℕ) :
    Query.encProg (ZeroLengthDispatch.iidProgram n) = ([], List.range n) := by
  simp only [Query.encProg, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [ZeroLengthDispatch.iidProgram, Program.pure]

/-! ## FL -/

/-- Indices of the arithmetic and initialisation functions. -/
structure AIx where
  ceilDiv : ℕ
  cellB : ℕ
  repB : ℕ
  seedB : ℕ
  ctx : ℕ
  init : ℕ

variable (L : Lib) (h : HIx) (p : PIx) (a : AIx) (y : IxI)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) TParams) (base den : ℕ)

/-- `(x, y) ↦ ceilDiv x y` (`0` if `y = 0`). -/
def ceilDivBody : Tm [.prod .nat .nat] .nat :=
  .ite (.isZero (.snd v0)) .zero
    (.fst (.app L.dmF (.pair (.app (predF L.pred) (.app (addF L.add) v0)) (.snd v0))))
def ceilDivF : FnSig (.prod .nat .nat) .nat := bodySig a.ceilDiv (ceilDivBody L)

/-- `(a, b) ↦ rationalCellBudget a b`. -/
def cellBBody : Tm [.prod .nat .nat] .nat :=
  .app (ceilDivF L a) (.pair
    (.app (mulF L.mul) (.pair (.app (mulF L.mul) (.pair (.lit (144 : ℕ)) (.snd v0))) (.snd v0)))
    (.app (mulF L.mul) (.pair (.fst v0) (.fst v0))))
def cellBF : FnSig (.prod .nat .nat) .nat := bodySig a.cellB (cellBBody L a)

/-- `(n, c, d) ↦ rationalRepetitionBudget (2 (n+1)) c d`. -/
def repBBody : Tm [.prod .nat (.prod .nat .nat)] .nat :=
  .app (subF L.sub) (.pair
    (.app (bitLenF L.bitLen) (.app (predF L.pred) (.app (ceilDivF L a) (.pair
      (.app (mulF L.mul) (.pair
        (.app (mulF L.mul) (.pair (.lit (2 : ℕ)) (.app (succF L.succ) (.fst v0)))) (.snd (.snd v0))))
      (.fst (.snd v0))))))
    (.lit (2 : ℕ)))
def repBF : FnSig (.prod .nat (.prod .nat .nat)) .nat := bodySig a.repB (repBBody L a)

/-- `q ↦ L·(k+2)` for the hash parameters of `(base, den, q)`. -/
def seedBBody : Tm [.nat] .nat :=
  .letE (.app Fp (.pair (.lit base) (.pair (.lit den) v0))) <|
  .app (mulF L.mul) (.pair (pL v0) (.app (succF L.succ) (.app (succF L.succ) (pK v0))))
def seedBF : FnSig .nat .nat := bodySig a.seedB (seedBBody L Fp base den)

/-- Projections of a parsed input `(n, rows, a, b, c, d, coins)`. -/
abbrev Pn {Γ : List Ty} (x : Tm Γ TParsed) : Tm Γ .nat := .fst x
abbrev Prows {Γ : List Ty} (x : Tm Γ TParsed) : Tm Γ TRowsW := .fst (.snd x)
abbrev Pa {Γ : List Ty} (x : Tm Γ TParsed) : Tm Γ .nat := .fst (.snd (.snd x))
abbrev Pb {Γ : List Ty} (x : Tm Γ TParsed) : Tm Γ .nat := .fst (.snd (.snd (.snd x)))
abbrev Pc {Γ : List Ty} (x : Tm Γ TParsed) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd x))))
abbrev Pd {Γ : List Ty} (x : Tm Γ TParsed) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd (.snd x)))))
abbrev Pcoins {Γ : List Ty} (x : Tm Γ TParsed) : Tm Γ (.list .bool) :=
  .snd (.snd (.snd (.snd (.snd (.snd x)))))

/-- `(n, rows, a, b, c, d, coins) ↦ ((q, n, B, m), (n, rows, C, q, SB, coins))`. -/
def ctxBody : Tm [TParsed] (TCtx TX) :=
  .letE (.app (addF L.add) (.pair (Pn v0) (.app (addF L.add) (.pair (Pn v0) (Pn v0))))) <|
  .pair
    (.pair v0 (.pair (Pn v1)
      (.pair (.app (cellBF L a) (.pair (Pa v1) (Pb v1)))
        (.app (repBF L a) (.pair (Pn v1) (.pair (Pc v1) (Pd v1)))))))
    (.pair (Pn v1) (.pair (Prows v1) (.pair (.pair .lnil (.app (rangeF L.range) (Pn v1)))
      (.pair v0 (.pair (.app (seedBF L a Fp base den) v0) (Pcoins v1))))))
def ctxF : FnSig TParsed (TCtx TX) := bodySig a.ctx (ctxBody L a Fp base den)

/-- **The init function**: raw input bits ↦ `(ctx, cfg₀)`. -/
def initTopBody : Tm [.list .bool] (TArg TX) :=
  .letE (.app (parseF L h p) v0) <|
  .letE (.app (ctxF L a Fp base den) v0) <|
  .pair v0 (.ite (.isZero (.fst v1)) (.lit (encCfg zeroCfg))
    (.app (initF y) (.pair (.fst (.fst v0)) (.pair (.fst v1) (.snd (.snd (.snd (.fst v0))))))))
def initTopF : FnSig (.list .bool) (TArg TX) := bodySig a.init (initTopBody L h p a y Fp base den)

/-! ## Meaning -/

theorem ceilDivF_den (x z : ℕ) : (ceilDivF L a).den (x, z) = ceilDiv x z := by
  by_cases hz : z = 0
  · subst hz; simp [ceilDivF, bodySig_den, ceilDivBody, tm_simp, ceilDiv]
  · simp [ceilDivF, bodySig_den, ceilDivBody, tm_simp, hz, ceilDiv]

theorem cellBF_den (x z : ℕ) : (cellBF L a).den (x, z) = rationalCellBudget x z := by
  simp only [cellBF, bodySig_den, cellBBody, tm_simp, mulF_den]
  rw [ceilDivF_den]
  rfl

theorem repBF_den (n c d : ℕ) :
    (repBF L a).den (n, c, d) = rationalRepetitionBudget (2 * (n + 1)) c d := by
  simp only [repBF, bodySig_den, repBBody, tm_simp, mulF_den, succF_den]
  rw [ceilDivF_den]
  rfl

theorem seedBF_den (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple) (q : ℕ) :
    (seedBF L a Fp base den).den q = seedB base den q := by
  simp only [seedBF, bodySig_den, seedBBody, tm_simp, mulF_den, succF_den, hFp]
  rfl

theorem ctxF_den (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple) {n : ℕ}
    (rows : List (List (PauliCoord n))) (x z c d : ℕ) (coins : List Bool) :
    (ctxF L a Fp base den).den (n, Query.encRows rows, x, z, c, d, coins) =
      encCtx (keySize n n) n (rationalCellBudget x z) (rationalRepetitionBudget (2 * (n + 1)) c d)
        (wireX base den rows coins) := by
  simp only [ctxF, bodySig_den, ctxBody, tm_simp, addF_den, rangeF_den]
  rw [cellBF_den, repBF_den, seedBF_den L a Fp base den hFp]
  simp only [encCtx, wireX, encProg_iid, keySize]

/-- **Init, positive instance.** -/
theorem initTopF_den_pos (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple) {k : ℕ}
    (rows : List (List (PauliCoord (k + 1)))) (x z c d : ℕ) (coins : List Bool) :
    (initTopF L h p a y Fp base den).den
        (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram (k + 1)) x z c d ++ coins) =
      (encCtx (keySize (k + 1) (k + 1)) (k + 1) (rationalCellBudget x z)
          (rationalRepetitionBudget (2 * (k + 1 + 1)) c d) (wireX base den rows coins),
        encCfg (initial (keySize (k + 1) (k + 1)) (k + 1)
          (rationalRepetitionBudget (2 * (k + 1 + 1)) c d))) := by
  simp only [initTopF, bodySig_den, initTopBody, tm_simp]
  rw [parseF_problemBits, ctxF_den L a Fp base den hFp]
  simp only [encCtx, Nat.add_one_ne_zero, Bool.false_eq_true, ↓reduceIte]
  rw [initF_den]

/-- **Init, `n = 0`.** -/
theorem initTopF_den_zero (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple)
    (rows : List (List (PauliCoord 0))) (x z c d : ℕ) (coins : List Bool) :
    (initTopF L h p a y Fp base den).den
        (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram 0) x z c d ++ coins) =
      (encCtx (keySize 0 0) 0 (rationalCellBudget x z) (rationalRepetitionBudget (2 * (0 + 1)) c d)
        (wireX base den rows coins), encCfg zeroCfg) := by
  simp only [initTopF, bodySig_den, initTopBody, tm_simp]
  rw [parseF_problemBits, ctxF_den L a Fp base den hFp]
  simp [encCtx]

theorem zeroCfg_pc : zeroCfg.pc = .done := rfl
theorem zeroCfg_output : zeroCfg.output = ZeroLengthDispatch.zeroVector.entries.toList := rfl

/-! ## Validity -/

/-- The arithmetic/init bodies are installed at their indices. -/
structure AIx.OK (P : Program) : Prop where
  ceilDiv : P[a.ceilDiv]? = some (ceilDivBody L).compile
  cellB : P[a.cellB]? = some (cellBBody L a).compile
  repB : P[a.repB]? = some (repBBody L a).compile
  seedB : P[a.seedB]? = some (seedBBody L Fp base den).compile
  ctx : P[a.ctx]? = some (ctxBody L a Fp base den).compile
  init : P[a.init]? = some (initTopBody L h p a y Fp base den).compile

section Valid
variable {L h p a y Fp base den} {P : Program} (hL : L.OK P)

include hL in
theorem ceilDiv_valid (hc : P[a.ceilDiv]? = some (ceilDivBody L).compile) :
    ∀ x, (ceilDivF L a).ValidAt P x := fun x => by
  refine bodySig_valid hc ?_
  obtain ⟨u, v⟩ := x
  by_cases hv : v = 0
  · subst hv; simp [tm_simp, ceilDivBody]
  · simp [tm_simp, ceilDivBody, hv, hL.pred, hL.add]
    exact hL.dm _ (Nat.pos_of_ne_zero hv)

variable (hFpv : ∀ x, Fp.ValidAt P x) (hA : a.OK L h p y Fp base den P)
include hL hA

theorem cellB_valid : ∀ x, (cellBF L a).ValidAt P x := fun x =>
  bodySig_valid hA.cellB (by simp [tm_simp, cellBBody, hL.mul, ceilDiv_valid hL hA.ceilDiv])

theorem repB_valid : ∀ x, (repBF L a).ValidAt P x := fun x =>
  bodySig_valid hA.repB (by
    simp [tm_simp, repBBody, hL.mul, hL.succ, hL.pred, hL.sub, hL.bitLen,
      ceilDiv_valid hL hA.ceilDiv])

include hFpv in
theorem seedB_valid : ∀ x, (seedBF L a Fp base den).ValidAt P x := fun x =>
  bodySig_valid hA.seedB (by simp [tm_simp, seedBBody, hL.mul, hL.succ, hFpv])

include hFpv in
theorem ctx_valid : ∀ x, (ctxF L a Fp base den).ValidAt P x := fun x =>
  bodySig_valid hA.ctx (by
    simp [tm_simp, ctxBody, hL.add, hL.range, cellB_valid hL hA, repB_valid hL hA,
      seedB_valid hL hFpv hA])

include hFpv in
/-- **Validity of the init function** at every argument. -/
theorem initTop_valid (hH : h.OK L P) (hp : p.OK L h P) (hI : LibI y P) :
    ∀ x, (initTopF L h p a y Fp base den).ValidAt P x := fun x => by
  refine bodySig_valid hA.init ?_
  simp only [tm_simp, initTopBody, parse_valid hL hH hp, ctx_valid hL hFpv hA, init_valid hI,
    true_and]
  split_ifs <;> trivial

end Valid

end QecReliability.Trans.Wire
