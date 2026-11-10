import Trans.Hash.FLScalar
import Trans.Hash.Positive

/-!
# Trans.Hash.Main: the hash program in FL

`hashF`: `(base, den, q, r, bits) ↦ hashPlain base den q prog nb r bits`, assembled from the
component signatures (`paramsF`, `padF`, `pselectF`, the encoder index map, `affF`,
`seedRowsF`, `transF`, `pcomposeF`, `divModF`, the library) and the two oracles
`iprog` (`ell ↦ encProg (X.program ell)`) and the neighbor map `nb` (inside the encoder index map).

* `hash_valid`: validity and meaning, from the callees' contracts and meanings;
* `hash_den_encProg`: for `X : DyadicXorData`, `G : MGGInput` the meaning is
  `encProg` of the walk-circuit hash program (`Corr.lean`);
* `hash_den_positive`: the instance `positiveCircuits hD hd A k` used by the algorithm.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Hash
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.Trans.Query QecReliability.Trans.Query.Plain

variable {P : Program}

abbrev THashArg : Ty := .prod .nat (.prod .nat (.prod .nat (.prod .nat (.list .bool))))

/-- The callee signatures of `hashF`. -/
structure HashCallees where
  params : FnSig (.prod .nat (.prod .nat .nat)) TParams
  pad : FnSig (.prod .nat (.prod .nat (.prod .nat TProg))) TProg
  prog : FnSig .nat TProg
  sel : FnSig (.prod TProg (.list .nat)) TProg
  encOuts : FnSig (.prod (.prod .nat (.prod .nat (.prod .nat .nat))) (.list .nat)) (.list .nat)
  range : ℕ
  mul : ℕ
  succ : ℕ
  aff : FnSig (.prod .nat (.prod .nat (.prod .nat (.list TRow)))) TProg
  rows : FnSig (.prod .nat (.prod .nat (.list .bool))) (.list TRow)
  trans : FnSig (.prod .nat TProg) TProg
  comp : FnSig (.prod .nat (.prod TProg TProg)) TProg
  dm : FnSig (.prod .nat .nat) (.prod .nat .nat)

section Proj
variable {Γ : List Ty}
abbrev pE1 (p : Tm Γ TParams) : Tm Γ .nat := .fst p
abbrev pN1 (p : Tm Γ TParams) : Tm Γ .nat := .fst (.snd p)
abbrev pS (p : Tm Γ TParams) : Tm Γ .nat := .fst (.snd (.snd p))
abbrev pOrd (p : Tm Γ TParams) : Tm Γ .nat := .fst (.snd (.snd (.snd p)))
abbrev pK (p : Tm Γ TParams) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd p))))
abbrev pD (p : Tm Γ TParams) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd (.snd p)))))
abbrev pM (p : Tm Γ TParams) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd (.snd (.snd p))))))
abbrev pE2 (p : Tm Γ TParams) : Tm Γ .nat := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))
abbrev pL (p : Tm Γ TParams) : Tm Γ .nat := .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))
abbrev aQ (a : Tm Γ THashArg) : Tm Γ .nat := .fst (.snd (.snd a))
abbrev aR (a : Tm Γ THashArg) : Tm Γ .nat := .fst (.snd (.snd (.snd a)))
abbrev aBits (a : Tm Γ THashArg) : Tm Γ (.list .bool) := .snd (.snd (.snd (.snd a)))
end Proj

/-- Contexts: `[p, arg]`, `[t, p, arg]`, `[Lt, t, p, arg]`, `[enc, …]`, `[aff, enc, …]`,
`[ext, aff, enc, …]`. -/
def hashBody (C : HashCallees) : Tm [THashArg] TProg :=
  .letE (.app C.params (.pair (.fst v0) (.pair (.fst (.snd v0)) (aQ v0))))
  (.letE (.app (succF C.succ) (pK v0))
  (.letE (.app (mulF C.mul) (.pair (pL v1) v0))
  (.letE (.app C.sel (.pair
      (.app C.pad (.pair (.fst (.app C.dm (.pair (pN1 v2) (.lit (4 : ℕ)))))
        (.pair (aQ v3) (.pair (pOrd v2) (.app C.prog (pE1 v2))))))
      (.app C.encOuts (.pair (.pair (pS v2) (.pair (pD v2) (.pair (pM v2) v1)))
        (.app (rangeF C.range) v0)))))
  (.letE (.app C.aff (.pair v1 (.pair v2 (.pair .zero
      (.app C.rows (.pair v2 (.pair (pL v3) (aBits v4))))))))
  (.letE (.app C.sel (.pair
      (.app C.trans (.pair (.fst (.app C.dm (.pair (pL v4) (.lit (4 : ℕ)))))
        (.app C.prog (pE2 v4))))
      (.app (rangeF C.range) (aQ v5))))
  (.app C.sel (.pair (.app C.comp (.pair (aQ v6) (.pair (.app C.comp (.pair (aQ v6) (.pair v2 v1)))
      v0)))
    (.app (rangeF C.range) (aR v6)))))))))

def hashF (C : HashCallees) (prog : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    FnSig THashArg TProg :=
  exactSig i (hashBody C) (fun x => hashPlain x.1 x.2.1 x.2.2.1 prog nb x.2.2.2.1 x.2.2.2.2)

theorem firstHit_ge (p : ℕ → Prop) [DecidablePred p] (fuel start : ℕ) :
    start ≤ UniformAdapter.firstHit p fuel start := by
  induction fuel generalizing start with
  | zero => simp [UniformAdapter.firstHit]
  | succ n ih =>
    simp only [UniformAdapter.firstHit]
    split_ifs
    · exact le_rfl
    · exact (Nat.le_succ start).trans (ih (start + 1))

theorem params_s_pos (base den q : ℕ) : 0 < (params base den q).s :=
  firstHit_ge _ _ 1

/-- **Validity and meaning of `hashF`.** -/
theorem hash_valid (C : HashCallees) (prog : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ) {i : ℕ}
    (hparams : ∀ x, C.params.ValidAt P x)
    (hparamsd : ∀ x, C.params.den x = (params x.1 x.2.1 x.2.2).tuple)
    (hpad : ∀ x, C.pad.ValidAt P x) (hpadd : ∀ x, C.pad.den x = padP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hprog : ∀ x, C.prog.ValidAt P x) (hprogd : ∀ x, C.prog.den x = prog x)
    (hsel : ∀ x, C.sel.ValidAt P x) (hseld : ∀ x, C.sel.den x = pselect x.1 x.2)
    (henc : ∀ x, 0 < x.1.2.1 ∧ 0 < x.1.2.2.1 ∧ 0 < x.1.2.2.2 → C.encOuts.ValidAt P x)
    (hencd : ∀ x, C.encOuts.den x =
      x.2.map (encIndex (nb x.1.1) 16 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    (hrange : ∀ x, (rangeF C.range).ValidAt P x) (hmul : ∀ x, (mulF C.mul).ValidAt P x)
    (hsucc : ∀ x, (succF C.succ).ValidAt P x)
    (haff : ∀ x, C.aff.ValidAt P x) (haffd : ∀ x, C.aff.den x = affP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hrows : ∀ x, C.rows.ValidAt P x) (hrowsd : ∀ x, C.rows.den x = seedRows x.1 x.2.1 x.2.2)
    (htrans : ∀ x, C.trans.ValidAt P x) (htransd : ∀ x, C.trans.den x = transP x.1 x.2)
    (hcomp : ∀ x, C.comp.ValidAt P x) (hcompd : ∀ x, C.comp.den x = pcompose x.1 x.2.1 x.2.2)
    (hdm : ∀ a, C.dm.ValidAt P (a, 4)) (hdmd : ∀ x, C.dm.den x = (x.1 / x.2, x.1 % x.2))
    (hP : P[i]? = some (hashBody C).compile) :
    ∀ x, (hashF C prog nb i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      obtain ⟨base, den, q, r, bits⟩ := x
      have hD : 0 < 16 ^ (params base den q).k := by positivity
      have hs := params_s_pos base den q
      have hM : 0 < (params base den q).s * (params base den q).s * 16 ^ (params base den q).k :=
        by positivity
      simp only [hashBody, tm_simp, hparamsd, Params.tuple, hparams, hpad, hprog, hsel, hrange,
        hmul, hsucc, haff, hrows, htrans, hcomp, hdm, true_and, and_true, succF_den, mulF_den,
        hdmd]
      refine henc _ ⟨?_, ?_, ?_⟩
      · simp only [params] at hD ⊢; exact hD
      · simp only [params] at hM ⊢; exact hM
      · simp)
    (fun x _ => by
      obtain ⟨base, den, q, r, bits⟩ := x
      simp only [hashBody, tm_simp, hparamsd, Params.tuple, hpadd, hprogd, hseld, hencd, haffd,
        hrowsd, htransd, hcompd, hdmd, succF_den, mulF_den, rangeF_den, hashPlain]) x trivial

/-! ## Meaning: the walk-circuit hash program -/

theorem hash_den_encProg (C : HashCallees) (i : ℕ) (X : UniformAdapter.DyadicXorData)
    (hb : 8 ≤ X.base) (G : UniformAdapter.MGGInput) (q : ℕ) {A : Type*}
    (e : A ≃ BitModels q) (r : Fin (q + 1)) (bits : List Bool)
    (hbits : bits.length = CodeHash.seedBits (X.walkCode hb G q).L ((X.walkCode hb G q).steps + 1)) :
    (hashF C (fun ell => encProg (X.program ell)) (gNbr G) i).den
        (X.base, X.den, q, r.val, bits) =
      encProg (((X.walkCircuits hb G q).forward e).compiled.implementation.program r
        (seedOfBits (X.walkCode hb G q).L ((X.walkCode hb G q).steps + 1) bits)) :=
  (encProg_hashProgram X hb G q e r bits hbits).symm

open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
  QecReliability.SharedCircuit.LatentEncoding QecReliability.SharedCircuit.FixedLocalEmitter.AllLength in
/-- **The algorithm's hash program**: for `q = keySize (k+1) (k+1)` and a seed given by its
bits, `hashF` at `(X.base, X.den, q, scale, bits)` (with `X = data hD hd A`, oracles
`encProg ∘ X.program` and `gNbr actualMGG`) means `encProg ((positiveCircuits hD hd A k).program …)`. -/
theorem hash_den_positive (C : HashCallees) (i : ℕ) {D t : ℕ} (hD : D = 16 ^ 384)
    (hd : D = 256 * t) (A : CertifiedParity (512 * t) (64 * t) t) (k : ℕ)
    (scale : Fin (keySize (k + 1) (k + 1) + 1)) (bits : List Bool)
    (hbits : bits.length = CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k)) :
    (hashF C (fun ell => encProg ((data hD hd A).program ell)) (gNbr actualMGG) i).den
        ((data hD hd A).base, (data hD hd A).den, keySize (k + 1) (k + 1), scale.val, bits) =
      encProg ((positiveCircuits hD hd A k).program scale
        (seedOfBits (positiveLength hD hd A k) (positiveWidth hD hd A k) bits)) :=
  (encProg_positiveProgram hD hd A k scale bits hbits).symm

end QecReliability.Trans.Hash
