import Trans.HashCallees.EncoderFLAmp

/-!
# Trans.HashCallees.EncoderFL: the encoder family in FL

* `oneCopyF` (`oneCopyP`, two `pcomposeF` calls of `Trans/Hash/FLWire.lean`);
* the recursion as a `foldl` from the base program (`encP_foldl`), step `encStepF`;
* `encF`: `(E, ell) ↦ encP E ell`; **`progF E`**: `ell ↦ encP E (ell + 1)` with the constants
  `E = (D, K, code)` as a literal (valid for `4 ≤ D`).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.HashCallees
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.Trans.Query.Plain QecReliability.Trans.Hash

variable {P : Program}

/-! ## Composition (`Trans/Hash/FLWire.lean`) -/

/-- Indices of `pcomposeF` and its table helpers. -/
structure PcIx where
  tw : ℕ
  gm : ℕ
  tg : ℕ
  twl : ℕ
  pc : ℕ

abbrev PcIx.twF (L : Lib) (I : PcIx) : FnSig (.prod TTab .nat) .nat :=
  Hash.twF L.lt L.gd L.add L.sub I.tw
abbrev PcIx.tgF (L : Lib) (I : PcIx) : FnSig (.prod TTab (.list TGate)) (.list TGate) :=
  tabGatesF (I.twF L) I.gm I.tg
abbrev PcIx.twlF (L : Lib) (I : PcIx) : FnSig (.prod TTab (.list .nat)) (.list .nat) :=
  tabWiresF (I.twF L) I.twl
abbrev PcIx.pcF (L : Lib) (I : PcIx) : FnSig (.prod .nat (.prod TProg TProg)) TProg :=
  pcomposeF L.len L.add L.app (I.tgF L) (I.twlF L) I.pc

structure PcIx.OK (P : Program) (L : Lib) (I : PcIx) : Prop where
  tw : P[I.tw]? = some (twBody L.lt L.gd L.add L.sub).compile
  gm : P[I.gm]? = some (gmapBody (I.twF L)).compile
  tg : P[I.tg]? = some (mapEnvBody (gmapF (I.twF L) I.gm) I.tg).compile
  twl : P[I.twl]? = some (mapEnvBody (I.twF L) I.twl).compile
  pc : P[I.pc]? = some (pcomposeBody L.len L.add L.app (I.tgF L) (I.twlF L)).compile

theorem PcIx.OK.valid {L : Lib} (hL : L.OK P) {I : PcIx} (hI : I.OK P L) :
    ∀ x, (I.pcF L).ValidAt P x := by
  have htw := tw_valid hL.lt hL.gd hL.add hL.sub hI.tw
  have htwd : ∀ x, (I.twF L).den x = tableWire x.1 x.2 := fun _ => rfl
  exact pcompose_valid hL.len hL.add (hL.app TGate)
    (mapEnv_validAll (gmap_valid htw htwd hI.gm) hI.tg) (mapEnv_validAll htw hI.twl)
    (fun _ => rfl) (fun x => tabWiresF_den _ _ htwd x.1 x.2) hI.pc

@[simp] theorem PcIx.pcF_den (L : Lib) (I : PcIx) (x : ℕ × ProgP × ProgP) :
    (I.pcF L).den x = pcompose x.1 x.2.1 x.2.2 := rfl

/-! ## One copy -/

abbrev TOne : Ty := .prod .nat (.prod TProg (.prod TProg TProg))

/-- Context `[f, rh, (n, R₁, H, R₂)]`. -/
def oneCopyBody (L : Lib) (I : PcIx) : Tm [TOne] TProg :=
  .letE (.app (I.pcF L) (.pair (.fst v0) (.pair (.fst (.snd v0)) (.fst (.snd (.snd v0))))))
  (.letE (.app (I.pcF L) (.pair (.fst v1) (.pair v0 (.snd (.snd (.snd v1))))))
    (.pair (.fst v0) (.app (appendF .nat L.app) (.pair
      (.app (appendF .nat L.app) (.pair (.app (rangeF L.range) (.fst v2)) (.snd v1)))
      (.snd v0)))))

def oneCopyF (L : Lib) (I : PcIx) (i : ℕ) : FnSig TOne TProg :=
  exactSig i (oneCopyBody L I) (fun x => oneCopyP x.1 x.2.1 x.2.2.1 x.2.2.2)

theorem oneCopy_valid {L : Lib} (hL : L.OK P) {I : PcIx} (hI : I.OK P L) {i : ℕ}
    (hP : P[i]? = some (oneCopyBody L I).compile) : ∀ x, (oneCopyF L I i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, oneCopyBody, hI.valid hL, hL.app, hL.range])
    (fun x _ => by simp [tm_simp, oneCopyBody, oneCopyP]) x trivial

/-! ## The recursion as a fold -/

/-- One level: state `(E, prog, w)` with `w = mwP D ell`. -/
def encStep (st : (ℕ × ℕ × ℕ) × ProgP × ℕ) (_ : ℕ) : (ℕ × ℕ × ℕ) × ProgP × ℕ :=
  (st.1, oneCopyP (2 * st.2.2) (ampP st.1.1 st.1.2.1 st.1.2.2 (2 * st.2.2)) st.2.1
      (ampP st.1.1 st.1.2.1 st.1.2.2 (4 * st.2.2)), 2 * st.2.2)

theorem encP_foldl (E : ℕ × ℕ × ℕ) (ell : ℕ) :
    (List.range ell).foldl encStep (E, baseP E.1 E.2.2, 16 * E.1) =
      (E, encP E ell, mwP E.1 ell) := by
  induction ell with
  | zero => simp [encP, mwP]
  | succ ell ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, encStep, encP, mwP, Prod.mk.injEq, true_and]
    ring

abbrev TSt : Ty := .prod TE (.prod TProg .nat)

/-- Context `[w2, ((E, prog, w), _)]`. -/
def encStepBody (L : Lib) (A : AmpIx) (I : PcIx) (ione : ℕ) : Tm [.prod TSt .nat] TSt :=
  .letE (.bit .ff (.snd (.snd (.fst v0))))
    (.pair (.fst (.fst v1)) (.pair
      (.app (oneCopyF L I ione) (.pair v0 (.pair (.app (ampF L A) (.pair (.fst (.fst v1)) v0))
        (.pair (.fst (.snd (.fst v1))) (.app (ampF L A) (.pair (.fst (.fst v1)) (.bit .ff v0)))))))
      v0))

def encStepF (L : Lib) (A : AmpIx) (I : PcIx) (ione i : ℕ) : FnSig (.prod TSt .nat) TSt :=
  exactSig i (encStepBody L A I ione) (fun x => encStep x.1 x.2)

theorem encStep_valid {L : Lib} (hL : L.OK P) {A : AmpIx} (hA : A.OK P L) {I : PcIx}
    (hI : I.OK P L) {ione i : ℕ} (hone : P[ione]? = some (oneCopyBody L I).compile)
    (hP : P[i]? = some (encStepBody L A I ione).compile) :
    ∀ x : (Ty.prod TSt .nat).den, 4 ≤ x.1.1.1 → (encStepF L A I ione i).ValidAt P x :=
  exactSig_valid hP _
    (fun x hx => by
      obtain ⟨⟨⟨D, K, code⟩, prog, w⟩, j⟩ := x
      have ha : ∀ T, (ampF L A).ValidAt P ((D, K, code), T) := fun T => amp_valid hL hA _ hx
      simp [tm_simp, encStepBody, ha, oneCopy_valid hL hI hone])
    (fun x _ => by
      obtain ⟨⟨⟨D, K, code⟩, prog, (w : ℕ)⟩, j⟩ := x
      have h4 : 2 * (2 * w) = 4 * w := by ring
      simp [tm_simp, encStepBody, encStep, ampF, oneCopyF, h4])

/-- Indices of the encoder family. -/
structure EncIx where
  base : BaseIx
  amp : AmpIx
  pc : PcIx
  one : ℕ
  step : ℕ
  fold : ℕ
  enc : ℕ
  prog : ℕ

abbrev EncIx.stepF (L : Lib) (I : EncIx) : FnSig (.prod TSt .nat) TSt :=
  encStepF L I.amp I.pc I.one I.step

/-- Context `[r, (E, ell)]`. -/
def encBody (L : Lib) (I : EncIx) : Tm [.prod TE .nat] TProg :=
  .letE (.app (foldlF (I.stepF L) I.fold) (.pair
      (.pair (.fst v0) (.pair (.app (baseF L I.base) (.pair (.fst (.fst v0)) (.snd (.snd (.fst v0)))))
        (.app (mulF L.mul) (.pair (.lit (16 : ℕ)) (.fst (.fst v0))))))
      (.app (rangeF L.range) (.snd v0))))
    (.fst (.snd v0))

def encF (L : Lib) (I : EncIx) : FnSig (.prod TE .nat) TProg :=
  exactSig I.enc (encBody L I) (fun x => encP x.1 x.2)

/-- **The encoder oracle** `prog : ell ↦ encP E (ell + 1)` (constants `E` as a literal). -/
def progBody (L : Lib) (I : EncIx) (E : ℕ × ℕ × ℕ) : Tm [.nat] TProg :=
  .app (encF L I) (.pair (.lit E) (.app (succF L.succ) v0))

def progF (L : Lib) (I : EncIx) (E : ℕ × ℕ × ℕ) : FnSig .nat TProg :=
  exactSig I.prog (progBody L I E) (fun ell => encP E (ell + 1))

structure EncIx.OK (P : Program) (L : Lib) (I : EncIx) (E : ℕ × ℕ × ℕ) : Prop where
  base : I.base.OK P L
  amp : I.amp.OK P L
  pc : I.pc.OK P L
  one : P[I.one]? = some (oneCopyBody L I.pc).compile
  step : P[I.step]? = some (encStepBody L I.amp I.pc I.one).compile
  fold : P[I.fold]? = some (foldlBody (I.stepF L) I.fold).compile
  enc : P[I.enc]? = some (encBody L I).compile
  prog : P[I.prog]? = some (progBody L I E).compile

theorem enc_valid {L : Lib} (hL : L.OK P) {I : EncIx} {E : ℕ × ℕ × ℕ} (hI : I.OK P L E) :
    ∀ x : (Ty.prod TE .nat).den, 4 ≤ x.1.1 → (encF L I).ValidAt P x :=
  exactSig_valid hI.enc _
    (fun x hx => by
      obtain ⟨⟨(D : ℕ), K, code⟩, (ell : ℕ)⟩ := x
      have hx' : 4 ≤ D := hx
      have hok := foldlOK_of_inv (P := P) (I.stepF L) (fun st => 4 ≤ st.1.1) (List.range ell)
        ((D, K, code), baseP D code, 16 * D) hx'
        (fun _ _ acc h => by simpa [EncIx.stepF, encStepF, encStep] using h)
        (fun _ _ acc h => encStep_valid hL hI.amp hI.pc hI.one hI.step _ h)
      have hb := base_valid hL hI.base (D, code) hx'
      have hbd : (baseF L I.base).den (D, code) = baseP D code := rfl
      simp [tm_simp, encBody, hL.mul, hL.range, hb, hbd,
        foldl_valid hI.fold (((D, K, code), baseP D code, 16 * D), List.range ell) hok])
    (fun x _ => by
      obtain ⟨⟨D, K, code⟩, ell⟩ := x
      have h := encP_foldl (D, K, code) ell
      simp only [encBody, tm_simp, foldlF_den, foldlDen, rangeF_den, mulF_den, baseF, exactSig_den,
        EncIx.stepF, encStepF, Env.one]
      rw [show (fun acc x => encStep (acc : (ℕ × ℕ × ℕ) × ProgP × ℕ) (x : ℕ)) = encStep from rfl,
        h])

/-- **Validity of the encoder oracle** (all arguments, `4 ≤ D`). -/
theorem prog_valid {L : Lib} (hL : L.OK P) {I : EncIx} {E : ℕ × ℕ × ℕ} (hI : I.OK P L E)
    (hE : 4 ≤ E.1) : ∀ ell, (progF L I E).ValidAt P ell := fun ell =>
  exactSig_valid hI.prog (fun _ => True)
    (fun ell _ => by
      simp [tm_simp, progBody, hL.succ, enc_valid hL hI (E, ell + 1) hE])
    (fun ell _ => by simp [tm_simp, progBody, encF]) ell trivial

end QecReliability.Trans.HashCallees
