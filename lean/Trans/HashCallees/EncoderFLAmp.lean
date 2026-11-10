import Trans.HashCallees.EncoderFLBase

/-!
# Trans.HashCallees.EncoderFLAmp: the amplifiers in FL

* `pwStepF` (one step of the port-word walk, calls `lazyRotF`), `powRotF` (`powRotP` as a
  `foldl`), `portRefF` (`portRef`);
* `ampGateF` (gate `g` of the amplifier emitter, environment `(code, D, K, T, s)`), `ampOutF`;
* `ampF`: `((D, K, code), T) ↦ ampP D K code T` (valid for `4 ≤ D`), the side
  `ceilSquare (T / D)` by the `csStepF` scan of `Trans/Hash/FLScalar.lean`.
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

/-- Indices of the MGG rotation (`MGG.lean`). -/
structure RotIx where
  coord : ℕ
  rot : ℕ
  lazy : ℕ

structure RotIx.OK (P : Program) (L : Lib) (R : RotIx) : Prop where
  coord : P[R.coord]? = some (coordBody L).compile
  rot : P[R.rot]? = some (mggRotBody L R.coord).compile
  lazy : P[R.lazy]? = some (lazyRotBody L R.rot R.coord).compile

abbrev RotIx.lazyF (L : Lib) (R : RotIx) : FnSig (.prod .nat (.prod .nat .nat)) (.prod .nat .nat) :=
  lazyRotF L R.coord R.rot R.lazy

theorem RotIx.OK.lazy_valid {L : Lib} (hL : L.OK P) {R : RotIx} (hR : R.OK P L) :
    ∀ x : (Ty.prod .nat (.prod .nat .nat)).den, 0 < x.1 → (R.lazyF L).ValidAt P x :=
  lazyRot_valid hL hR.coord hR.rot hR.lazy

/-! ## The port-word walk -/

abbrev T4 : Ty := .prod .nat (.prod .nat (.prod .nat .nat))

/-- Context `[r, qr, (st, _)]`. -/
def pwStepBody (L : Lib) (R : RotIx) : Tm [.prod T4 .nat] T4 :=
  .letE (.app L.dmF (.pair (.fst (.snd (.snd (.fst v0)))) (.lit (16 : ℕ))))
  (.letE (.app (R.lazyF L) (.pair (.fst (.fst v1)) (.pair (.fst (.snd (.fst v1))) (.snd v0))))
    (.pair (.fst (.fst v2)) (.pair (.fst v0) (.pair (.fst v1)
      (.app (addF L.add) (.pair (.app (mulF L.mul) (.pair (.snd (.snd (.snd (.fst v2))))
        (.lit (16 : ℕ)))) (.snd v0)))))))

def pwStepF (L : Lib) (R : RotIx) (i : ℕ) : FnSig (.prod T4 .nat) T4 :=
  exactSig i (pwStepBody L R) (fun x => powStep x.1 x.2)

theorem pwStep_valid {L : Lib} (hL : L.OK P) {R : RotIx} (hR : R.OK P L) {i : ℕ}
    (hP : P[i]? = some (pwStepBody L R).compile) :
    ∀ x : (Ty.prod T4 .nat).den, 0 < x.1.1 → (pwStepF L R i).ValidAt P x :=
  exactSig_valid hP _
    (fun x hx => by
      obtain ⟨⟨s, v, w, acc⟩, j⟩ := x
      have h := hR.lazy_valid hL (s, v, w % 16) hx
      simp [tm_simp, pwStepBody, hL.add, hL.mul, hL.dm' _ (show 0 < 16 by omega), h])
    (fun x _ => by
      obtain ⟨⟨s, v, w, acc⟩, j⟩ := x
      simp [tm_simp, pwStepBody, powStep, lazyRotF, RotIx.lazyF])

/-- `(s, K, v, i) ↦ powRotP s K v i`. -/
def powRotBody (L : Lib) (R : RotIx) (ist ifo : ℕ) : Tm [T4] (.prod .nat .nat) :=
  .letE (.app (foldlF (pwStepF L R ist) ifo)
      (.pair (.pair (.fst v0) (.pair (.fst (.snd (.snd v0))) (.pair (.snd (.snd (.snd v0))) .zero)))
        (.app (rangeF L.range) (.fst (.snd v0)))))
    (.pair (.fst (.snd v0)) (.snd (.snd (.snd v0))))

def powRotF (L : Lib) (R : RotIx) (ist ifo i : ℕ) : FnSig T4 (.prod .nat .nat) :=
  exactSig i (powRotBody L R ist ifo) (fun x => powRotP x.1 x.2.1 x.2.2.1 x.2.2.2)

theorem powRot_valid {L : Lib} (hL : L.OK P) {R : RotIx} (hR : R.OK P L) {ist ifo i : ℕ}
    (hst : P[ist]? = some (pwStepBody L R).compile)
    (hfo : P[ifo]? = some (foldlBody (pwStepF L R ist) ifo).compile)
    (hP : P[i]? = some (powRotBody L R ist ifo).compile) :
    ∀ x : T4.den, 0 < x.1 → (powRotF L R ist ifo i).ValidAt P x :=
  exactSig_valid hP _
    (fun x hx => by
      obtain ⟨s, K, v, j⟩ := x
      have hok := foldlOK_of_inv (P := P) (pwStepF L R ist) (fun st => 0 < st.1) (List.range K)
        (s, v, j, 0) hx (fun _ _ acc h => by simpa [pwStepF, powStep] using h)
        (fun _ _ acc h => pwStep_valid hL hR hst _ h)
      simp [tm_simp, powRotBody, hL.range, foldl_valid hfo ((s, v, j, 0), List.range K) hok])
    (fun x _ => by
      obtain ⟨s, K, v, j⟩ := x
      simp only [powRotBody, tm_simp, foldlF_den, foldlDen, rangeF_den, pwStepF, exactSig_den,
        powRotP, Env.one])

/-! ## Port references -/

abbrev T6 : Ty := .prod .nat (.prod .nat (.prod .nat (.prod .nat (.prod .nat .nat))))

/-- `(D, K, T, s, v, j) ↦ portRef D K T s v j`. -/
def portRefBody (L : Lib) (iprot : FnSig T4 (.prod .nat .nat)) : Tm [T6] .nat :=
  .ite (.app (ltF L.lt) (.pair (.snd (.snd (.snd (.snd (.snd v0))))) (.fst v0)))
    (.letE (.app (addF L.add) (.pair (.snd (.snd (.snd (.snd (.snd v0)))))
        (.app (mulF L.mul) (.pair (.fst v0) (.fst (.snd (.snd (.snd (.snd v0)))))))))
      (.ite (.app (ltF L.lt) (.pair v0 (.fst (.snd (.snd v1))))) v0 (.fst (.snd (.snd v1)))))
    (.letE (.app iprot (.pair (.fst (.snd (.snd (.snd v0)))) (.pair (.fst (.snd v0))
        (.pair (.fst (.snd (.snd (.snd (.snd v0)))))
          (.app (subF L.sub) (.pair (.snd (.snd (.snd (.snd (.snd v0))))) (.fst v0)))))))
      (.letE (.app (addF L.add) (.pair (.snd v0) (.app (mulF L.mul) (.pair (.fst v1) (.fst v0)))))
        (.ite (.app (ltF L.lt) (.pair v0 (.fst (.snd (.snd v2))))) v0 (.fst (.snd (.snd v2))))))

def portRefF (L : Lib) (iprot : FnSig T4 (.prod .nat .nat)) (i : ℕ) : FnSig T6 .nat :=
  exactSig i (portRefBody L iprot)
    (fun x => portRef x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)

theorem portRef_valid {L : Lib} (hL : L.OK P) {iprot : FnSig T4 (.prod .nat .nat)} {i : ℕ}
    (hpr : ∀ x : T4.den, 0 < x.1 → iprot.ValidAt P x)
    (hprd : ∀ x : T4.den, iprot.den x = powRotP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hP : P[i]? = some (portRefBody L iprot).compile) :
    ∀ x : T6.den, 0 < x.2.2.2.1 → (portRefF L iprot i).ValidAt P x :=
  exactSig_valid hP _
    (fun x hx => by
      obtain ⟨D, K, T, s, v, j⟩ := x
      simp only at hx
      have h : ∀ y : T4.den, y.1 = s → iprot.ValidAt P y := fun y hy => hpr y (hy ▸ hx)
      simp [tm_simp, portRefBody, hL.add, hL.mul, hL.lt, hL.sub, h])
    (fun x _ => by
      obtain ⟨D, K, T, s, v, j⟩ := x
      simp only [portRefBody, tm_simp, ltF_den, addF_den, mulF_den, subF_den, hprd, portRef,
        padRef, portRefF, exactSig_den, Env.one]
      by_cases h1 : j < D <;> simp [h1])

/-! ## Amplifier gates -/

/-- Environment of the amplifier emitter: `(code, D, K, T, s)`. -/
abbrev TAEnv : Ty := .prod .nat (.prod .nat (.prod .nat (.prod .nat .nat)))

/-- Context `[ab, qr, c, (env, g)]`. -/
def ampGateBody (L : Lib) (itb : ℕ) (ipref : FnSig T6 .nat) : Tm [.prod TAEnv .nat] TGate :=
  .letE (.app (addF L.add) (.pair (.fst (.snd (.fst v0))) (.fst (.snd (.fst v0)))))
  (.letE (.app L.dmF (.pair (.snd v1) v0))
  (.letE (.app L.dmF (.pair (.fst v0)
      (.app (div2F L.div2) (.app (div2F L.div2) (.fst (.snd (.fst v2)))))))
    (.pair .ff (.pair .tt (.pair
      (.ite (.isZero (.snd v1)) (.fst (.snd (.snd (.snd (.fst v3)))))
        (.app (addF L.add) (.pair (.fst (.snd (.snd (.snd (.fst v3))))) (.snd v3))))
      (.ite (.app (testBitF L itb) (.pair (.fst (.fst v3))
          (.app (addF L.add) (.pair (.app (mulF L.mul) (.pair (.snd v0) v2)) (.snd v1)))))
        (.app ipref (.pair (.fst (.snd (.fst v3))) (.pair (.fst (.snd (.snd (.fst v3))))
          (.pair (.fst (.snd (.snd (.snd (.fst v3))))) (.pair (.snd (.snd (.snd (.snd (.fst v3)))))
            (.pair (.fst v0) (.snd v1)))))))
        (.fst (.snd (.snd (.snd (.fst v3)))))))))))

def ampGateF (L : Lib) (itb : ℕ) (ipref : FnSig T6 .nat) (i : ℕ) :
    FnSig (.prod TAEnv .nat) TGate :=
  exactSig i (ampGateBody L itb ipref)
    (fun x => gateP x.1.2.2.2.1 (x.1.2.1 + x.1.2.1)
      (ampRef x.1.2.1 x.1.2.2.1 x.1.1 x.1.2.2.2.1 x.1.2.2.2.2) x.2)

theorem ampGate_valid {L : Lib} (hL : L.OK P) {itb : ℕ} {ipref : FnSig T6 .nat} {i : ℕ}
    (htb : P[itb]? = some (testBitBody L itb).compile)
    (hpr : ∀ x : T6.den, 0 < x.2.2.2.1 → ipref.ValidAt P x)
    (hprd : ∀ x : T6.den, ipref.den x = portRef x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (hP : P[i]? = some (ampGateBody L itb ipref).compile) :
    ∀ x : (Ty.prod TAEnv .nat).den, 4 ≤ x.1.2.1 ∧ 0 < x.1.2.2.2.2 →
      (ampGateF L itb ipref i).ValidAt P x :=
  exactSig_valid hP _
    (fun x hx => by
      obtain ⟨⟨code, (D : ℕ), K, T, (s : ℕ)⟩, (g : ℕ)⟩ := x
      obtain ⟨hD, hs⟩ := hx
      have hD' : 4 ≤ D := hD
      have hs' : 0 < s := hs
      have hc : 0 < D + D := by omega
      have hh : 0 < D / 2 / 2 := by omega
      have h : ∀ y : T6.den, y.2.2.2.1 = s → ipref.ValidAt P y := fun y hy => hpr y (hy ▸ hs')
      simp [tm_simp, ampGateBody, hL.add, hL.mul, hL.div2, hL.dm' _ hc, hL.dm' _ hh,
        testBit_valid hL htb, h])
    (fun x _ => by
      obtain ⟨⟨code, D, K, T, s⟩, g⟩ := x
      simp only [ampGateBody, tm_simp, Lib.dmF_den, addF_den, mulF_den, div2F_den, testBitF_den,
        hprd, gateP, ampRef, coeffP, exactSig_den, Env.one, den_isZero, Nat.div_div_eq_div_mul]
      by_cases h0 : g % (D + D) = 0 <;> simp [h0])

def ampOutBody (L : Lib) : Tm [.prod (.prod .nat (.prod .nat .nat)) .nat] .nat :=
  .ite (.app (ltF L.lt) (.pair (.snd v0) (.fst (.snd (.fst v0)))))
    (.app (addF L.add) (.pair (.fst (.fst v0))
      (.app (mulF L.mul) (.pair (.app (succF L.succ) (.snd v0)) (.snd (.snd (.fst v0)))))))
    (.fst (.fst v0))

def ampOutF (L : Lib) (i : ℕ) : FnSig (.prod (.prod .nat (.prod .nat .nat)) .nat) .nat :=
  exactSig i (ampOutBody L)
    (fun x => if x.2 < x.1.2.1 then x.1.1 + (x.2 + 1) * x.1.2.2 else x.1.1)

theorem ampOut_valid {L : Lib} (hL : L.OK P) {i : ℕ}
    (hP : P[i]? = some (ampOutBody L).compile) : ∀ x, (ampOutF L i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, ampOutBody, hL.add, hL.mul, hL.succ, hL.lt])
    (fun x _ => by
      obtain ⟨⟨T, m, c⟩, j⟩ := x
      simp only [ampOutBody, tm_simp, ltF_den, addF_den, mulF_den, succF_den, exactSig_den,
        Env.one]
      split_ifs <;> simp_all) x trivial

/-! ## The amplifier program -/

/-- Indices of the amplifier's functions (`tb` is shared with the base program). -/
structure AmpIx where
  rot : RotIx
  tb : ℕ
  pstep : ℕ
  pfold : ℕ
  prot : ℕ
  pref : ℕ
  gate : ℕ
  gmap : ℕ
  out : ℕ
  omap : ℕ
  cs : ℕ
  csf : ℕ
  amp : ℕ

abbrev AmpIx.protF (L : Lib) (I : AmpIx) : FnSig T4 (.prod .nat .nat) :=
  powRotF L I.rot I.pstep I.pfold I.prot
abbrev AmpIx.prefF (L : Lib) (I : AmpIx) : FnSig T6 .nat := portRefF L (I.protF L) I.pref
abbrev AmpIx.gateF (L : Lib) (I : AmpIx) : FnSig (.prod TAEnv .nat) TGate :=
  ampGateF L I.tb (I.prefF L) I.gate
abbrev AmpIx.csF (L : Lib) (I : AmpIx) :
    FnSig (.prod (.prod .nat (.prod .bool .nat)) .nat) (.prod .nat (.prod .bool .nat)) :=
  csStepF L.le L.succ L.mul I.cs

abbrev TE : Ty := .prod .nat (.prod .nat .nat)

/-- Context `[c, m, s, N, ((D, K, code), T)]`. -/
def ampBody (L : Lib) (I : AmpIx) : Tm [.prod TE .nat] TProg :=
  .letE (.fst (.app L.dmF (.pair (.snd v0) (.fst (.fst v0)))))
  (.letE (.snd (.snd (.app (foldlF (I.csF L) I.csf)
      (.pair (.pair v0 (.pair .ff (.lit (1 : ℕ)))) (.app (rangeF L.range) v0)))))
  (.letE (.app (mulF L.mul) (.pair (.app (mulF L.mul) (.pair v0 v0))
      (.app (div2F L.div2) (.app (div2F L.div2) (.fst (.fst v2))))))
  (.letE (.app (addF L.add) (.pair (.fst (.fst v3)) (.fst (.fst v3))))
    (.pair
      (.lcons (.lit (constGate false))
        (.app (mapEnvF (I.gateF L) I.gmap)
          (.pair (.pair (.snd (.snd (.fst v4))) (.pair (.fst (.fst v4)) (.pair (.fst (.snd (.fst v4)))
              (.pair (.snd v4) v2))))
            (.app (rangeF L.range) (.app (mulF L.mul) (.pair v1 v0))))))
      (.app (mapEnvF (ampOutF L I.out) I.omap) (.pair (.pair (.snd v4) (.pair v1 v0))
        (.app (rangeF L.range) (.app (div2F L.div2) (.snd v4)))))))))

def ampF (L : Lib) (I : AmpIx) : FnSig (.prod TE .nat) TProg :=
  exactSig I.amp (ampBody L I) (fun x => ampP x.1.1 x.1.2.1 x.1.2.2 x.2)

structure AmpIx.OK (P : Program) (L : Lib) (I : AmpIx) : Prop where
  rot : I.rot.OK P L
  tb : P[I.tb]? = some (testBitBody L I.tb).compile
  pstep : P[I.pstep]? = some (pwStepBody L I.rot).compile
  pfold : P[I.pfold]? = some (foldlBody (pwStepF L I.rot I.pstep) I.pfold).compile
  prot : P[I.prot]? = some (powRotBody L I.rot I.pstep I.pfold).compile
  pref : P[I.pref]? = some (portRefBody L (I.protF L)).compile
  gate : P[I.gate]? = some (ampGateBody L I.tb (I.prefF L)).compile
  gmap : P[I.gmap]? = some (mapEnvBody (I.gateF L) I.gmap).compile
  out : P[I.out]? = some (ampOutBody L).compile
  omap : P[I.omap]? = some (mapEnvBody (ampOutF L I.out) I.omap).compile
  cs : P[I.cs]? = some (csStepBody L.le L.succ L.mul).compile
  csf : P[I.csf]? = some (foldlBody (I.csF L) I.csf).compile
  amp : P[I.amp]? = some (ampBody L I).compile

@[simp] theorem csStepF_den' (a b c i : ℕ) (x : (Ty.prod (.prod .nat (.prod .bool .nat)) .nat).den) :
    (csStepF a b c i).den x = csStep x.1 x.2 := rfl

theorem ceilSquare_pos (N : ℕ) : 0 < UniformAdapter.ceilSquare N :=
  Nat.lt_of_lt_of_le Nat.one_pos (firstHit_ge _ _ 1)

theorem amp_valid {L : Lib} (hL : L.OK P) {I : AmpIx} (hI : I.OK P L) :
    ∀ x : (Ty.prod TE .nat).den, 4 ≤ x.1.1 → (ampF L I).ValidAt P x :=
  exactSig_valid hI.amp _
    (fun x hx => by
      obtain ⟨⟨(D : ℕ), K, code⟩, (T : ℕ)⟩ := x
      simp only at hx
      have hprot := powRot_valid hL hI.rot hI.pstep hI.pfold hI.prot
      have hpref := portRef_valid hL hprot (fun _ => rfl) hI.pref
      have hgate := ampGate_valid hL hI.tb hpref (fun _ => rfl) hI.gate
      have hcs := csStep_valid hL.le hL.succ hL.mul hI.cs
      have hcsf := foldl_validAll hcs hI.csf
      have ho := mapEnv_validAll (ampOut_valid hL hI.out) hI.omap
      have hcsp := ceilSquare_pos (T / D)
      rw [← ceilSquare_foldl] at hcsp
      have hg := mapEnv_valid hI.gmap ((code, D, K, T,
          ((List.range (T / D)).foldl csStep (T / D, false, 1)).2.2),
        List.range (((List.range (T / D)).foldl csStep (T / D, false, 1)).2.2 *
          ((List.range (T / D)).foldl csStep (T / D, false, 1)).2.2 * (D / 2 / 2) * (D + D)))
        (fun y _ => hgate _ ⟨hx, hcsp⟩)
      have hx' : 4 ≤ D := hx
      have hD0 : 0 < D := by omega
      have hdmD : ∀ a, L.dmF.ValidAt P (a, D) := fun a => hL.dm' a hD0
      simp [tm_simp, ampBody, hL.add, hL.mul, hL.div2, hL.range, hdmD,
        hcsf, ho, foldlF_den, foldlDen, hg])
    (fun x _ => by
      obtain ⟨⟨D, K, code⟩, T⟩ := x
      have hcs := ceilSquare_foldl (T / D)
      simp only [ampBody, tm_simp, Lib.dmF_den, addF_den, mulF_den, div2F_den, mapEnvF_den,
        rangeF_den, foldlF_den, foldlDen, AmpIx.csF, csStepF_den', AmpIx.gateF, ampGateF,
        ampOutF, exactSig_den, Env.one, ampP, emitP, Nat.div_div_eq_div_mul, hcs])

end QecReliability.Trans.HashCallees
