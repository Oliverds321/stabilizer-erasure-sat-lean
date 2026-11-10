import Trans.Hash.FLBase

/-!
# Trans.Hash.FLWire: wire renaming and program combinators in FL

* `twF` (`Plain.tableWire`), `gmapF` (`gmapW (tableWire e)`), `tabGatesF`, `tabWiresF`;
* `getD0F`, `pselectF` (`pselect`), `pcomposeF` (`pcompose`);
* `padTabF` (`padTable`), `padF` (`padP`).

All are exact signatures (bounds = body bounds) or `mapEnvF` instances.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Hash
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.Trans.Query.Plain

variable {P : Program}

/-! ## `tableWire` -/

def twBody (ilt igd iadd isub : ℕ) : Tm [.prod TTab .nat] .nat :=
  .ite (.app (ltF ilt) (.pair (.snd v0) (.fst (.snd (.fst v0)))))
    (.app (getDF .nat igd) (.pair (.fst (.fst v0)) (.pair (.snd v0) .zero)))
    (.app (addF iadd) (.pair (.snd (.snd (.fst v0)))
      (.app (subF isub) (.pair (.snd v0) (.fst (.snd (.fst v0)))))))

def twF (ilt igd iadd isub i : ℕ) : FnSig (.prod TTab .nat) .nat :=
  exactSig i (twBody ilt igd iadd isub) (fun x => tableWire x.1 x.2)

theorem tw_valid {ilt igd iadd isub i : ℕ}
    (hlt : ∀ x, (ltF ilt).ValidAt P x) (hgd : ∀ x, (getDF .nat igd).ValidAt P x)
    (hadd : ∀ x, (addF iadd).ValidAt P x) (hsub : ∀ x, (subF isub).ValidAt P x)
    (hP : P[i]? = some (twBody ilt igd iadd isub).compile) :
    ∀ x, (twF ilt igd iadd isub i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, twBody, hlt, hgd, hadd, hsub])
    (fun x _ => by
      obtain ⟨⟨os, k, b⟩, w⟩ := x
      simp only [twBody, tm_simp, ltF_den, getDF_den, addF_den, subF_den, tableWire]
      split_ifs <;> simp_all) x trivial

/-! ## Gate renaming -/

def gmapBody (itw : FnSig (.prod TTab .nat) .nat) : Tm [.prod TTab TGate] TGate :=
  .ite (.fst (.snd v0))
    (.ite (.fst (.snd (.snd v0))) (.snd v0)
      (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0)))
        (.pair (.app itw (.pair (.fst v0) (.fst (.snd (.snd (.snd v0))))))
          (.snd (.snd (.snd (.snd v0))))))))
    (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0)))
      (.pair (.app itw (.pair (.fst v0) (.fst (.snd (.snd (.snd v0))))))
        (.app itw (.pair (.fst v0) (.snd (.snd (.snd (.snd v0)))))))))

def gmapF (itw : FnSig (.prod TTab .nat) .nat) (i : ℕ) : FnSig (.prod TTab TGate) TGate :=
  exactSig i (gmapBody itw) (fun x => gmapW (tableWire x.1) x.2)

theorem gmap_valid {itw : FnSig (.prod TTab .nat) .nat} {i : ℕ}
    (htw : ∀ x, itw.ValidAt P x) (htwd : ∀ x, itw.den x = tableWire x.1 x.2)
    (hP : P[i]? = some (gmapBody itw).compile) :
    ∀ x, (gmapF itw i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, gmapBody, htw])
    (fun x _ => by
      obtain ⟨e, ⟨u, s, a, b⟩⟩ := x
      simp only [gmapBody, tm_simp, gmapW, htwd]) x trivial

/-- `tabGates e gs` and `tabWires e ws`. -/
abbrev tabGatesF (itw : FnSig (.prod TTab .nat) .nat) (igm i : ℕ) :
    FnSig (.prod TTab (.list TGate)) (.list TGate) := mapEnvF (gmapF itw igm) i
abbrev tabWiresF (itw : FnSig (.prod TTab .nat) .nat) (i : ℕ) :
    FnSig (.prod TTab (.list .nat)) (.list .nat) := mapEnvF itw i

theorem tabGatesF_den (itw : FnSig (.prod TTab .nat) .nat) (igm i : ℕ) (e : List ℕ × ℕ × ℕ)
    (gs : List Query.Plain.GateP) : (tabGatesF itw igm i).den (e, gs) = tabGates e gs := rfl

theorem tabWiresF_den (itw : FnSig (.prod TTab .nat) .nat) (i : ℕ)
    (htwd : ∀ x, itw.den x = tableWire x.1 x.2) (e : List ℕ × ℕ × ℕ) (ws : List ℕ) :
    (tabWiresF itw i).den (e, ws) = tabWires e ws := by
  simp [tabWires, htwd]

/-! ## Selection -/

def getD0Body (igd : ℕ) : Tm [.prod (.list .nat) .nat] .nat :=
  .app (getDF .nat igd) (.pair (.fst v0) (.pair (.snd v0) .zero))

def getD0F (igd i : ℕ) : FnSig (.prod (.list .nat) .nat) .nat :=
  exactSig i (getD0Body igd) (fun x => x.1.getD x.2 0)

theorem getD0_valid {igd i : ℕ} (hgd : ∀ x, (getDF .nat igd).ValidAt P x)
    (hP : P[i]? = some (getD0Body igd).compile) : ∀ x, (getD0F igd i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True) (fun _ _ => by simp [tm_simp, getD0Body, hgd])
    (fun x _ => by simp [tm_simp, getD0Body]) x trivial

def pselectBody (isel : FnSig (.prod (.list .nat) (.list .nat)) (.list .nat)) :
    Tm [.prod TProg (.list .nat)] TProg :=
  .pair (.fst (.fst v0)) (.app isel (.pair (.snd (.fst v0)) (.snd v0)))

/-- `pselect P idx`; `isel = mapEnvF (getD0F igd ig) is`. -/
def pselectF (isel : FnSig (.prod (.list .nat) (.list .nat)) (.list .nat)) (i : ℕ) :
    FnSig (.prod TProg (.list .nat)) TProg :=
  exactSig i (pselectBody isel) (fun x => pselect x.1 x.2)

theorem pselect_valid {igd ig is i : ℕ} (hg : ∀ x, (getD0F igd ig).ValidAt P x)
    (hs : P[is]? = some (mapEnvBody (getD0F igd ig) is).compile)
    (hP : P[i]? = some (pselectBody (mapEnvF (getD0F igd ig) is)).compile) :
    ∀ x, (pselectF (mapEnvF (getD0F igd ig) is) i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      simp only [pselectBody, tm_simp, true_and]
      exact mapEnv_valid hs _ (fun y _ => hg _))
    (fun x _ => by simp [tm_simp, pselectBody, pselect, getD0F]) x trivial

/-! ## Composition -/

def pcomposeBody (ilen iadd iapp : ℕ) (itg : FnSig (.prod TTab (.list TGate)) (.list TGate))
    (itw : FnSig (.prod TTab (.list .nat)) (.list .nat)) :
    Tm [.prod .nat (.prod TProg TProg)] TProg :=
  .letE (.pair (.snd (.fst (.snd v0)))
      (.pair (.app (lengthF .nat ilen) (.snd (.fst (.snd v0))))
        (.app (addF iadd) (.pair (.fst v0) (.app (lengthF TGate ilen) (.fst (.fst (.snd v0))))))))
    (.pair (.app (appendF TGate iapp) (.pair (.fst (.fst (.snd v1)))
        (.app itg (.pair v0 (.fst (.snd (.snd v1)))))))
      (.app itw (.pair v0 (.snd (.snd (.snd v1))))))

def pcomposeF (ilen iadd iapp : ℕ) (itg : FnSig (.prod TTab (.list TGate)) (.list TGate))
    (itw : FnSig (.prod TTab (.list .nat)) (.list .nat)) (i : ℕ) :
    FnSig (.prod .nat (.prod TProg TProg)) TProg :=
  exactSig i (pcomposeBody ilen iadd iapp itg itw) (fun x => pcompose x.1 x.2.1 x.2.2)

theorem pcompose_valid {ilen iadd iapp i : ℕ}
    {itg : FnSig (.prod TTab (.list TGate)) (.list TGate)}
    {itw : FnSig (.prod TTab (.list .nat)) (.list .nat)}
    (hlen : ∀ (t : Ty) x, (lengthF t ilen).ValidAt P x) (hadd : ∀ x, (addF iadd).ValidAt P x)
    (happ : ∀ x, (appendF TGate iapp).ValidAt P x)
    (htg : ∀ x, itg.ValidAt P x) (htw : ∀ x, itw.ValidAt P x)
    (htgd : ∀ x, itg.den x = tabGates x.1 x.2) (htwd : ∀ x, itw.den x = tabWires x.1 x.2)
    (hP : P[i]? = some (pcomposeBody ilen iadd iapp itg itw).compile) :
    ∀ x, (pcomposeF ilen iadd iapp itg itw i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, pcomposeBody, hlen, hadd, happ, htg, htw])
    (fun x _ => by simp [tm_simp, pcomposeBody, pcompose, htgd, htwd]) x trivial

/-! ## Padding -/

theorem padTable_eq (a q : ℕ) : padTable a q = (List.range a).map (fun i => min q i) := by
  simp only [padTable]
  congr 1; funext i
  split_ifs with h <;> omega

def padBody (imt : FnSig (.prod .nat (.list .nat)) (.list .nat)) (irange isucc ilen isub irep
    iappw : ℕ) (itg : FnSig (.prod TTab (.list TGate)) (.list TGate))
    (itw : FnSig (.prod TTab (.list .nat)) (.list .nat)) :
    Tm [.prod .nat (.prod .nat (.prod .nat TProg))] TProg :=
  .letE (.pair (.app imt (.pair (.fst (.snd v0)) (.app (rangeF irange) (.fst v0))))
      (.pair (.fst v0) (.app (succF isucc) (.fst (.snd v0)))))
    (.pair (.lcons (.lit (constGate false)) (.app itg (.pair v0 (.fst (.snd (.snd (.snd v1)))))))
      (.app (appendF .nat iappw) (.pair (.app itw (.pair v0 (.snd (.snd (.snd (.snd v1))))))
        (.app (replicateF .nat irep) (.pair
          (.app (subF isub) (.pair (.fst (.snd (.snd v1)))
            (.app (lengthF .nat ilen) (.snd (.snd (.snd (.snd v1)))))))
          (.fst (.snd v1)))))))

/-- `padP a q m P` on `(a, q, m, P)`. -/
def padF (imt : FnSig (.prod .nat (.list .nat)) (.list .nat)) (irange isucc ilen isub irep
    iappw : ℕ) (itg : FnSig (.prod TTab (.list TGate)) (.list TGate))
    (itw : FnSig (.prod TTab (.list .nat)) (.list .nat)) (i : ℕ) :
    FnSig (.prod .nat (.prod .nat (.prod .nat TProg))) TProg :=
  exactSig i (padBody imt irange isucc ilen isub irep iappw itg itw)
    (fun x => padP x.1 x.2.1 x.2.2.1 x.2.2.2)

theorem pad_valid {imt : FnSig (.prod .nat (.list .nat)) (.list .nat)}
    {irange isucc ilen isub irep iappw i : ℕ}
    {itg : FnSig (.prod TTab (.list TGate)) (.list TGate)}
    {itw : FnSig (.prod TTab (.list .nat)) (.list .nat)}
    (hmt : ∀ x, imt.ValidAt P x) (hmtd : ∀ x, imt.den x = x.2.map (fun j => min x.1 j))
    (hrange : ∀ x, (rangeF irange).ValidAt P x) (hsucc : ∀ x, (succF isucc).ValidAt P x)
    (hlen : ∀ x, (lengthF .nat ilen).ValidAt P x) (hsub : ∀ x, (subF isub).ValidAt P x)
    (hrep : ∀ x, (replicateF .nat irep).ValidAt P x)
    (happw : ∀ x, (appendF .nat iappw).ValidAt P x)
    (htg : ∀ x, itg.ValidAt P x) (htw : ∀ x, itw.ValidAt P x)
    (htgd : ∀ x, itg.den x = tabGates x.1 x.2) (htwd : ∀ x, itw.den x = tabWires x.1 x.2)
    (hP : P[i]? = some (padBody imt irange isucc ilen isub irep iappw itg itw).compile) :
    ∀ x, (padF imt irange isucc ilen isub irep iappw itg itw i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, padBody, hmt, hrange, hsucc, hlen, hsub, hrep, happw, htg, htw])
    (fun x _ => by
      simp [tm_simp, padBody, padP, htgd, htwd, hmtd, padTable_eq]) x trivial

end QecReliability.Trans.Hash
