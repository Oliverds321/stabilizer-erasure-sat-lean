import Trans.Hash.FLAffine

/-!
# Trans.Hash.FLTrans: the transpose of an XOR program in FL

* `pAddWireF` (`pAddWire`);
* `scatterP` as a `foldr` (`scatterP_foldr`), `scatStepF`;
* `revStepF` (`revStep`), `revP` as a `foldl` (`revP_foldl`);
* `transF` (`transP`).
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

abbrev TNP : Ty := .prod .nat TProg

/-! ## `pAddWire` -/

def addWireBody' (iapp : ℕ) (igd0 : FnSig (.prod (.list .nat) .nat) .nat)
    (iset : FnSig (.prod (.list .nat) (.prod .nat .nat)) (.list .nat)) (iadd ilen : ℕ) :
    Tm [.prod .nat (.prod TProg (.prod .nat .nat))] TProg :=
  .pair (.app (appendF TGate iapp) (.pair (.fst (.fst (.snd v0)))
      (.lcons (.pair .ff (.pair .tt (.pair
          (.app igd0 (.pair (.snd (.fst (.snd v0))) (.fst (.snd (.snd v0)))))
          (.snd (.snd (.snd v0)))))) .lnil)))
    (.app iset (.pair (.snd (.fst (.snd v0)))
      (.pair (.fst (.snd (.snd v0)))
        (.app (addF iadd) (.pair (.fst v0) (.app (lengthF TGate ilen) (.fst (.fst (.snd v0)))))))))

def addWireF (iapp : ℕ) (igd0 : FnSig (.prod (.list .nat) .nat) .nat)
    (iset : FnSig (.prod (.list .nat) (.prod .nat .nat)) (.list .nat)) (iadd ilen i : ℕ) :
    FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg :=
  exactSig i (addWireBody' iapp igd0 iset iadd ilen) (fun x => pAddWire x.1 x.2.1 x.2.2.1 x.2.2.2)

theorem addWire_valid {iapp iadd ilen i : ℕ} {igd0 : FnSig (.prod (.list .nat) .nat) .nat}
    {iset : FnSig (.prod (.list .nat) (.prod .nat .nat)) (.list .nat)}
    (happ : ∀ x, (appendF TGate iapp).ValidAt P x) (hgd : ∀ x, igd0.ValidAt P x)
    (hgdd : ∀ x, igd0.den x = x.1.getD x.2 0)
    (hset : ∀ x, iset.ValidAt P x) (hsetd : ∀ x, iset.den x = x.1.set x.2.1 x.2.2)
    (hadd : ∀ x, (addF iadd).ValidAt P x) (hlen : ∀ x, (lengthF TGate ilen).ValidAt P x)
    (hP : P[i]? = some (addWireBody' iapp igd0 iset iadd ilen).compile) :
    ∀ x, (addWireF iapp igd0 iset iadd ilen i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, addWireBody', happ, hgd, hset, hadd, hlen])
    (fun x _ => by simp [tm_simp, addWireBody', pAddWire, hgdd, hsetd]) x trivial

/-! ## Scatter -/

def scatStep (ts : ℕ × ℕ) (s : ℕ × ProgP) : ℕ × ProgP := (s.1, pAddWire s.1 s.2 ts.1 ts.2)

theorem scatterP_foldr (n : ℕ) (Q : ProgP) (xs : List (ℕ × ℕ)) :
    xs.foldr scatStep (n, Q) = (n, scatterP n Q xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, ih, scatStep, scatterP]

def scatStepBody (iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg) :
    Tm [.prod (.prod .nat .nat) TNP] TNP :=
  .pair (.fst (.snd v0)) (.app iaw (.pair (.fst (.snd v0)) (.pair (.snd (.snd v0)) (.fst v0))))

def scatStepF (iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg) (i : ℕ) :
    FnSig (.prod (.prod .nat .nat) TNP) TNP :=
  exactSig i (scatStepBody iaw) (fun x => scatStep x.1 x.2)

theorem scatStep_valid {iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg} {i : ℕ}
    (haw : ∀ x, iaw.ValidAt P x) (hawd : ∀ x, iaw.den x = pAddWire x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hP : P[i]? = some (scatStepBody iaw).compile) : ∀ x, (scatStepF iaw i).ValidAt P x :=
  fun x => exactSig_valid hP (fun _ => True) (fun _ _ => by simp [tm_simp, scatStepBody, haw])
    (fun x _ => by simp [tm_simp, scatStepBody, scatStep, hawd]) x trivial

/-! ## Reverse -/

def revStepBody (iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg)
    (idl : FnSig (.list .nat) (.list .nat)) (igd0 : FnSig (.prod (.list .nat) .nat) .nat)
    (ipred ilen : ℕ) : Tm [.prod TNP TGate] TNP :=
  .ite (.fst (.snd v0))
    (.pair (.fst (.fst v0)) (.pair (.fst (.snd (.fst v0))) (.app idl (.snd (.snd (.fst v0))))))
    (.letE (.app (predF ipred) (.app (lengthF .nat ilen) (.snd (.snd (.fst v0)))))
      (.letE (.app iaw (.pair (.fst (.fst v1)) (.pair (.snd (.fst v1)) (.pair
          (.fst (.snd (.snd (.snd v1))))
          (.app igd0 (.pair (.snd (.snd (.fst v1))) v0))))))
        (.letE (.app iaw (.pair (.fst (.fst v2)) (.pair v0 (.pair
            (.snd (.snd (.snd (.snd v2))))
            (.app igd0 (.pair (.snd v0) v1))))))
          (.pair (.fst (.fst v3)) (.pair (.fst v0) (.app idl (.snd v0)))))))

def revStepF (iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg)
    (idl : FnSig (.list .nat) (.list .nat)) (igd0 : FnSig (.prod (.list .nat) .nat) .nat)
    (ipred ilen i : ℕ) : FnSig (.prod TNP TGate) TNP :=
  exactSig i (revStepBody iaw idl igd0 ipred ilen) (fun x => (x.1.1, revStep x.1.1 x.1.2 x.2))

theorem revStep_valid {iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg}
    {idl : FnSig (.list .nat) (.list .nat)} {igd0 : FnSig (.prod (.list .nat) .nat) .nat}
    {ipred ilen i : ℕ}
    (haw : ∀ x, iaw.ValidAt P x) (hawd : ∀ x, iaw.den x = pAddWire x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hdl : ∀ x, idl.ValidAt P x) (hdld : ∀ x, idl.den x = x.dropLast)
    (hgd : ∀ x, igd0.ValidAt P x) (hgdd : ∀ x, igd0.den x = x.1.getD x.2 0)
    (hpred : ∀ x, (predF ipred).ValidAt P x) (hlen : ∀ x, (lengthF .nat ilen).ValidAt P x)
    (hP : P[i]? = some (revStepBody iaw idl igd0 ipred ilen).compile) :
    ∀ x, (revStepF iaw idl igd0 ipred ilen i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      obtain ⟨_, ⟨u, _⟩⟩ := x
      cases u <;> simp [tm_simp, revStepBody, haw, hdl, hgd, hpred, hlen])
    (fun x _ => by
      obtain ⟨_, ⟨u, _⟩⟩ := x
      cases u <;> simp [tm_simp, revStepBody, revStep, hawd, hdld, hgdd]) x trivial

def revFold (s : ℕ × ProgP) (g : GateP) : ℕ × ProgP := (s.1, revStep s.1 s.2 g)

theorem revP_foldl (n : ℕ) (gs : List GateP) (Q : ProgP) :
    gs.foldl revFold (n, Q) = (n, revP n gs Q) := by
  induction gs generalizing Q with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons, revFold, ih, revP]

/-! ## Transpose -/

/-- `transP k C` on `(k, C)`; `isc = foldrF (scatStepF …) _`, `irv = foldlF (revStepF …) _`. -/
def transBody (ilen iadd irep irev iip : ℕ) (isc : FnSig (.prod (.list (.prod .nat .nat)) TNP) TNP)
    (irv : FnSig (.prod TNP (.list TGate)) TNP) : Tm [.prod .nat TProg] TProg :=
  .letE (.app (lengthF .nat ilen) (.snd (.snd v0)))
    (.snd (.app irv (.pair
      (.app isc (.pair (.app (ipairsF .nat iip) (.pair (.snd (.snd v1)) .zero))
        (.pair v0 (.pair (.lcons (.lit (constGate false)) .lnil)
          (.app (replicateF .nat irep) (.pair (.app (addF iadd) (.pair (.fst v1)
            (.app (lengthF TGate ilen) (.fst (.snd v1))))) v0))))))
      (.app (reverseF TGate irev) (.fst (.snd v1))))))

def transF (ilen iadd irep irev iip : ℕ) (isc : FnSig (.prod (.list (.prod .nat .nat)) TNP) TNP)
    (irv : FnSig (.prod TNP (.list TGate)) TNP) (i : ℕ) : FnSig (.prod .nat TProg) TProg :=
  exactSig i (transBody ilen iadd irep irev iip isc irv) (fun x => transP x.1 x.2)

theorem trans_valid {ilen iadd irep irev iip isucc i : ℕ}
    {Fs : FnSig (.prod (.prod .nat .nat) TNP) TNP} {Fr : FnSig (.prod TNP TGate) TNP}
    {isc irv : ℕ}
    (hlen : ∀ (t : Ty) x, (lengthF t ilen).ValidAt P x) (hadd : ∀ x, (addF iadd).ValidAt P x)
    (hrep : ∀ x, (replicateF .nat irep).ValidAt P x)
    (hrev : ∀ x, (reverseF TGate irev).ValidAt P x)
    (hs : ∀ n, (succF isucc).ValidAt P n)
    (hip : P[iip]? = some (ipairsBody .nat isucc iip).compile)
    (hFs : ∀ x, Fs.ValidAt P x) (hFsd : ∀ x, Fs.den x = scatStep x.1 x.2)
    (hFr : ∀ x, Fr.ValidAt P x) (hFrd : ∀ x, Fr.den x = revFold x.1 x.2)
    (hsc : P[isc]? = some (foldrBody Fs isc).compile)
    (hrv : P[irv]? = some (foldlBody Fr irv).compile)
    (hP : P[i]? = some (transBody ilen iadd irep irev iip (foldrF Fs isc)
      (foldlF Fr irv)).compile) :
    ∀ x, (transF ilen iadd irep irev iip (foldrF Fs isc) (foldlF Fr irv) i).ValidAt P x :=
  fun x => exactSig_valid hP (fun _ => True)
    (fun _ _ => by
      simp [tm_simp, transBody, hlen, hadd, hrep, hrev, ipairs_valid hs hip,
        foldr_validAll hFs hsc, foldl_validAll hFr hrv])
    (fun x _ => by
      obtain ⟨k, C⟩ := x
      have h1 := scatterP_foldr C.2.length ([constGate false], List.replicate (k + C.1.length)
        C.2.length) (idxPairs C.2 0)
      have h2 := revP_foldl C.2.length C.1.reverse (scatterP C.2.length ([constGate false],
        List.replicate (k + C.1.length) C.2.length) (idxPairs C.2 0))
      rw [idxPairs_eq] at h1
      simp only [transBody, tm_simp, foldrF_den, foldlF_den, foldrDen, foldlDen, hFsd, hFrd,
        ipairsF_den, lengthF_den, addF_den, replicateF_den, reverseF_den, transP]
      rw [show (fun x acc => scatStep (x : ℕ × ℕ) acc) = scatStep from rfl, h1]
      rw [show (fun acc x => revFold acc (x : GateP)) = revFold from rfl, ← idxPairs_eq, h2])
    x trivial

end QecReliability.Trans.Hash
