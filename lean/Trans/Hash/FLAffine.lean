import Trans.Hash.FLList

/-!
# Trans.Hash.FLAffine: local affine hashing in FL

* `abit` as a `foldr` over `ipairs cs x0` (`abit_foldr`), `abitStepF`, `abitF`;
* `affP` as a `foldr` over `ipairs rows i` (`affP_foldr`), `affStepF`, `affF`;
* `seedRows` as a map over `range L` (`seedRows_map`), `rowF`, `seedRowsF`.
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

/-! ## Folds valid everywhere -/

theorem foldr_validAll {a b : Ty} {F : FnSig (.prod a b) b} {i : ℕ}
    (hF : ∀ x, F.ValidAt P x) (hP : P[i]? = some (foldrBody F i).compile) :
    ∀ p, (foldrF F i).ValidAt P p := fun p =>
  foldr_valid hP p (foldrOK_of_inv F (fun _ => True) p.1 p.2 trivial (fun _ _ _ _ => trivial)
    (fun x' _ acc _ => hF (x', acc)))

theorem foldl_validAll {a b : Ty} {F : FnSig (.prod b a) b} {i : ℕ}
    (hF : ∀ x, F.ValidAt P x) (hP : P[i]? = some (foldlBody F i).compile) :
    ∀ p, (foldlF F i).ValidAt P p := fun p =>
  foldl_valid hP p (foldlOK_of_inv F (fun _ => True) p.2 p.1 trivial (fun _ _ _ _ => trivial)
    (fun x _ acc _ => hF (acc, x)))

theorem mapEnv_validAll {e a b : Ty} {F : FnSig (.prod e a) b} {i : ℕ}
    (hF : ∀ x, F.ValidAt P x) (hP : P[i]? = some (mapEnvBody F i).compile) :
    ∀ p, (mapEnvF F i).ValidAt P p := fun p => mapEnv_valid hP p (fun x _ => hF _)

/-! ## `abit` -/

abbrev TAb : Ty := .prod .nat (.prod (.list TGate) .nat)

def abitStep (p : Bool × ℕ) (s : ℕ × List GateP × ℕ) : ℕ × List GateP × ℕ :=
  if p.1 then (s.1, s.2.1 ++ [(false, true, p.2, s.2.2)], s.1 + s.2.1.length) else s

theorem abit_foldr (v : ℕ) (cs : List Bool) (b : Bool) (x0 : ℕ) :
    (ipairs cs x0).foldr abitStep (v, [constGate b], v) =
      (v, (abit v cs b x0).1, (abit v cs b x0).2) := by
  induction cs generalizing x0 with
  | nil => rfl
  | cons c cs ih =>
    simp only [ipairs, List.foldr_cons, ih, abitStep, abit]
    cases c <;> simp

def abitStepBody (iapp iadd ilen : ℕ) : Tm [.prod (.prod .bool .nat) TAb] TAb :=
  .ite (.fst (.fst v0))
    (.pair (.fst (.snd v0))
      (.pair (.app (appendF TGate iapp) (.pair (.fst (.snd (.snd v0)))
          (.lcons (.pair .ff (.pair .tt (.pair (.snd (.fst v0)) (.snd (.snd (.snd v0)))))) .lnil)))
        (.app (addF iadd) (.pair (.fst (.snd v0))
          (.app (lengthF TGate ilen) (.fst (.snd (.snd v0))))))))
    (.snd v0)

def abitStepF (iapp iadd ilen i : ℕ) : FnSig (.prod (.prod .bool .nat) TAb) TAb :=
  exactSig i (abitStepBody iapp iadd ilen) (fun x => abitStep x.1 x.2)

theorem abitStep_valid {iapp iadd ilen i : ℕ} (happ : ∀ x, (appendF TGate iapp).ValidAt P x)
    (hadd : ∀ x, (addF iadd).ValidAt P x) (hlen : ∀ x, (lengthF TGate ilen).ValidAt P x)
    (hP : P[i]? = some (abitStepBody iapp iadd ilen).compile) :
    ∀ x, (abitStepF iapp iadd ilen i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      obtain ⟨⟨c, _⟩, _⟩ := x
      cases c <;> simp [tm_simp, abitStepBody, happ, hadd, hlen])
    (fun x _ => by
      obtain ⟨⟨c, _⟩, _⟩ := x
      cases c <;> simp [tm_simp, abitStepBody, abitStep]) x trivial

/-- `abit` on `(v, cs, b, x0)`; `ifold = foldrF (abitStepF …) _`. -/
def abitBody (iip : ℕ) (ifold : FnSig (.prod (.list (.prod .bool .nat)) TAb) TAb) :
    Tm [.prod .nat (.prod (.list .bool) (.prod .bool .nat))] (.prod (.list TGate) .nat) :=
  .letE (.app ifold (.pair (.app (ipairsF .bool iip) (.pair (.fst (.snd v0))
      (.snd (.snd (.snd v0)))))
    (.pair (.fst v0) (.pair (.lcons (.pair .tt (.pair .tt
        (.pair (.ite (.fst (.snd (.snd v0))) (.lit (1 : ℕ)) .zero) .zero))) .lnil) (.fst v0)))))
    (.pair (.fst (.snd v0)) (.snd (.snd v0)))

def abitF (iip : ℕ) (ifold : FnSig (.prod (.list (.prod .bool .nat)) TAb) TAb) (i : ℕ) :
    FnSig (.prod .nat (.prod (.list .bool) (.prod .bool .nat))) (.prod (.list TGate) .nat) :=
  exactSig i (abitBody iip ifold) (fun x => abit x.1 x.2.1 x.2.2.1 x.2.2.2)

theorem abit_valid {isucc iip iapp iadd ilen ist ifo i : ℕ}
    (hs : ∀ n, (succF isucc).ValidAt P n)
    (hip : P[iip]? = some (ipairsBody .bool isucc iip).compile)
    (happ : ∀ x, (appendF TGate iapp).ValidAt P x)
    (hadd : ∀ x, (addF iadd).ValidAt P x) (hlen : ∀ x, (lengthF TGate ilen).ValidAt P x)
    (hst : P[ist]? = some (abitStepBody iapp iadd ilen).compile)
    (hfo : P[ifo]? = some (foldrBody (abitStepF iapp iadd ilen ist) ifo).compile)
    (hP : P[i]? = some (abitBody iip (foldrF (abitStepF iapp iadd ilen ist) ifo)).compile) :
    ∀ x, (abitF iip (foldrF (abitStepF iapp iadd ilen ist) ifo) i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      simp [tm_simp, abitBody, ipairs_valid hs hip,
        foldr_validAll (abitStep_valid happ hadd hlen hst) hfo])
    (fun x _ => by
      obtain ⟨v, cs, b, x0⟩ := x
      have h := abit_foldr v cs b x0
      cases b <;>
      · simp only [abitBody, tm_simp, foldrF_den, ipairsF_den, foldrDen, abitStepF, exactSig_den]
        simp only [constGate, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [show (fun x acc => abitStep (x : Bool × ℕ) acc) = abitStep from rfl, h]) x trivial

/-! ## `affP` -/

abbrev TAf : Ty := .prod .nat (.prod .nat TProg)

def affStep (p : (List Bool × Bool) × ℕ) (s : ℕ × ℕ × ProgP) : ℕ × ℕ × ProgP :=
  (s.1, s.2.1,
    ((abit s.1 p.1.1 p.1.2 (s.2.1 * p.2)).1 ++
        tabGates (List.range s.1, s.1, s.1 + (abit s.1 p.1.1 p.1.2 (s.2.1 * p.2)).1.length) s.2.2.1,
      (abit s.1 p.1.1 p.1.2 (s.2.1 * p.2)).2 ::
        tabWires (List.range s.1, s.1, s.1 + (abit s.1 p.1.1 p.1.2 (s.2.1 * p.2)).1.length)
          s.2.2.2))

theorem affP_foldr (v t i0 : ℕ) (rows : List (List Bool × Bool)) :
    (ipairs rows i0).foldr affStep (v, t, ([], [])) = (v, t, affP v t i0 rows) := by
  induction rows generalizing i0 with
  | nil => rfl
  | cons r rs ih =>
    simp only [ipairs, List.foldr_cons, ih, affStep, affP]

def affStepBody (iabit : FnSig (.prod .nat (.prod (.list .bool) (.prod .bool .nat)))
    (.prod (.list TGate) .nat)) (imul irange iadd ilen iapp : ℕ)
    (itg : FnSig (.prod TTab (.list TGate)) (.list TGate))
    (itw : FnSig (.prod TTab (.list .nat)) (.list .nat)) :
    Tm [.prod (.prod TRow .nat) TAf] TAf :=
  .letE (.app iabit (.pair (.fst (.snd v0)) (.pair (.fst (.fst (.fst v0)))
      (.pair (.snd (.fst (.fst v0))) (.app (mulF imul) (.pair (.fst (.snd (.snd v0)))
        (.snd (.fst v0))))))))
    (.letE (.pair (.app (rangeF irange) (.fst (.snd v1))) (.pair (.fst (.snd v1))
        (.app (addF iadd) (.pair (.fst (.snd v1)) (.app (lengthF TGate ilen) (.fst v0))))))
      (.pair (.fst (.snd v2)) (.pair (.fst (.snd (.snd v2)))
        (.pair (.app (appendF TGate iapp) (.pair (.fst v1)
            (.app itg (.pair v0 (.fst (.snd (.snd (.snd v2))))))))
          (.lcons (.snd v1) (.app itw (.pair v0 (.snd (.snd (.snd (.snd v2)))))))))))

def affStepF (iabit : FnSig (.prod .nat (.prod (.list .bool) (.prod .bool .nat)))
    (.prod (.list TGate) .nat)) (imul irange iadd ilen iapp : ℕ)
    (itg : FnSig (.prod TTab (.list TGate)) (.list TGate))
    (itw : FnSig (.prod TTab (.list .nat)) (.list .nat)) (i : ℕ) :
    FnSig (.prod (.prod TRow .nat) TAf) TAf :=
  exactSig i (affStepBody iabit imul irange iadd ilen iapp itg itw) (fun x => affStep x.1 x.2)

theorem affStep_valid {iabit : FnSig (.prod .nat (.prod (.list .bool) (.prod .bool .nat)))
    (.prod (.list TGate) .nat)} {imul irange iadd ilen iapp i : ℕ}
    {itg : FnSig (.prod TTab (.list TGate)) (.list TGate)}
    {itw : FnSig (.prod TTab (.list .nat)) (.list .nat)}
    (habit : ∀ x, iabit.ValidAt P x) (habitd : ∀ x, iabit.den x = abit x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hmul : ∀ x, (mulF imul).ValidAt P x) (hrange : ∀ x, (rangeF irange).ValidAt P x)
    (hadd : ∀ x, (addF iadd).ValidAt P x) (hlen : ∀ x, (lengthF TGate ilen).ValidAt P x)
    (happ : ∀ x, (appendF TGate iapp).ValidAt P x)
    (htg : ∀ x, itg.ValidAt P x) (htw : ∀ x, itw.ValidAt P x)
    (htgd : ∀ x, itg.den x = tabGates x.1 x.2) (htwd : ∀ x, itw.den x = tabWires x.1 x.2)
    (hP : P[i]? = some (affStepBody iabit imul irange iadd ilen iapp itg itw).compile) :
    ∀ x, (affStepF iabit imul irange iadd ilen iapp itg itw i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by
      simp [tm_simp, affStepBody, habit, hmul, hrange, hadd, hlen, happ, htg, htw])
    (fun x _ => by
      simp [tm_simp, affStepBody, affStep, habitd, htgd, htwd, Nat.mul_comm]) x trivial

/-- `affP v t i rows` on `(v, t, i, rows)`; `ifold = foldrF (affStepF …) _`. -/
def affBody (iip : ℕ) (ifold : FnSig (.prod (.list (.prod TRow .nat)) TAf) TAf) :
    Tm [.prod .nat (.prod .nat (.prod .nat (.list TRow)))] TProg :=
  .snd (.snd (.app ifold (.pair (.app (ipairsF TRow iip) (.pair (.snd (.snd (.snd v0)))
      (.fst (.snd (.snd v0)))))
    (.pair (.fst v0) (.pair (.fst (.snd v0)) (.pair .lnil .lnil))))))

def affF (iip : ℕ) (ifold : FnSig (.prod (.list (.prod TRow .nat)) TAf) TAf) (i : ℕ) :
    FnSig (.prod .nat (.prod .nat (.prod .nat (.list TRow)))) TProg :=
  exactSig i (affBody iip ifold) (fun x => affP x.1 x.2.1 x.2.2.1 x.2.2.2)

theorem aff_valid {isucc iip i : ℕ} {F : FnSig (.prod (.prod TRow .nat) TAf) TAf} {ifo : ℕ}
    (hs : ∀ n, (succF isucc).ValidAt P n)
    (hip : P[iip]? = some (ipairsBody TRow isucc iip).compile)
    (hF : ∀ x, F.ValidAt P x) (hFd : ∀ x, F.den x = affStep x.1 x.2)
    (hfo : P[ifo]? = some (foldrBody F ifo).compile)
    (hP : P[i]? = some (affBody iip (foldrF F ifo)).compile) :
    ∀ x, (affF iip (foldrF F ifo) i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      simp [tm_simp, affBody, ipairs_valid hs hip, foldr_validAll hF hfo])
    (fun x _ => by
      obtain ⟨v, t, i0, rows⟩ := x
      have h := affP_foldr v t i0 rows
      simp only [affBody, tm_simp, foldrF_den, ipairsF_den, foldrDen, hFd]
      rw [show (fun x acc => affStep (x : (List Bool × Bool) × ℕ) acc) = affStep from rfl, h])
    x trivial

/-! ## Seed rows -/

theorem seedRows_map (t L : ℕ) (bs : List Bool) :
    seedRows t L bs = (List.range L).map (fun l =>
      ((bs.drop ((t + 1) * l)).take t, bs.getD ((t + 1) * l + t) false)) := by
  induction L generalizing bs with
  | zero => rfl
  | succ L ih =>
    rw [seedRows, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, List.drop_zero, Nat.zero_add,
      List.cons.injEq, true_and]
    apply List.map_congr_left
    intro l _
    simp only [Function.comp_apply, List.drop_drop, List.getD_eq_getElem?_getD,
      List.getElem?_drop, Prod.mk.injEq]
    constructor
    · congr 2; simp only [Nat.succ_eq_add_one]; ring
    · congr 2; simp only [Nat.succ_eq_add_one]; ring

/-- One row: `((t, bs), l) ↦ (take t (drop ((t+1) l) bs), bs[(t+1) l + t])`. -/
def rowBody (isucc imul idrop itake igd iadd : ℕ) : Tm [.prod (.prod .nat (.list .bool)) .nat] TRow :=
  .letE (.app (mulF imul) (.pair (.app (succF isucc) (.fst (.fst v0))) (.snd v0)))
    (.pair (.app (takeF .bool itake) (.pair (.fst (.fst v1))
        (.app (dropF .bool idrop) (.pair v0 (.snd (.fst v1))))))
      (.app (getDF .bool igd) (.pair (.snd (.fst v1))
        (.pair (.app (addF iadd) (.pair v0 (.fst (.fst v1)))) .ff))))

def rowF (isucc imul idrop itake igd iadd i : ℕ) :
    FnSig (.prod (.prod .nat (.list .bool)) .nat) TRow :=
  exactSig i (rowBody isucc imul idrop itake igd iadd)
    (fun x => ((x.1.2.drop ((x.1.1 + 1) * x.2)).take x.1.1, x.1.2.getD ((x.1.1 + 1) * x.2 + x.1.1) false))

theorem row_valid {isucc imul idrop itake igd iadd i : ℕ}
    (hs : ∀ x, (succF isucc).ValidAt P x) (hmul : ∀ x, (mulF imul).ValidAt P x)
    (hdrop : ∀ x, (dropF .bool idrop).ValidAt P x) (htake : ∀ x, (takeF .bool itake).ValidAt P x)
    (hgd : ∀ x, (getDF .bool igd).ValidAt P x) (hadd : ∀ x, (addF iadd).ValidAt P x)
    (hP : P[i]? = some (rowBody isucc imul idrop itake igd iadd).compile) :
    ∀ x, (rowF isucc imul idrop itake igd iadd i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, rowBody, hs, hmul, hdrop, htake, hgd, hadd])
    (fun x _ => by simp [tm_simp, rowBody]) x trivial

/-- `seedRows t L bs` on `(t, L, bs)`; `imap = mapEnvF (rowF …) _`. -/
def seedRowsBody (irange : ℕ) (imap : FnSig (.prod (.prod .nat (.list .bool)) (.list .nat))
    (.list TRow)) : Tm [.prod .nat (.prod .nat (.list .bool))] (.list TRow) :=
  .app imap (.pair (.pair (.fst v0) (.snd (.snd v0))) (.app (rangeF irange) (.fst (.snd v0))))

def seedRowsF (irange : ℕ) (imap : FnSig (.prod (.prod .nat (.list .bool)) (.list .nat))
    (.list TRow)) (i : ℕ) : FnSig (.prod .nat (.prod .nat (.list .bool))) (.list TRow) :=
  exactSig i (seedRowsBody irange imap) (fun x => seedRows x.1 x.2.1 x.2.2)

theorem seedRows_valid {irange : ℕ} {F : FnSig (.prod (.prod .nat (.list .bool)) .nat) TRow}
    {im i : ℕ} (hrange : ∀ x, (rangeF irange).ValidAt P x) (hF : ∀ x, F.ValidAt P x)
    (hFd : ∀ x, F.den x = ((x.1.2.drop ((x.1.1 + 1) * x.2)).take x.1.1,
      x.1.2.getD ((x.1.1 + 1) * x.2 + x.1.1) false))
    (hm : P[im]? = some (mapEnvBody F im).compile)
    (hP : P[i]? = some (seedRowsBody irange (mapEnvF F im)).compile) :
    ∀ x, (seedRowsF irange (mapEnvF F im) i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by
      simp only [seedRowsBody, tm_simp, true_and]
      exact ⟨hrange _, mapEnv_validAll hF hm _⟩)
    (fun x _ => by simp [tm_simp, seedRowsBody, hFd, seedRows_map]) x trivial

end QecReliability.Trans.Hash
