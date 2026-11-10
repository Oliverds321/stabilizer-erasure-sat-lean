import Trans.HashCallees.EncoderCorr

/-!
# Trans.HashCallees.EncoderFLBase: bit lookup and the base program in FL

* `testBitF` (`(a, p) ↦ a.testBit p`, recursion on `p`, closed-form bounds);
* `baseGateF` (gate `g` of the base emitter, environment `(code, k, h, n)`), `baseOutF`;
* `baseF`: `(D, code) ↦ baseP D code` (valid for `4 ≤ D`).
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

/-! ## Bit lookup -/

@[simps] def testBitF (_L : Lib) (i : ℕ) : FnSig (.prod .nat .nat) .bool where
  idx := i
  den x := x.1.testBit x.2
  cost x := (x.2 + 1) * (25 * x.2.size + 60)
  depth x := x.2 + x.2.size + 3
  msize x := 4 * x.1.size + 4 * x.2.size + 20

def testBitBody (L : Lib) (i : ℕ) : Tm [.prod .nat .nat] .bool :=
  .ite (.isZero (.snd v0)) (.app (oddF L.odd) (.fst v0))
    (.app (testBitF L i) (.pair (.app (div2F L.div2) (.fst v0)) (.app (predF L.pred) (.snd v0))))

theorem testBit_valid {L : Lib} (hL : L.OK P) {i : ℕ}
    (hP : P[i]? = some (testBitBody L i).compile) : ∀ x, (testBitF L i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun (x : (Ty.prod .nat .nat).den) => x.2) ?_
  rintro ⟨(a : ℕ), (p : ℕ)⟩ ih
  by_cases hp : p = 0
  · subst hp
    constructor <;> tm_auto [testBitBody, hL.odd, Nat.testBit_zero]
  · have hih := ih (a / 2, p - 1) (by simp only; omega)
    have hs := size_mono (Nat.sub_le p 1)
    have ha := size_half_le a
    have hden : a.testBit p = (a / 2).testBit (p - 1) := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp [Nat.testBit_div_two]
    constructor
    · tm_auto [testBitBody, hL.div2, hL.pred, hih, hp]
    · tm_auto [testBitBody, hL.div2, hL.pred, hih, hp, hden]
    · have hm := Nat.mul_le_mul_left p (show 25 * (p - 1).size + 60 ≤ 25 * p.size + 60 by omega)
      have hp1 : p - 1 + 1 = p := by omega
      tm_unfold [testBitBody, hL.div2, hL.pred, hih, hp]
      rw [hp1]
      nlinarith
    · tm_auto [testBitBody, hL.div2, hL.pred, hih, hp]
    · tm_auto [testBitBody, hL.div2, hL.pred, hih, hp]

/-! ## Base gates -/

/-- Environment of the base emitter: `(code, k, h, n)`. -/
abbrev TBEnv : Ty := .prod .nat (.prod .nat (.prod .nat .nat))

/-- Context `[ab, qr, x]`, `qr = (g / k, g % k)`, `ab = (g / k / h, g / k % h)`. -/
def baseGateBody (L : Lib) (itb : ℕ) : Tm [.prod TBEnv .nat] TGate :=
  .letE (.app L.dmF (.pair (.snd v0) (.fst (.snd (.fst v0)))))
  (.letE (.app L.dmF (.pair (.fst v0) (.fst (.snd (.snd (.fst v1))))))
    (.pair .ff (.pair .tt (.pair
      (.ite (.isZero (.snd v1)) (.snd (.snd (.snd (.fst v2))))
        (.app (addF L.add) (.pair (.snd (.snd (.snd (.fst v2)))) (.snd v2))))
      (.ite (.app (testBitF L itb) (.pair (.fst (.fst v2))
          (.app (addF L.add) (.pair (.app (mulF L.mul) (.pair (.snd v0) (.fst (.snd (.fst v2)))))
            (.snd v1)))))
        (.app (addF L.add) (.pair (.snd v1) (.app (mulF L.mul) (.pair (.fst (.snd (.fst v2)))
          (.fst v0)))))
        (.snd (.snd (.snd (.fst v2)))))))))

def baseGateF (L : Lib) (itb i : ℕ) : FnSig (.prod TBEnv .nat) TGate :=
  exactSig i (baseGateBody L itb)
    (fun x => gateP x.1.2.2.2 x.1.2.1 (baseRef x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2) x.2)

theorem baseGate_valid {L : Lib} (hL : L.OK P) {itb i : ℕ}
    (htb : P[itb]? = some (testBitBody L itb).compile)
    (hP : P[i]? = some (baseGateBody L itb).compile) :
    ∀ x : (Ty.prod TBEnv .nat).den, 0 < x.1.2.1 ∧ 0 < x.1.2.2.1 →
      (baseGateF L itb i).ValidAt P x :=
  exactSig_valid hP _
    (fun x hx => by
      obtain ⟨⟨code, k, h, n⟩, g⟩ := x
      obtain ⟨hk, hh⟩ := hx
      simp only at hk hh
      simp [tm_simp, baseGateBody, hL.add, hL.mul, hL.dm' _ hk, hL.dm' _ hh,
        testBit_valid hL htb])
    (fun x _ => by
      obtain ⟨⟨code, k, h, n⟩, g⟩ := x
      simp only [baseGateBody, tm_simp, Lib.dmF_den, addF_den, mulF_den, testBitF_den, gateP,
        baseRef, coeffP, exactSig_den, Env.one, den_isZero]
      by_cases h0 : g % k = 0 <;> simp [h0, Nat.mul_comm])

def baseOutBody (L : Lib) : Tm [.prod (.prod .nat .nat) .nat] .nat :=
  .app (addF L.add) (.pair (.fst (.fst v0))
    (.app (mulF L.mul) (.pair (.app (succF L.succ) (.snd v0)) (.snd (.fst v0)))))

def baseOutF (L : Lib) (i : ℕ) : FnSig (.prod (.prod .nat .nat) .nat) .nat :=
  exactSig i (baseOutBody L) (fun x => x.1.1 + (x.2 + 1) * x.1.2)

theorem baseOut_valid {L : Lib} (hL : L.OK P) {i : ℕ}
    (hP : P[i]? = some (baseOutBody L).compile) : ∀ x, (baseOutF L i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, baseOutBody, hL.add, hL.mul, hL.succ])
    (fun x _ => by simp [tm_simp, baseOutBody]) x trivial

/-! ## The base program -/

/-- Indices of the base program's functions. -/
structure BaseIx where
  tb : ℕ
  gate : ℕ
  gmap : ℕ
  out : ℕ
  omap : ℕ
  base : ℕ

/-- Context `[n, h, k, (D, code)]`. -/
def baseBody (L : Lib) (I : BaseIx) : Tm [.prod .nat .nat] TProg :=
  .letE (.app (addF L.add) (.pair (.fst v0) (.fst v0)))
  (.letE (.app (div2F L.div2) (.app (div2F L.div2) (.fst v1)))
  (.letE (.app (mulF L.mul) (.pair (.lit (8 : ℕ)) v1))
    (.pair
      (.lcons (.lit (constGate false))
        (.app (mapEnvF (baseGateF L I.tb I.gate) I.gmap)
          (.pair (.pair (.snd v3) (.pair v2 (.pair v1 v0)))
            (.app (rangeF L.range) (.app (mulF L.mul)
              (.pair (.app (mulF L.mul) (.pair (.lit (8 : ℕ)) v1)) v2))))))
      (.app (appendF .nat L.app) (.pair
        (.app (appendF .nat L.app) (.pair (.app (rangeF L.range) v0)
          (.app (mapEnvF (baseOutF L I.out) I.omap) (.pair (.pair v0 v2)
            (.app (rangeF L.range) (.app (mulF L.mul) (.pair (.lit (8 : ℕ)) v1)))))))
        (.app (replicateF .nat L.rep) (.pair (.app (mulF L.mul) (.pair (.lit (46 : ℕ)) (.fst v3)))
          v0)))))))

def baseF (L : Lib) (I : BaseIx) : FnSig (.prod .nat .nat) TProg :=
  exactSig I.base (baseBody L I) (fun x => baseP x.1 x.2)

/-- The base program's bodies are installed. -/
structure BaseIx.OK (P : Program) (L : Lib) (I : BaseIx) : Prop where
  tb : P[I.tb]? = some (testBitBody L I.tb).compile
  gate : P[I.gate]? = some (baseGateBody L I.tb).compile
  gmap : P[I.gmap]? = some (mapEnvBody (baseGateF L I.tb I.gate) I.gmap).compile
  out : P[I.out]? = some (baseOutBody L).compile
  omap : P[I.omap]? = some (mapEnvBody (baseOutF L I.out) I.omap).compile
  base : P[I.base]? = some (baseBody L I).compile

theorem base_valid {L : Lib} (hL : L.OK P) {I : BaseIx} (hI : I.OK P L) :
    ∀ x : ℕ × ℕ, 4 ≤ x.1 → (baseF L I).ValidAt P x :=
  exactSig_valid hI.base _
    (fun x hx => by
      obtain ⟨(D : ℕ), (code : ℕ)⟩ := x
      simp only at hx
      have hg : ∀ p : (Ty.prod TBEnv (.list .nat)).den, 0 < p.1.2.1 ∧ 0 < p.1.2.2.1 →
          (mapEnvF (baseGateF L I.tb I.gate) I.gmap).ValidAt P p := fun p hp =>
        mapEnv_valid hI.gmap p (fun y _ => baseGate_valid hL hI.tb hI.gate _ hp)
      have ho := mapEnv_validAll (baseOut_valid hL hI.out) hI.omap
      have h4 : 0 < D / 2 / 2 := by omega
      have hg' := hg ((code, D + D, D / 2 / 2, 8 * (D + D)),
        List.range (8 * (D / 2 / 2) * (D + D))) ⟨show 0 < D + D by omega, h4⟩
      simp [tm_simp, baseBody, hL.add, hL.mul, hL.div2, hL.range, hL.app, hL.rep, ho, hg'])
    (fun x _ => by
      obtain ⟨D, code⟩ := x
      simp only [baseBody, tm_simp, addF_den, div2F_den, mulF_den, mapEnvF_den, rangeF_den,
        appendF_den, replicateF_den, baseGateF, baseOutF, exactSig_den, Env.one, baseP, emitP,
        Nat.div_div_eq_div_mul]
      try simp [List.append_assoc])

end QecReliability.Trans.HashCallees
