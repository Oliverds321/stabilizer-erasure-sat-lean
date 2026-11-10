import Trans.Hash.FLWalk

/-!
# Trans.Hash.FLScalar: the scalar parameters of the walk code in FL

* `dyadicUp`/`dyadicValue` as a `foldl` scan (`dy_foldl`), `dyStepF`;
* `ceilSquare` as a `foldl` scan (`cs_foldl`), `csStepF`;
* `16 ^ k` as a `foldl` (`pow_foldl`), `powStepF`;
* `paramsF`: `(base, den, q) ↦ params base den q` (as a 9-tuple).
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

/-! ## Scans -/

/-- Dyadic scan state `(target, done, e, base * 2^e)`. -/
def dyStep (st : ℕ × Bool × ℕ × ℕ) (_ : ℕ) : ℕ × Bool × ℕ × ℕ :=
  if st.2.1 then st else if st.1 ≤ st.2.2.2 then (st.1, true, st.2.2.1, st.2.2.2)
  else (st.1, false, st.2.2.1 + 1, 2 * st.2.2.2)

theorem dy_done (T e p : ℕ) (xs : List ℕ) : xs.foldl dyStep (T, true, e, p) = (T, true, e, p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [dyStep] using ih

theorem dy_foldl (base T : ℕ) (xs : List ℕ) : ∀ e, ∃ b,
    xs.foldl dyStep (T, false, e, base * 2 ^ e) =
      (T, b, UniformAdapter.firstHit (fun e => T ≤ base * 2 ^ e) xs.length e,
        base * 2 ^ UniformAdapter.firstHit (fun e => T ≤ base * 2 ^ e) xs.length e) := by
  induction xs with
  | nil => intro e; exact ⟨false, rfl⟩
  | cons x xs ih =>
    intro e
    by_cases h : T ≤ base * 2 ^ e
    · refine ⟨true, ?_⟩
      simp only [List.foldl_cons, dyStep, Bool.false_eq_true, ↓reduceIte, h, dy_done,
        List.length_cons, UniformAdapter.firstHit]
    · obtain ⟨b, hb⟩ := ih (e + 1)
      refine ⟨b, ?_⟩
      simp only [List.foldl_cons, dyStep, Bool.false_eq_true, ↓reduceIte, h,
        List.length_cons, UniformAdapter.firstHit]
      rw [show 2 * (base * 2 ^ e) = base * 2 ^ (e + 1) by ring, hb]

theorem dyadicUp_foldl (base T : ℕ) :
    ((List.range T).foldl dyStep (T, false, 0, base)).2.2 =
      (UniformAdapter.dyadicUp base T, UniformAdapter.dyadicValue base T) := by
  obtain ⟨b, h⟩ := dy_foldl base T (List.range T) 0
  simp only [pow_zero, Nat.mul_one] at h
  rw [h, List.length_range]
  rfl

theorem dy_fst (base T : ℕ) :
    ((List.range T).foldl dyStep (T, false, 0, base)).2.2.1 = UniformAdapter.dyadicUp base T := by
  rw [dyadicUp_foldl]

theorem dy_snd (base T : ℕ) :
    ((List.range T).foldl dyStep (T, false, 0, base)).2.2.2 =
      base * 2 ^ UniformAdapter.dyadicUp base T := by
  rw [dyadicUp_foldl]; rfl

def dyStepBody (ile isucc imul : ℕ) : Tm [.prod (.prod .nat (.prod .bool (.prod .nat .nat))) .nat]
    (.prod .nat (.prod .bool (.prod .nat .nat))) :=
  .ite (.fst (.snd (.fst v0))) (.fst v0)
    (.ite (.app (leF ile) (.pair (.fst (.fst v0)) (.snd (.snd (.snd (.fst v0))))))
      (.pair (.fst (.fst v0)) (.pair .tt (.snd (.snd (.fst v0)))))
      (.pair (.fst (.fst v0)) (.pair .ff (.pair (.app (succF isucc) (.fst (.snd (.snd (.fst v0)))))
        (.app (mulF imul) (.pair (.lit (2 : ℕ)) (.snd (.snd (.snd (.fst v0))))))))))

def dyStepF (ile isucc imul i : ℕ) : FnSig (.prod (.prod .nat (.prod .bool (.prod .nat .nat))) .nat)
    (.prod .nat (.prod .bool (.prod .nat .nat))) :=
  exactSig i (dyStepBody ile isucc imul) (fun x => dyStep x.1 x.2)

theorem dyStep_valid {ile isucc imul i : ℕ} (hle : ∀ x, (leF ile).ValidAt P x)
    (hs : ∀ x, (succF isucc).ValidAt P x) (hmul : ∀ x, (mulF imul).ValidAt P x)
    (hP : P[i]? = some (dyStepBody ile isucc imul).compile) :
    ∀ x, (dyStepF ile isucc imul i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      obtain ⟨⟨T, d, e, p⟩, j⟩ := x
      cases d <;> simp [tm_simp, dyStepBody, hle, hs, hmul])
    (fun x _ => by
      obtain ⟨⟨T, d, e, p⟩, j⟩ := x
      cases d <;> simp [tm_simp, dyStepBody, dyStep] <;> split_ifs <;> simp) x trivial

/-- Square scan state `(N, done, s)`. -/
def csStep (st : ℕ × Bool × ℕ) (_ : ℕ) : ℕ × Bool × ℕ :=
  if st.2.1 then st else if st.1 ≤ st.2.2 * st.2.2 then (st.1, true, st.2.2)
  else (st.1, false, st.2.2 + 1)

theorem cs_done (N s : ℕ) (xs : List ℕ) : xs.foldl csStep (N, true, s) = (N, true, s) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [csStep] using ih

theorem cs_foldl (N : ℕ) (xs : List ℕ) : ∀ s, ∃ b,
    xs.foldl csStep (N, false, s) =
      (N, b, UniformAdapter.firstHit (fun s => N ≤ s * s) xs.length s) := by
  induction xs with
  | nil => intro s; exact ⟨false, rfl⟩
  | cons x xs ih =>
    intro s
    by_cases h : N ≤ s * s
    · exact ⟨true, by simp [csStep, h, cs_done, UniformAdapter.firstHit]⟩
    · obtain ⟨b, hb⟩ := ih (s + 1)
      exact ⟨b, by simp only [List.foldl_cons, csStep, Bool.false_eq_true, ↓reduceIte, h,
        List.length_cons, UniformAdapter.firstHit, hb]⟩

theorem ceilSquare_foldl (N : ℕ) :
    ((List.range N).foldl csStep (N, false, 1)).2.2 = UniformAdapter.ceilSquare N := by
  obtain ⟨b, h⟩ := cs_foldl N (List.range N) 1
  rw [h, List.length_range]
  rfl

def csStepBody (ile isucc imul : ℕ) : Tm [.prod (.prod .nat (.prod .bool .nat)) .nat]
    (.prod .nat (.prod .bool .nat)) :=
  .ite (.fst (.snd (.fst v0))) (.fst v0)
    (.ite (.app (leF ile) (.pair (.fst (.fst v0))
        (.app (mulF imul) (.pair (.snd (.snd (.fst v0))) (.snd (.snd (.fst v0)))))))
      (.pair (.fst (.fst v0)) (.pair .tt (.snd (.snd (.fst v0)))))
      (.pair (.fst (.fst v0)) (.pair .ff (.app (succF isucc) (.snd (.snd (.fst v0)))))))

def csStepF (ile isucc imul i : ℕ) : FnSig (.prod (.prod .nat (.prod .bool .nat)) .nat)
    (.prod .nat (.prod .bool .nat)) :=
  exactSig i (csStepBody ile isucc imul) (fun x => csStep x.1 x.2)

theorem csStep_valid {ile isucc imul i : ℕ} (hle : ∀ x, (leF ile).ValidAt P x)
    (hs : ∀ x, (succF isucc).ValidAt P x) (hmul : ∀ x, (mulF imul).ValidAt P x)
    (hP : P[i]? = some (csStepBody ile isucc imul).compile) :
    ∀ x, (csStepF ile isucc imul i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      obtain ⟨⟨N, d, s⟩, j⟩ := x
      cases d <;> simp [tm_simp, csStepBody, hle, hs, hmul])
    (fun x _ => by
      obtain ⟨⟨N, d, s⟩, j⟩ := x
      cases d <;> simp [tm_simp, csStepBody, csStep] <;> split_ifs <;> simp) x trivial

/-! ## Powers -/

def powStep (st : ℕ × ℕ) (_ : ℕ) : ℕ × ℕ := (st.1, st.1 * st.2)

theorem pow_foldl (b : ℕ) (xs : List ℕ) : ∀ p, xs.foldl powStep (b, p) = (b, b ^ xs.length * p) := by
  induction xs with
  | nil => intro p; simp
  | cons x xs ih => intro p; simp only [List.foldl_cons, powStep, ih, List.length_cons]; ring_nf

theorem pow16 (n : ℕ) : ((List.range n).foldl powStep (16, 1)).2 = 16 ^ n := by
  rw [pow_foldl]; simp

def powStepBody (imul : ℕ) : Tm [.prod (.prod .nat .nat) .nat] (.prod .nat .nat) :=
  .pair (.fst (.fst v0)) (.app (mulF imul) (.pair (.fst (.fst v0)) (.snd (.fst v0))))

def powStepF (imul i : ℕ) : FnSig (.prod (.prod .nat .nat) .nat) (.prod .nat .nat) :=
  exactSig i (powStepBody imul) (fun x => powStep x.1 x.2)

theorem powStep_valid {imul i : ℕ} (hmul : ∀ x, (mulF imul).ValidAt P x)
    (hP : P[i]? = some (powStepBody imul).compile) : ∀ x, (powStepF imul i).ValidAt P x :=
  fun x => exactSig_valid hP (fun _ => True) (fun _ _ => by simp [tm_simp, powStepBody, hmul])
    (fun x _ => by simp [tm_simp, powStepBody, powStep]) x trivial

/-! ## Parameters -/

abbrev TParams : Ty :=
  .prod .nat (.prod .nat (.prod .nat (.prod .nat (.prod .nat (.prod .nat (.prod .nat
    (.prod .nat .nat)))))))

def Params.tuple (p : Params) : TParams.den := (p.e1, p.N1, p.s, p.m, p.k, p.D, p.M, p.e2, p.L)

/-- `params base den q` on `(base, den, q)`. -/
def paramsBody (irange imul : ℕ)
    (idy : FnSig (.prod (.prod .nat (.prod .bool (.prod .nat .nat))) (.list .nat))
      (.prod .nat (.prod .bool (.prod .nat .nat))))
    (ics : FnSig (.prod (.prod .nat (.prod .bool .nat)) (.list .nat)) (.prod .nat (.prod .bool .nat)))
    (ipw : FnSig (.prod (.prod .nat .nat) (.list .nat)) (.prod .nat .nat)) :
    Tm [.prod .nat (.prod .nat .nat)] TParams :=
  -- v0 = (base, den, q)
  .letE (.app (mulF imul) (.pair (.lit (4 : ℕ)) (.snd (.snd v0))))                      -- 4q
    (.letE (.snd (.snd (.app idy (.pair (.pair v0 (.pair .ff (.pair .zero (.fst v1))))
        (.app (rangeF irange) v0)))))                                                    -- (e1, N1)
      (.letE (.snd (.snd (.app ics (.pair (.pair (.snd v0) (.pair .ff (.lit (1 : ℕ))))
          (.app (rangeF irange) (.snd v0))))))                                           -- s
        (.letE (.app (mulF imul) (.pair (.lit (256 : ℕ)) (.app (mulF imul)
            (.pair (.fst (.snd v3)) (.fst (.snd v3))))))                                 -- k
          (.letE (.snd (.app ipw (.pair (.pair (.lit (16 : ℕ)) (.lit (1 : ℕ)))
              (.app (rangeF irange) v0))))                                               -- D
            (.letE (.app (mulF imul) (.pair (.app (mulF imul) (.pair v2 v2)) v0))       -- M
              (.letE (.snd (.snd (.app idy (.pair (.pair v0 (.pair .ff (.pair .zero (.fst v6))))
                  (.app (rangeF irange) v0)))))                                          -- (e2, L)
                (.pair (.fst v5) (.pair (.snd v5) (.pair v4 (.pair (.app (mulF imul) (.pair v4 v4))
                  (.pair v3 (.pair v2 (.pair v1 (.pair (.fst v0) (.snd v0)))))))))))))))

def paramsF (irange imul : ℕ)
    (idy : FnSig (.prod (.prod .nat (.prod .bool (.prod .nat .nat))) (.list .nat))
      (.prod .nat (.prod .bool (.prod .nat .nat))))
    (ics : FnSig (.prod (.prod .nat (.prod .bool .nat)) (.list .nat)) (.prod .nat (.prod .bool .nat)))
    (ipw : FnSig (.prod (.prod .nat .nat) (.list .nat)) (.prod .nat .nat)) (i : ℕ) :
    FnSig (.prod .nat (.prod .nat .nat)) TParams :=
  exactSig i (paramsBody irange imul idy ics ipw) (fun x => (params x.1 x.2.1 x.2.2).tuple)

theorem params_valid {irange imul i : ℕ}
    {Fdy : FnSig (.prod (.prod .nat (.prod .bool (.prod .nat .nat))) .nat)
      (.prod .nat (.prod .bool (.prod .nat .nat)))}
    {Fcs : FnSig (.prod (.prod .nat (.prod .bool .nat)) .nat) (.prod .nat (.prod .bool .nat))}
    {Fpw : FnSig (.prod (.prod .nat .nat) .nat) (.prod .nat .nat)} {idy ics ipw : ℕ}
    (hrange : ∀ x, (rangeF irange).ValidAt P x) (hmul : ∀ x, (mulF imul).ValidAt P x)
    (hdy : ∀ x, Fdy.ValidAt P x) (hdyd : ∀ x, Fdy.den x = dyStep x.1 x.2)
    (hcs : ∀ x, Fcs.ValidAt P x) (hcsd : ∀ x, Fcs.den x = csStep x.1 x.2)
    (hpw : ∀ x, Fpw.ValidAt P x) (hpwd : ∀ x, Fpw.den x = powStep x.1 x.2)
    (hidy : P[idy]? = some (foldlBody Fdy idy).compile)
    (hics : P[ics]? = some (foldlBody Fcs ics).compile)
    (hipw : P[ipw]? = some (foldlBody Fpw ipw).compile)
    (hP : P[i]? = some (paramsBody irange imul (foldlF Fdy idy) (foldlF Fcs ics)
      (foldlF Fpw ipw)).compile) :
    ∀ x, (paramsF irange imul (foldlF Fdy idy) (foldlF Fcs ics) (foldlF Fpw ipw) i).ValidAt P x :=
  fun x => exactSig_valid hP (fun _ => True)
    (fun _ _ => by
      simp [tm_simp, paramsBody, hrange, hmul, foldl_validAll hdy hidy, foldl_validAll hcs hics,
        foldl_validAll hpw hipw])
    (fun x _ => by
      obtain ⟨base, den, q⟩ := x
      have e1 : (fun acc x => dyStep acc (x : ℕ)) = dyStep := rfl
      have e2 : (fun acc x => csStep acc (x : ℕ)) = csStep := rfl
      have e3 : (fun acc x => powStep acc (x : ℕ)) = powStep := rfl
      simp only [paramsBody, Tm.den, Env.get, Env.one, mulF_den, rangeF_den, foldlF_den, foldlDen,
        hdyd, hcsd, hpwd, e1, e2, e3, dy_fst, dy_snd, ceilSquare_foldl, pow16]
      simp only [params, Params.tuple, UniformAdapter.walkClock, UniformAdapter.dyadicValue]
      ring_nf) x trivial

end QecReliability.Trans.Hash
