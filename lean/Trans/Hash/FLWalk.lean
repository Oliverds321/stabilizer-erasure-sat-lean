import Trans.Hash.FLTrans

/-!
# Trans.Hash.FLWalk: walk symbols in FL

* `divModF`: `(a, b) ↦ (a / b, a % b)` for `b > 0` (binary long division, closed-form bounds);
* `pvisits` (degree 16) as a `foldl` (`pvisits_foldl`), `visStepF` (calls the neighbor
  oracle `inb : (s, v, i) ↦ nb s v i`);
* `encIdxF` (`encIndex (nb s) 16 D M t`), the encoder index list via `mapEnvF`.
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

/-! ## Division with remainder -/

theorem divmod_step (a b : ℕ) (hb : 0 < b) (ha : a ≠ 0) :
    (if b ≤ 2 * (a / 2 % b) + a % 2 then (2 * (a / 2 / b) + 1, 2 * (a / 2 % b) + a % 2 - b)
      else (2 * (a / 2 / b), 2 * (a / 2 % b) + a % 2)) = (a / b, a % b) := by
  have e1 := Nat.div_add_mod a 2
  have e2 := Nat.div_add_mod (a / 2) b
  have hlt := Nat.mod_lt (a / 2) hb
  have h2 := Nat.mod_lt a (show 0 < 2 by omega)
  split_ifs with h
  · have := (Nat.div_mod_unique (a := a) (d := 2 * (a / 2 / b) + 1)
      (c := 2 * (a / 2 % b) + a % 2 - b) hb).mpr ⟨by
        have : b * (2 * (a / 2 / b) + 1) = 2 * (b * (a / 2 / b)) + b := by ring
        omega, by omega⟩
    rw [this.1, this.2]
  · have := (Nat.div_mod_unique (a := a) (d := 2 * (a / 2 / b))
      (c := 2 * (a / 2 % b) + a % 2) hb).mpr ⟨by
        have : b * (2 * (a / 2 / b)) = 2 * (b * (a / 2 / b)) := by ring
        omega, by omega⟩
    rw [this.1, this.2]

@[simps] def divModF (ile isub i : ℕ) : FnSig (.prod .nat .nat) (.prod .nat .nat) where
  idx := i
  den x := (x.1 / x.2, x.1 % x.2)
  cost x := 300 * (x.1.size + 1) * (x.2.size + 2)
  depth x := x.1.size + 2 * x.2.size + 10
  msize x := 8 * (x.1.size + x.2.size) + 40

def divModBody (ile isub i : ℕ) : Tm [.prod .nat .nat] (.prod .nat .nat) :=
  .ncase (.fst v0) (.pair .zero .zero)
    (.letE (.app (divModF ile isub i) (.pair v1 (.snd v2)))
      (.letE (.bit v1 (.snd v0))
        (.ite (.app (leF ile) (.pair (.snd v4) v0))
          (.pair (.bit .tt (.fst v1)) (.app (subF isub) (.pair v0 (.snd v4))))
          (.pair (.bit .ff (.fst v1)) v0))))

theorem divMod_valid {ile isub i : ℕ} (hle : ∀ x, (leF ile).ValidAt P x)
    (hsub : ∀ x, (subF isub).ValidAt P x) (hP : P[i]? = some (divModBody ile isub i).compile) :
    ∀ x : ℕ × ℕ, 0 < x.2 → (divModF ile isub i).ValidAt P x := by
  refine FnSig.valid_of_body' _ _ hP (fun (x : (Ty.prod .nat .nat).den) => x.1) _ ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩ hb ih
  simp only at hb
  by_cases ha : a = 0
  · subst ha
    constructor <;> tm_auto [divModBody]
  have hih := ih (a / 2, b) (by simp only; omega) hb
  have hs := size_half ha
  have hst := divmod_step a b hb ha
  have hr : 2 * (a / 2 % b) + a % 2 < 2 * b := by
    have := Nat.mod_lt (a / 2) hb; have := Nat.mod_lt a (show 0 < 2 by omega); omega
  have hrs : (2 * (a / 2 % b) + a % 2).size ≤ b.size + 1 := by
    have := size_mono (show 2 * (a / 2 % b) + a % 2 ≤ 2 * b by omega)
    have := size_double_le b; omega
  have hq := size_mono (Nat.div_le_self (a / 2) b)
  have hq2 := size_half_le a
  have hm := size_mono (Nat.mod_le (a / 2) b)
  have hm2 := size_mono (show a / 2 % b ≤ b by have := Nat.mod_lt (a / 2) hb; omega)
  have hbn : bitNat (decide (a % 2 = 1)) (a / 2 % b) = 2 * (a / 2 % b) + a % 2 := by
    unfold bitNat; split_ifs with h <;> simp at h <;> omega
  have key : 300 * (a.size + 1) * (b.size + 2) =
      300 * ((a / 2).size + 1) * (b.size + 2) + 300 * (b.size + 2) := by rw [← hs]; ring
  constructor
  · tm_lean [divModBody, hih, hle, hsub, if_neg ha]
  · simp only [divModBody, Tm.den, Env.get, divModF_den, leF_den, subF_den, if_neg ha, hbn,
      bitNat_true, bitNat_false, Env.one]
    rw [← hst]
    split_ifs <;> simp_all
  · tm_lean [divModBody, hih, hle, hsub, if_neg ha, divModF_cost, leF_cost, subF_cost,
      divModF_den, leF_den, hbn]
    all_goals nlinarith [key, hrs]
  · tm_lean [divModBody, hih, hle, hsub, if_neg ha, divModF_depth, leF_depth, subF_depth,
      divModF_den, leF_den, hbn]
  · have hp1 := size_bitNat_le true (a / 2 / b)
    have hp0 := size_bitNat_le false (a / 2 / b)
    have hsr := size_sub_le (2 * (a / 2 % b) + a % 2) b
    tm_auto [divModBody, hih, hle, hsub, hbn]

/-! ## Visits (degree 16) -/

theorem pvisits_snoc (nb : ℕ → ℕ → ℕ) (h : ℕ) :
    ∀ v w, pvisits nb 16 v w (h + 1) = nb (pvisits nb 16 v w h) (w / 16 ^ h % 16) := by
  induction h with
  | zero => intro v w; simp [pvisits]
  | succ h ih =>
    intro v w
    rw [pvisits, ih, pvisits, Nat.div_div_eq_div_mul, ← pow_succ']

theorem pvisits_foldl (nb : ℕ → ℕ → ℕ → ℕ) (s : ℕ) (h : ℕ) :
    ∀ v w, ((List.range h).foldl (fun st (_ : ℕ) => (st.1, nb st.1 st.2.1 (st.2.2 % 16), st.2.2 / 16))
      (s, v, w)) = (s, pvisits (nb s) 16 v w h, w / 16 ^ h) := by
  induction h with
  | zero => intro v w; simp [pvisits]
  | succ h ih =>
    intro v w
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Prod.mk.injEq, true_and]
    refine ⟨(pvisits_snoc (nb s) h v w).symm, ?_⟩
    rw [Nat.div_div_eq_div_mul, ← pow_succ]

def visStepBody (inb : FnSig (.prod .nat (.prod .nat .nat)) .nat)
    (idm : FnSig (.prod .nat .nat) (.prod .nat .nat)) :
    Tm [.prod (.prod .nat (.prod .nat .nat)) .nat] (.prod .nat (.prod .nat .nat)) :=
  .letE (.app idm (.pair (.snd (.snd (.fst v0))) (.lit (16 : ℕ))))
    (.pair (.fst (.fst v1)) (.pair
      (.app inb (.pair (.fst (.fst v1)) (.pair (.fst (.snd (.fst v1))) (.snd v0))))
      (.fst v0)))

def visStepF (inb : FnSig (.prod .nat (.prod .nat .nat)) .nat)
    (idm : FnSig (.prod .nat .nat) (.prod .nat .nat)) (i : ℕ) :
    FnSig (.prod (.prod .nat (.prod .nat .nat)) .nat) (.prod .nat (.prod .nat .nat)) :=
  exactSig i (visStepBody inb idm)
    (fun x => (x.1.1, inb.den (x.1.1, x.1.2.1, x.1.2.2 % 16), x.1.2.2 / 16))

theorem visStep_valid {inb : FnSig (.prod .nat (.prod .nat .nat)) .nat}
    {idm : FnSig (.prod .nat .nat) (.prod .nat .nat)} {i : ℕ}
    (hnb : ∀ x, inb.ValidAt P x) (hdm : ∀ w, idm.ValidAt P (w, 16))
    (hdmd : ∀ x, idm.den x = (x.1 / x.2, x.1 % x.2))
    (hP : P[i]? = some (visStepBody inb idm).compile) :
    ∀ x, (visStepF inb idm i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True) (fun _ _ => by simp [tm_simp, visStepBody, hnb, hdm])
    (fun x _ => by simp [tm_simp, visStepBody, hdmd]) x trivial

/-! ## Encoder index -/

/-- `encIndex (nb s) 16 D M t x` on `((s, D, M, t), x)`; `idm = divModF …`,
`ivis = foldlF (visStepF …) _`. -/
def encIdxBody (idm : FnSig (.prod .nat .nat) (.prod .nat .nat)) (imul iadd irange : ℕ)
    (ivis : FnSig (.prod (.prod .nat (.prod .nat .nat)) (.list .nat)) (.prod .nat (.prod .nat .nat))) :
    Tm [.prod (.prod .nat (.prod .nat (.prod .nat .nat))) .nat] .nat :=
  .letE (.app idm (.pair (.snd v0) (.snd (.snd (.snd (.fst v0))))))      -- (x / t, x % t)
    (.letE (.app idm (.pair (.fst v0) (.fst (.snd (.snd (.fst v1))))))   -- (_, x / t % M)
      (.letE (.app (addF iadd) (.pair (.snd v1) (.app (mulF imul)
          (.pair (.snd (.snd (.snd (.fst v2)))) (.snd v0)))))           -- y
        (.letE (.app idm (.pair v0 (.snd (.snd (.snd (.fst v3)))))) -- (y / t, y % t)
          (.letE (.app idm (.pair (.fst v0) (.fst (.snd (.fst v4)))))  -- (y/t/D, y/t%D)
            (.fst (.snd (.app ivis (.pair (.pair (.fst (.fst v5)) (.pair (.fst v0) (.snd v0)))
              (.app (rangeF irange) (.snd v1))))))))))

def encIdxF (idm : FnSig (.prod .nat .nat) (.prod .nat .nat)) (imul iadd irange : ℕ)
    (ivis : FnSig (.prod (.prod .nat (.prod .nat .nat)) (.list .nat)) (.prod .nat (.prod .nat .nat)))
    (nb : ℕ → ℕ → ℕ → ℕ) (i : ℕ) :
    FnSig (.prod (.prod .nat (.prod .nat (.prod .nat .nat))) .nat) .nat :=
  exactSig i (encIdxBody idm imul iadd irange ivis)
    (fun x => encIndex (nb x.1.1) 16 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2)

theorem encIdx_valid {ile isub imul iadd irange i : ℕ} {idm : ℕ}
    {inb : FnSig (.prod .nat (.prod .nat .nat)) .nat} {nb : ℕ → ℕ → ℕ → ℕ} {ivs ifo : ℕ}
    (hle : ∀ x, (leF ile).ValidAt P x) (hsub : ∀ x, (subF isub).ValidAt P x)
    (hdm : P[idm]? = some (divModBody ile isub idm).compile)
    (hmul : ∀ x, (mulF imul).ValidAt P x) (hadd : ∀ x, (addF iadd).ValidAt P x)
    (hrange : ∀ x, (rangeF irange).ValidAt P x)
    (hnb : ∀ x, inb.ValidAt P x) (hnbd : ∀ x, inb.den x = nb x.1 x.2.1 x.2.2)
    (hvs : P[ivs]? = some (visStepBody inb (divModF ile isub idm)).compile)
    (hfo : P[ifo]? = some (foldlBody (visStepF inb (divModF ile isub idm) ivs) ifo).compile)
    (hP : P[i]? = some (encIdxBody (divModF ile isub idm) imul iadd irange
      (foldlF (visStepF inb (divModF ile isub idm) ivs) ifo)).compile) :
    ∀ x : (Ty.prod (.prod .nat (.prod .nat (.prod .nat .nat))) .nat).den,
      0 < x.1.2.1 ∧ 0 < x.1.2.2.1 ∧ 0 < x.1.2.2.2 →
      (encIdxF (divModF ile isub idm) imul iadd irange
        (foldlF (visStepF inb (divModF ile isub idm) ivs) ifo) nb i).ValidAt P x := by
  have hdmv := divMod_valid hle hsub hdm
  have hvis := foldl_validAll (visStep_valid hnb (fun w => hdmv (w, 16) (by simp))
    (fun _ => rfl) hvs) hfo
  refine exactSig_valid hP _ ?_ ?_
  · rintro ⟨⟨s, D, M, t⟩, x⟩ ⟨hD, hM, ht⟩
    simp only at hD hM ht
    have hdt : ∀ y, (divModF ile isub idm).ValidAt P (y, t) := fun y => hdmv _ ht
    have hdM : ∀ y, (divModF ile isub idm).ValidAt P (y, M) := fun y => hdmv _ hM
    have hdD : ∀ y, (divModF ile isub idm).ValidAt P (y, D) := fun y => hdmv _ hD
    simp [tm_simp, encIdxBody, hdt, hdM, hdD, hmul, hadd, hrange, hvis]
  · rintro ⟨⟨s, D, M, t⟩, x⟩ ⟨hD, hM, ht⟩
    have h := pvisits_foldl nb s ((x % t + t * (x / t % M)) % t)
      ((x % t + t * (x / t % M)) / t / D) ((x % t + t * (x / t % M)) / t % D)
    simp only [encIdxBody, tm_simp, divModF_den, addF_den, mulF_den, rangeF_den, foldlF_den,
      foldlDen, visStepF, exactSig_den, hnbd, encIndex]
    rw [h]

end QecReliability.Trans.Hash
