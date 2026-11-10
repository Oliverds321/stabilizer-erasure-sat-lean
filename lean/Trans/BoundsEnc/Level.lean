import Trans.BoundsEnc.Amp

/-!
# Trans.BoundsEnc.Level: the level fold, `encF` and the encoder oracle `progF`

Generic in the constants `E = (D, K, code)` (walk length `K ≤ K0`), given a size bound of the
level programs `mag (encP E j) ≤ G kS cS (2^ell)` for `j ≤ ell + 1` (discharged for the concrete
constants in `Main.lean` from `HashCallees/EncoderSize.lean`):

* `encStepF_At`: one level (`oneCopyF` of two amplifiers), on walk length `≤ K0`;
* `encAcc`, `encStep_acc`: the accumulators of the level fold are `(E, encP E j, mwP D j)`;
* `encFold_At`: the level fold `foldlF encStepF` over `range (ell + 1)`, bounded by
  `G k (c + 2^ell)` in its argument's magnitude (`foldl_At` at `m = mag + 2^ell`);
* `encF_At`, `progF_At`: the same for `encF` at `(E, ell + 1)` and `progF` at `ell`;
* **`prog_bound_gen`**: `cost/depth/msize/mag(result)` of `progF L I E` at `ell` are
  `≤ G kq cq (2^ell)` — hypothesis (b) of `Trans.BoundsQH.hash_on`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.BoundsEnc
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH QecReliability.Trans.Hash QecReliability.Trans.HashCallees
open QecReliability.Trans.Query.Plain

/-! ## One level -/

theorem encStepF_At (L : HashCallees.Lib) (A : AmpIx) (I : PcIx) (ione i K0 : ℕ) :
    ∃ k c, ∀ x : (Ty.prod TSt .nat).den, x.1.1.2.1 ≤ K0 →
      FnBAt (G k c) (encStepF L A I ione i) x := by
  obtain ⟨ka, ca, ha⟩ := ampF_At L A K0
  obtain ⟨k1, c1, h1⟩ := fnBAt_P (oneCopyF_P L I ione)
  have e1 := h1 (ka + k1 + 1) (ca + c1) (by omega) (by omega)
  refine ⟨_, _, fun x hx => fnBAt_exactP (K := ka + k1) (C := ca + c1) _ _ _ x ?_ ?_⟩
  · obtain ⟨⟨⟨D, K, code⟩, prog, (w : ℕ)⟩, j⟩ := x
    have h4 : 2 * (2 * w) = 4 * w := by ring
    simp [tm_simp, encStepBody, encStep, ampF, oneCopyF, h4]
  · obtain ⟨⟨⟨D, K, code⟩, prog, (w : ℕ)⟩, j⟩ := x
    simp only at hx
    simp only [Tm.CallsBP, encStepBody, e1, true_and, and_true]
    refine ⟨?_, ?_⟩ <;> refine FnBAt.lift (ha _ ?_) (by omega) (by omega) <;>
      simpa [tm_simp] using hx

/-! ## The accumulators of the level fold -/

/-- The accumulator after `j` levels. -/
def encAcc (E : ℕ × ℕ × ℕ) (j : ℕ) : (ℕ × ℕ × ℕ) × ProgP × ℕ := (E, encP E j, mwP E.1 j)

theorem encStep_acc (E : ℕ × ℕ × ℕ) (j x : ℕ) : encStep (encAcc E j) x = encAcc E (j + 1) := by
  simp only [encStep, encAcc, encP, mwP, Prod.mk.injEq, true_and]
  ring

theorem encAcc_zero (E : ℕ × ℕ × ℕ) :
    ((E, baseP E.1 E.2.2, 16 * E.1) : (ℕ × ℕ × ℕ) × ProgP × ℕ) = encAcc E 0 := by
  simp [encAcc, encP, mwP]

theorem mag_encAcc (E : ℕ × ℕ × ℕ) (j : ℕ) :
    mag TSt (encAcc E j) = mag TE E + (mag TProg (encP E j) + mwP E.1 j + 1) + 1 := rfl

theorem mwP_le (D ell j : ℕ) (hj : j ≤ ell + 1) : mwP D j ≤ 32 * D * 2 ^ ell := by
  have h1 : 2 ^ j ≤ 2 ^ (ell + 1) := Nat.pow_le_pow_right (by omega) hj
  have h2 : 2 ^ (ell + 1) = 2 * 2 ^ ell := by rw [pow_succ]; ring
  have h3 : 16 * D * 2 ^ j ≤ 16 * D * (2 * 2 ^ ell) := Nat.mul_le_mul_left _ (h2 ▸ h1)
  have h4 : 16 * D * (2 * 2 ^ ell) = 32 * D * 2 ^ ell := by ring
  unfold mwP; omega

/-- Accumulator magnitudes from the program size bound. -/
theorem encAcc_mag (E : ℕ × ℕ × ℕ) {kS cS : ℕ}
    (hsz : ∀ ell j, j ≤ ell + 1 → mag TProg (encP E j) ≤ G kS cS (2 ^ ell)) (ell j : ℕ)
    (hj : j ≤ ell + 1) :
    mag TSt (encAcc E j) ≤ G (kS + 3) (cS + (mag TE E + 32 * E.1 + 2)) (2 ^ ell) := by
  rw [mag_encAcc]
  have h1 := hsz ell j hj
  have h2 := mwP_le E.1 ell j hj
  generalize hA : mag TE E + 32 * E.1 + 2 = A
  have h3 := lin_le A (2 ^ ell)
  have h4 : 32 * E.1 * 2 ^ ell ≤ A * (2 ^ ell + 1) := by
    have : 32 * E.1 ≤ A := by omega
    calc 32 * E.1 * 2 ^ ell ≤ A * 2 ^ ell := Nat.mul_le_mul_right _ this
      _ ≤ A * (2 ^ ell + 1) := Nat.mul_le_mul_left _ (by omega)
  have g1 : G kS cS (2 ^ ell) ≤ G (kS + 2) (cS + A) (2 ^ ell) := G_mono (by omega) (by omega) le_rfl
  have g2 : G 2 A (2 ^ ell) ≤ G (kS + 2) (cS + A) (2 ^ ell) := G_mono (by omega) (by omega) le_rfl
  have g3 := G_succ (kS + 2) (cS + A) (2 ^ ell)
  have g4 : G (kS + 2 + 1) (cS + A) (2 ^ ell) = G (kS + 3) (cS + A) (2 ^ ell) := rfl
  omega

/-! ## The level fold -/

/-- **The level fold** over `range (ell + 1)`, bounded by `G k (c + 2^ell)`. -/
theorem encFold_At (L : HashCallees.Lib) (I : EncIx) (E : ℕ × ℕ × ℕ) {K0 kS cS : ℕ}
    (hK : E.2.1 ≤ K0)
    (hsz : ∀ ell j, j ≤ ell + 1 → mag TProg (encP E j) ≤ G kS cS (2 ^ ell)) :
    ∃ k c, ∀ ell, FnBAt (G k (c + 2 ^ ell)) (foldlF (I.stepF L) I.fold)
      ((E, baseP E.1 E.2.2, 16 * E.1), List.range (ell + 1)) := by
  obtain ⟨k, c, hst⟩ := encStepF_At L I.amp I.pc I.one I.step K0
  refine ⟨k + (kS + 3) + 5, c + (cS + (mag TE E + 32 * E.1 + 2)) + 300, fun ell => ?_⟩
  have hstep : ∀ x ∈ List.range (ell + 1), ∀ n, n < (List.range (ell + 1)).length →
      ∀ acc, acc = encAcc E n → (I.stepF L).den (acc, x) = encAcc E (n + 1) := by
    intro x _ n _ acc hacc
    subst hacc
    exact encStep_acc E n x
  have hR : ∀ n, n ≤ (List.range (ell + 1)).length → ∀ acc, acc = encAcc E n →
      mag TSt acc ≤ G (kS + 3) (cS + (mag TE E + 32 * E.1 + 2))
        (mag (.prod TSt (.list .nat)) ((E, baseP E.1 E.2.2, 16 * E.1), List.range (ell + 1)) +
          2 ^ ell) := by
    intro n hn acc hacc
    subst hacc
    rw [List.length_range] at hn
    exact (encAcc_mag E hsz ell n hn).trans (G_mono le_rfl le_rfl (Nat.le_add_left _ _))
  have hF : ∀ x ∈ List.range (ell + 1), ∀ n, n < (List.range (ell + 1)).length →
      ∀ acc, acc = encAcc E n → FnBAt (G k c) (I.stepF L) (acc, x) := by
    intro x _ n _ acc hacc
    subst hacc
    exact hst (encAcc E n, x) hK
  obtain ⟨h1, h2, h3, h4⟩ := foldl_At (I.stepF L) I.fold (k := k) (c := c) (kR := kS + 3)
    (cR := cS + (mag TE E + 32 * E.1 + 2)) ((E, baseP E.1 E.2.2, 16 * E.1))
    (List.range (ell + 1))
    (mag (.prod TSt (.list .nat)) ((E, baseP E.1 E.2.2, 16 * E.1), List.range (ell + 1)) + 2 ^ ell)
    (Nat.le_add_right _ _) (fun n acc => acc = encAcc E n) (encAcc_zero E) hstep hR hF
  unfold FnBAt
  rw [← G_shift]
  exact ⟨h1, h2, h3, h4⟩

/-! ## `encF` and `progF` -/

theorem encBody_den (L : HashCallees.Lib) (I : EncIx) (x : (Ty.prod TE .nat).den) :
    (encBody L I).den (Env.one x) = encP x.1 x.2 := by
  obtain ⟨⟨D, K, code⟩, ell⟩ := x
  have h := encP_foldl (D, K, code) ell
  simp only [encBody, tm_simp, foldlF_den, foldlDen, rangeF_den, mulF_den, baseF, exactSig_den,
    EncIx.stepF, encStepF, Env.one]
  rw [show (fun acc x => encStep (acc : (ℕ × ℕ × ℕ) × ProgP × ℕ) (x : ℕ)) = encStep from rfl, h]

theorem encF_At (L : HashCallees.Lib) (I : EncIx) (E : ℕ × ℕ × ℕ) {K0 kS cS : ℕ}
    (hK : E.2.1 ≤ K0)
    (hsz : ∀ ell j, j ≤ ell + 1 → mag TProg (encP E j) ≤ G kS cS (2 ^ ell)) :
    ∃ k c, ∀ ell, FnBAt (G k (c + 2 ^ ell)) (encF L I) (E, ell + 1) := by
  obtain ⟨kf, cf, hf⟩ := encFold_At L I E hK hsz
  obtain ⟨k1, c1, hb⟩ := fnBAt_P (baseF_P L I.base)
  obtain ⟨k2, c2, hm⟩ := fnBAt_P (mulF_P (i := L.mul))
  obtain ⟨k3, c3, hr⟩ := fnBAt_P (rangeF_P (i := L.range))
  refine ⟨(Tm.nodes (encBody L I) + 1) * (kf + k1 + k2 + k3 + 1 + 1),
    cf + c1 + c2 + c3 + Tm.litc (encBody L I), fun ell => ?_⟩
  have hX := Nat.one_le_two_pow (n := ell)
  have eb := hb (kf + k1 + k2 + k3 + 1) (cf + c1 + c2 + c3 + 2 ^ ell) (by omega) (by omega)
  have em := hm (kf + k1 + k2 + k3 + 1) (cf + c1 + c2 + c3 + 2 ^ ell) (by omega) (by omega)
  have er := hr (kf + k1 + k2 + k3 + 1) (cf + c1 + c2 + c3 + 2 ^ ell) (by omega) (by omega)
  have hfold : FnBAt (G (kf + k1 + k2 + k3 + 1) (cf + c1 + c2 + c3 + 2 ^ ell))
      (foldlF (I.stepF L) I.fold) ((E, baseP E.1 E.2.2, 16 * E.1), List.range (ell + 1)) :=
    (hf ell).lift (by omega) (by omega)
  have hcalls : Tm.CallsBP (G (kf + k1 + k2 + k3 + 1) (cf + c1 + c2 + c3 + 2 ^ ell))
      (encBody L I) (Env.one (E, ell + 1)) := by
    simp only [Tm.CallsBP, encBody, eb, em, er, true_and, and_true]
    exact hfold
  have key := fnBAt_exactP I.enc (encBody L I) (fun x : (Ty.prod TE .nat).den => encP x.1 x.2)
    (E, ell + 1) (encBody_den L I _) hcalls
  exact key.lift le_rfl (by omega)

theorem progF_At (L : HashCallees.Lib) (I : EncIx) (E : ℕ × ℕ × ℕ) {K0 kS cS : ℕ}
    (hK : E.2.1 ≤ K0)
    (hsz : ∀ ell j, j ≤ ell + 1 → mag TProg (encP E j) ≤ G kS cS (2 ^ ell)) :
    ∃ k c, ∀ ell, FnBAt (G k (c + 2 ^ ell)) (progF L I E) ell := by
  obtain ⟨ke, ce, he⟩ := encF_At L I E hK hsz
  obtain ⟨k1, c1, hs⟩ := fnBAt_P (succF_P (i := L.succ))
  refine ⟨(Tm.nodes (progBody L I E) + 1) * (ke + k1 + 1 + 1),
    ce + c1 + Tm.litc (progBody L I E), fun ell => ?_⟩
  have hX := Nat.one_le_two_pow (n := ell)
  have es := hs (ke + k1 + 1) (ce + c1 + 2 ^ ell) (by omega) (by omega)
  have henc : FnBAt (G (ke + k1 + 1) (ce + c1 + 2 ^ ell)) (encF L I) (E, ell + 1) :=
    (he ell).lift (by omega) (by omega)
  have hcalls : Tm.CallsBP (G (ke + k1 + 1) (ce + c1 + 2 ^ ell)) (progBody L I E)
      (Env.one ell) := by
    simp only [Tm.CallsBP, progBody, es, true_and, and_true]
    exact henc
  have hden : (progBody L I E).den (Env.one ell) = encP E (ell + 1) := by
    simp [tm_simp, progBody, encF]
  have key := fnBAt_exactP I.prog (progBody L I E) (fun ell : ℕ => encP E (ell + 1)) ell hden
    hcalls
  exact key.lift le_rfl (by omega)

/-- **The encoder oracle bound (generic constants)**: hypothesis (b) of `hash_on`. -/
theorem prog_bound_gen (L : HashCallees.Lib) (I : EncIx) (E : ℕ × ℕ × ℕ) {K0 kS cS : ℕ}
    (hK : E.2.1 ≤ K0)
    (hsz : ∀ ell j, j ≤ ell + 1 → mag TProg (encP E j) ≤ G kS cS (2 ^ ell)) :
    ∃ kq cq, ∀ ell, (progF L I E).cost ell ≤ G kq cq (2 ^ ell) ∧
      (progF L I E).depth ell ≤ G kq cq (2 ^ ell) ∧
      (progF L I E).msize ell ≤ G kq cq (2 ^ ell) ∧
      mag TProg ((progF L I E).den ell) ≤ G kq cq (2 ^ ell) := by
  obtain ⟨k, c, h⟩ := progF_At L I E hK hsz
  refine ⟨k + 1, c, fun ell => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h ell
  have hl : ell ≤ 2 ^ ell := (Nat.lt_two_pow_self).le
  have e : G k (c + 2 ^ ell) (mag .nat ell) ≤ G (k + 1) c (2 ^ ell) := G_absorb hl
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e⟩

end QecReliability.Trans.BoundsEnc
