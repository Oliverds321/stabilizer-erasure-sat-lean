import Trans.BoundsQH.HMain
import Trans.HashCallees.Main

/-!
# Trans.BoundsQH.HFold: folds with bounded accumulators; the encoder index map

* `foldl_polyB`, `foldr_polyB`: an `FL.Lib` fold of a `PolyB` step is `PolyB` as soon as, for
  every argument, an invariant of the accumulators bounds their magnitude by one
  `G k c (mag arg)` (via `FL.Lib.foldl_bounds`/`foldr_bounds`).
* `nbrF_P`: the MGG neighbour map (`nbrF_FnB` of `HashCallees/MGGBounds.lean`).
* `visitsF_P`, `encIdxF_P`, **`encOutsF_P`**: the `encOuts` callee of `hash_on`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Hash QecReliability.Trans.Query.Plain

/-! ## Folds -/

section Folds
variable {a b : Ty}

/-- Common bound for one fold step: accumulator magnitude `≤ R`, element magnitude `≤ m`. -/
theorem fold_step_le {k c : ℕ} {F : FnSig (.prod b a) b} (hF : FnB (G k c) F) {acc : b.den}
    {x : a.den} {R m : ℕ} (hacc : mag b acc ≤ R) (hx : mag a x ≤ m) :
    F.cost (acc, x) ≤ G k c (R + m + 1) ∧ F.depth (acc, x) ≤ G k c (R + m + 1) ∧
      F.msize (acc, x) ≤ G k c (R + m + 1) ∧ mag b (F.den (acc, x)) ≤ G k c (R + m + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := hF (acc, x)
  have e := G_mono (k := k) (c := c) le_rfl le_rfl
    (show mag (.prod b a) (acc, x) ≤ R + m + 1 by simp only [mag_prod]; omega)
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e⟩

/-- **`foldl` with bounded accumulators.** -/
theorem foldl_polyB (F : FnSig (.prod b a) b) (i : ℕ) (hF : PolyB F) {kR cR : ℕ}
    (hS : ∀ (z : b.den) (xs : List a.den), ∃ S : b.den → Prop, S z ∧
      (∀ x ∈ xs, ∀ acc, S acc → S (F.den (acc, x))) ∧
      ∀ acc, S acc → mag b acc ≤ G kR cR (mag (.prod b (.list a)) (z, xs))) :
    PolyB (foldlF F i) := by
  obtain ⟨k, c, hFk⟩ := hF
  refine ⟨k + kR + 5, c + cR + 300, fun p => ?_⟩
  obtain ⟨z, xs⟩ := p
  obtain ⟨S, hz, hstep, hR⟩ := hS z xs
  generalize hm : mag (.prod b (.list a)) (z, xs) = m at hR ⊢
  have hY : G k c (G kR cR m + m + 1) ≤ G (k + kR + 2) (c + cR) m := by
    have h1 : G kR cR m + m + 1 ≤ G (kR + 1) cR m := by
      have := G_succ kR cR m; have := le_G kR cR m; omega
    exact (G_mono le_rfl le_rfl h1).trans ((G_comp k c (kR + 1) cR m).trans
      (G_mono (by omega) le_rfl le_rfl))
  generalize hRd : G kR cR m = R at hR hY
  generalize hYd : G k c (R + m + 1) = Y at hY
  have hxs : ∀ x ∈ xs, mag a x ≤ m := fun x hx => by
    have := mag_mem a hx; rw [← hm]; simp only [mag_prod]; omega
  have hz' : mag b z ≤ m := by rw [← hm]; simp only [mag_prod]; omega
  obtain ⟨r1, r2, r3, r4, r5⟩ := foldl_bounds F S Y Y (Y + 5 * R + 1) xs z hz
    (by have := sz_le b z; have := hR z hz; omega)
    (fun x hx acc hacc _ => by
      obtain ⟨f1, f2, f3, f4⟩ := fold_step_le hFk (hR acc hacc) (hxs x hx)
      rw [hYd] at f1 f2 f3 f4
      have s1 := hstep x hx acc hacc
      have := sz_le b (F.den (acc, x))
      have := hR _ s1
      exact ⟨s1, by omega, f1, f2, by omega⟩)
  have hl := mag_list_len a xs
  have hlen : xs.length ≤ m := by rw [← hm]; simp only [mag_prod]; omega
  have hsx := sz_le (.list a) xs
  have hmx : mag (.list a) xs ≤ m := by rw [← hm]; simp only [mag_prod]; omega
  have Gs : (G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1) + 16 ≤
      G (k + kR + 3) (c + cR) m := G_sq _ _ _
  have L0 := le_G (k + kR + 2) (c + cR) m
  have q1 : (Y + 12) * xs.length ≤ (G (k + kR + 2) (c + cR) m + 12) * G (k + kR + 2) (c + cR) m :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : (G (k + kR + 2) (c + cR) m + 12) * G (k + kR + 2) (c + cR) m ≤
      12 * ((G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1)) := by nlinarith
  have hRle : R ≤ G (k + kR + 2) (c + cR) m := hRd ▸ G_mono (by omega) (by omega) le_rfl
  have g3 : 100 * G (k + kR + 3) (c + cR + 300) m + 100 ≤ G (k + kR + 4) (c + cR + 300) m :=
    G_lin100 _ _ _ (by omega)
  have g2 : G (k + kR + 3) (c + cR) m ≤ G (k + kR + 3) (c + cR + 300) m :=
    G_mono le_rfl (by omega) le_rfl
  have g4 : 5 * G (k + kR + 4) (c + cR + 300) m + 16 ≤ G (k + kR + 5) (c + cR + 300) m :=
    G_succ _ _ _
  have g5 : G (k + kR + 2) (c + cR) m ≤ G (k + kR + 3) (c + cR) m := G_mono (by omega) le_rfl le_rfl
  simp only [foldlF_cost, foldlF_depth, foldlF_msize, foldlF_den]
  refine ⟨by omega, by omega, by omega, ?_⟩
  have := hR _ r1
  omega

/-- **`foldr` with bounded accumulators.** -/
theorem foldr_polyB (F : FnSig (.prod a b) b) (i : ℕ) (hF : PolyB F) {kR cR : ℕ}
    (hS : ∀ (xs : List a.den) (z : b.den), ∃ S : b.den → Prop, S z ∧
      (∀ x ∈ xs, ∀ acc, S acc → S (F.den (x, acc))) ∧
      ∀ acc, S acc → mag b acc ≤ G kR cR (mag (.prod (.list a) b) (xs, z))) :
    PolyB (foldrF F i) := by
  obtain ⟨k, c, hFk⟩ := hF
  refine ⟨k + kR + 5, c + cR + 300, fun p => ?_⟩
  obtain ⟨xs, z⟩ := p
  obtain ⟨S, hz, hstep, hR⟩ := hS xs z
  generalize hm : mag (.prod (.list a) b) (xs, z) = m at hR ⊢
  have hY : G k c (G kR cR m + m + 1) ≤ G (k + kR + 2) (c + cR) m := by
    have h1 : G kR cR m + m + 1 ≤ G (kR + 1) cR m := by
      have := G_succ kR cR m; have := le_G kR cR m; omega
    exact (G_mono le_rfl le_rfl h1).trans ((G_comp k c (kR + 1) cR m).trans
      (G_mono (by omega) le_rfl le_rfl))
  generalize hRd : G kR cR m = R at hR hY
  generalize hYd : G k c (R + m + 1) = Y at hY
  have hxs : ∀ x ∈ xs, mag a x ≤ m := fun x hx => by
    have := mag_mem a hx; rw [← hm]; simp only [mag_prod]; omega
  have stepB : ∀ x ∈ xs, ∀ acc, S acc → F.cost (x, acc) ≤ Y ∧ F.depth (x, acc) ≤ Y ∧
      F.msize (x, acc) ≤ Y := fun x hx acc hacc => by
    obtain ⟨f1, f2, f3, -⟩ := hFk (x, acc)
    have e := G_mono (k := k) (c := c) le_rfl le_rfl
      (show mag (.prod a b) (x, acc) ≤ R + m + 1 by
        have := hR acc hacc; have := hxs x hx; simp only [mag_prod]; omega)
    rw [hYd] at e
    exact ⟨f1.trans e, f2.trans e, f3.trans e⟩
  obtain ⟨r1, r2, r3, r4, r5⟩ := foldr_bounds F S Y Y (Y + 5 * R + 1) xs z hz
    (by have := sz_le b z; have := hR z hz; omega)
    (fun x hx acc hacc _ => by
      obtain ⟨f1, f2, f3⟩ := stepB x hx acc hacc
      have s1 := hstep x hx acc hacc
      have := sz_le b (F.den (x, acc))
      have := hR _ s1
      exact ⟨s1, by omega, f1, f2, by omega⟩)
  have hl := mag_list_len a xs
  have hlen : xs.length ≤ m := by rw [← hm]; simp only [mag_prod]; omega
  have hsx := sz_le (.list a) xs
  have hmx : mag (.list a) xs ≤ m := by rw [← hm]; simp only [mag_prod]; omega
  have Gs : (G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1) + 16 ≤
      G (k + kR + 3) (c + cR) m := G_sq _ _ _
  have L0 := le_G (k + kR + 2) (c + cR) m
  have q1 : (Y + 12) * xs.length ≤ (G (k + kR + 2) (c + cR) m + 12) * G (k + kR + 2) (c + cR) m :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : (G (k + kR + 2) (c + cR) m + 12) * G (k + kR + 2) (c + cR) m ≤
      12 * ((G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1)) := by nlinarith
  have hRle : R ≤ G (k + kR + 2) (c + cR) m := hRd ▸ G_mono (by omega) (by omega) le_rfl
  have g3 : 100 * G (k + kR + 3) (c + cR + 300) m + 100 ≤ G (k + kR + 4) (c + cR + 300) m :=
    G_lin100 _ _ _ (by omega)
  have g2 : G (k + kR + 3) (c + cR) m ≤ G (k + kR + 3) (c + cR + 300) m :=
    G_mono le_rfl (by omega) le_rfl
  have g4 : 5 * G (k + kR + 4) (c + cR + 300) m + 16 ≤ G (k + kR + 5) (c + cR + 300) m :=
    G_succ _ _ _
  have g5 : G (k + kR + 2) (c + cR) m ≤ G (k + kR + 3) (c + cR) m := G_mono (by omega) le_rfl le_rfl
  simp only [foldrF_cost, foldrF_depth, foldrF_msize, foldrF_den]
  refine ⟨by omega, by omega, by omega, ?_⟩
  have := hR _ r1
  omega

end Folds

/-! ## `foldl` with step-indexed accumulator invariants -/

section FoldIdx
variable {a b : Ty}

/-- `foldl` bounds from an invariant indexed by the number of steps taken. -/
theorem foldl_bounds_idx (F : FnSig (.prod b a) b) (S : ℕ → b.den → Prop) (K D M N : ℕ) :
    ∀ (xs : List a.den) (z : b.den) (j : ℕ), j + xs.length ≤ N → S j z → (b.enc z).size ≤ M →
    (∀ x ∈ xs, ∀ i, i < N → ∀ acc, S i acc → (b.enc acc).size ≤ M → S (i + 1) (F.den (acc, x)) ∧
      (b.enc (F.den (acc, x))).size ≤ M ∧
      F.cost (acc, x) ≤ K ∧ F.depth (acc, x) ≤ D ∧ F.msize (acc, x) ≤ M) →
    S (j + xs.length) (foldlDen F z xs) ∧ (b.enc (foldlDen F z xs)).size ≤ M ∧
      foldlCost F z xs ≤ (K + 12) * xs.length + 10 ∧
      foldlDepth F z xs ≤ xs.length + D + 1 ∧
      foldlMsize F z xs ≤ 2 * (Ty.enc (.list a) xs).size + 2 * M + 2
  | [], z, j, _, hz, hzM, _ => by simp [hz, hzM]
  | x :: xs, z, j, hN, hz, hzM, hS => by
    simp only [List.length_cons] at hN
    obtain ⟨g1, g2, g3, g4, g5⟩ := hS x (by simp) j (by omega) z hz hzM
    obtain ⟨h1, h2, h3, h4, h5⟩ := foldl_bounds_idx F S K D M N xs (F.den (z, x)) (j + 1)
      (by omega) g1 g2 (fun y hy => hS y (by simp [hy]))
    refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1] using h1, h2, ?_, ?_, ?_⟩
    · simp only [foldlCost, List.length_cons]; nlinarith
    · simp only [foldlDepth, List.length_cons]; omega
    · simp only [foldlMsize, Ty.enc_prod, Val.size_cons, Ty.sz_list_cons, max_le_iff]
      refine ⟨by have := Ty.sz_list_cons a x xs; omega, by omega, ?_⟩
      have := Ty.sz_list_cons a x xs
      omega

/-- **`foldl` with step-indexed bounded accumulators.** -/
theorem foldl_polyB_idx (F : FnSig (.prod b a) b) (i : ℕ) (hF : PolyB F) {kR cR : ℕ}
    (hS : ∀ (z : b.den) (xs : List a.den), ∃ S : ℕ → b.den → Prop, S 0 z ∧
      (∀ x ∈ xs, ∀ n, n < xs.length → ∀ acc, S n acc → S (n + 1) (F.den (acc, x))) ∧
      ∀ n, n ≤ xs.length → ∀ acc, S n acc →
        mag b acc ≤ G kR cR (mag (.prod b (.list a)) (z, xs))) :
    PolyB (foldlF F i) := by
  obtain ⟨k, c, hFk⟩ := hF
  refine ⟨k + kR + 5, c + cR + 300, fun p => ?_⟩
  obtain ⟨z, xs⟩ := p
  obtain ⟨S, hz, hstep, hR⟩ := hS z xs
  generalize hm : mag (.prod b (.list a)) (z, xs) = m at hR ⊢
  have hY : G k c (G kR cR m + m + 1) ≤ G (k + kR + 2) (c + cR) m := by
    have h1 : G kR cR m + m + 1 ≤ G (kR + 1) cR m := by
      have := G_succ kR cR m; have := le_G kR cR m; omega
    exact (G_mono le_rfl le_rfl h1).trans ((G_comp k c (kR + 1) cR m).trans
      (G_mono (by omega) le_rfl le_rfl))
  generalize hRd : G kR cR m = R at hR hY
  generalize hYd : G k c (R + m + 1) = Y at hY
  have hxs : ∀ x ∈ xs, mag a x ≤ m := fun x hx => by
    have := mag_mem a hx; rw [← hm]; simp only [mag_prod]; omega
  let S' : ℕ → b.den → Prop := fun n acc => n ≤ xs.length ∧ S n acc
  obtain ⟨r1, r2, r3, r4, r5⟩ := foldl_bounds_idx F S' Y Y (Y + 5 * R + 1) xs.length xs z 0
    (by omega) ⟨Nat.zero_le _, hz⟩ (by have := sz_le b z; have := hR 0 (Nat.zero_le _) z hz; omega)
    (fun x hx n hn acc hacc _ => by
      have hacc' := hR n hacc.1 acc hacc.2
      obtain ⟨f1, f2, f3, f4⟩ := fold_step_le hFk hacc' (hxs x hx)
      rw [hYd] at f1 f2 f3 f4
      have s1 := hstep x hx n hn acc hacc.2
      have := sz_le b (F.den (acc, x))
      have := hR (n + 1) (by omega) _ s1
      exact ⟨⟨by omega, s1⟩, by omega, f1, f2, by omega⟩)
  have hl := mag_list_len a xs
  have hlen : xs.length ≤ m := by rw [← hm]; simp only [mag_prod]; omega
  have hsx := sz_le (.list a) xs
  have hmx : mag (.list a) xs ≤ m := by rw [← hm]; simp only [mag_prod]; omega
  have Gs : (G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1) + 16 ≤
      G (k + kR + 3) (c + cR) m := G_sq _ _ _
  have L0 := le_G (k + kR + 2) (c + cR) m
  have q1 : (Y + 12) * xs.length ≤ (G (k + kR + 2) (c + cR) m + 12) * G (k + kR + 2) (c + cR) m :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : (G (k + kR + 2) (c + cR) m + 12) * G (k + kR + 2) (c + cR) m ≤
      12 * ((G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1)) := by nlinarith
  have hRle : R ≤ G (k + kR + 2) (c + cR) m := hRd ▸ G_mono (by omega) (by omega) le_rfl
  have g3 : 100 * G (k + kR + 3) (c + cR + 300) m + 100 ≤ G (k + kR + 4) (c + cR + 300) m :=
    G_lin100 _ _ _ (by omega)
  have g2 : G (k + kR + 3) (c + cR) m ≤ G (k + kR + 3) (c + cR + 300) m :=
    G_mono le_rfl (by omega) le_rfl
  have g4 : 5 * G (k + kR + 4) (c + cR + 300) m + 16 ≤ G (k + kR + 5) (c + cR + 300) m :=
    G_succ _ _ _
  have g5 : G (k + kR + 2) (c + cR) m ≤ G (k + kR + 3) (c + cR) m := G_mono (by omega) le_rfl le_rfl
  simp only [foldlF_cost, foldlF_depth, foldlF_msize, foldlF_den]
  refine ⟨by omega, by omega, by omega, ?_⟩
  have := hR _ (by omega) _ r1.2
  omega

end FoldIdx

/-! ## The encoder index map (`encOuts`) -/

section EncOuts
open QecReliability.Trans.HashCallees QecReliability.UniformAdapter

theorem B0B0_ge (m : ℕ) : 6000 * (m + 4) ^ 2 ≤ G 2 0 m := by
  show 6000 * (m + 4) ^ 2 ≤ B0 (B0 (m + 0))
  unfold B0
  simp only [Nat.add_zero]
  have h16 : 16 ≤ (m + 4) ^ 2 := by
    have := Nat.pow_le_pow_left (show 4 ≤ m + 4 by omega) 2; simpa using this
  generalize (m + 4) ^ 2 = y at *
  nlinarith

theorem nbrF_P (L : HashCallees.Lib) (irot icoord i : ℕ) : PolyB (nbrF L irot icoord i) :=
  ⟨2, 0, FnB.mono (fun m => B0B0_ge m) (nbrF_FnB L irot icoord i)⟩

theorem visStepNbr_P (L : HashCallees.Lib) (irot icoord inbr ivs : ℕ) :
    PolyB (visStepF (nbrF L irot icoord inbr) L.dmF ivs) :=
  visStepF_P (nbrF_P L irot icoord inbr) (divModF_P _ _ _) (fun _ => rfl) ivs

theorem visitsF_P (L : HashCallees.Lib) (irot icoord inbr ivs ifo : ℕ) :
    PolyB (foldlF (visStepF (nbrF L irot icoord inbr) L.dmF ivs) ifo) := by
  refine foldl_polyB _ _ (visStepNbr_P L irot icoord inbr ivs) (kR := 2) (cR := 0)
    (fun z xs => ?_)
  obtain ⟨(s : ℕ), (v0 : ℕ), (w0 : ℕ)⟩ := z
  refine ⟨fun acc => (acc.1 : ℕ) = s ∧ (acc.2.1 : ℕ) ≤ max v0 (s * s) ∧ (acc.2.2 : ℕ) ≤ w0,
    ⟨by simp, by simp, by simp⟩, ?_, ?_⟩
  · rintro x - ⟨(s' : ℕ), (v : ℕ), (w : ℕ)⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    subst h1
    simp only [visStepF, exactSig_den, nbrF, exactSig_den]
    refine ⟨by simp, ?_, (Nat.div_le_self w 16).trans h3⟩
    exact (nbrP_le s' v (w % 16)).trans (le_max_right _ _)
  · rintro ⟨(s' : ℕ), (v : ℕ), (w : ℕ)⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    subst h1
    have e : mag (.prod .nat (.prod .nat .nat)) (s', v, w) = s' + (v + w + 1) + 1 := rfl
    have e2 : mag (.prod (.prod .nat (.prod .nat .nat)) (.list .nat)) ((s', v0, w0), xs) =
        s' + (v0 + w0 + 1) + 1 + mag (.list .nat) xs + 1 := rfl
    rw [e, e2]
    generalize hm : s' + (v0 + w0 + 1) + 1 + mag (.list .nat) xs + 1 = m
    have hs : s' * s' ≤ (m + 1) * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
    have g1 : (m + 1) * (m + 1) + 16 ≤ G 1 0 m := G_sq 0 0 m
    have g2 : 5 * G 1 0 m + 16 ≤ G 2 0 m := G_succ 1 0 m
    have hv : v ≤ v0 + s' * s' :=
      le_trans h2 (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
    have h3' : w ≤ w0 := h3
    have hX := sq_ge m
    omega

theorem encIdxF_P (L : HashCallees.Lib) (irot icoord inbr ivs ifo iidx : ℕ) :
    PolyB (encIdxF L.dmF L.mul L.add L.range
      (foldlF (visStepF (nbrF L irot icoord inbr) L.dmF ivs) ifo) (gNbr actualMGG) iidx) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨⟨s, D, M, t⟩, x⟩ := x
      have h := pvisits_foldl (gNbr actualMGG) s ((x % t + t * (x / t % M)) % t)
        ((x % t + t * (x / t % M)) / t / D) ((x % t + t * (x / t % M)) / t % D)
      simp only [encIdxBody, tm_simp, divModF_den, addF_den, mulF_den, rangeF_den, foldlF_den,
        foldlDen, visStepF, exactSig_den, nbrF_den, encIndex]
      rw [h])
    (by simp [Tm.CallsP, encIdxBody, polyB, divModF_P, visitsF_P])

/-- **The `encOuts` callee of `hash_on` is polynomially bounded.** -/
theorem encOutsF_P (L : HashCallees.Lib) (R : RotIx) (inbr ivs ifo iidx imap : ℕ) :
    PolyB (encOutsF L R inbr ivs ifo iidx imap) :=
  mapEnvH_P (encIdxF_P L R.rot R.coord inbr ivs ifo iidx) imap

end EncOuts

end QecReliability.Trans.BoundsQH
