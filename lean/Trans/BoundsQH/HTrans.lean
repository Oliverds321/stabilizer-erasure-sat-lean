import Trans.BoundsQH.HParams

/-!
# Trans.BoundsQH.HTrans: transposed XOR programs (`transF`)

* `foldr_polyB_res`: a `foldr` of a `PolyB` step is `PolyB` if its result magnitude is
  bounded by one `G kR cR` of the argument (every suffix accumulator is such a result);
  `foldl_polyB_pre`: the same for `foldl` with all prefix accumulators.
* Wire invariants (`PInv` of `QPop`): `pAddWire_inv`, `scatterP_inv`, `revStep_inv`, `revP_inv`
  (all wires `≤ W + #gates`, `≤ 1` resp. `≤ 2` gates per step).
* `scatFold_P`, `revFold_P`, **`transF_P`**: the `trans` callee of `hash_on`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Hash QecReliability.Trans.Query.Plain

/-! ## Folds bounded through their results -/

section Folds
variable {a b : Ty}

theorem foldr_aux (F : FnSig (.prod a b) b) {k c kR cR : ℕ} (hF : FnB (G k c) F)
    (hS : ∀ (xs : List a.den) (z : b.den),
      mag b (foldrDen F xs z) ≤ G kR cR (mag (.prod (.list a) b) (xs, z))) (m : ℕ) :
    ∀ (xs : List a.den) (z : b.den), mag (.prod (.list a) b) (xs, z) ≤ m →
      foldrCost F xs z ≤ xs.length * (G k c (G kR cR m + m + 1) + 12) + 10 ∧
      foldrDepth F xs z ≤ xs.length + G k c (G kR cR m + m + 1) + 1 ∧
      foldrMsize F xs z ≤ G k c (G kR cR m + m + 1) + 10 * m + 5 * G kR cR m + 20
  | [], z, _ => by simp
  | x :: ys, z, hm => by
    have hm' : mag (.prod (.list a) b) (ys, z) ≤ m := by
      have := mag_cons a x ys; simp only [mag_prod] at hm ⊢; omega
    have hx : mag a x ≤ m := by have := mag_cons a x ys; simp only [mag_prod] at hm; omega
    obtain ⟨i1, i2, i3⟩ := foldr_aux F hF hS m ys z hm'
    have hacc := (hS ys z).trans (G_mono le_rfl le_rfl hm')
    obtain ⟨f1, f2, f3, -⟩ := hF (x, foldrDen F ys z)
    have e := G_mono (k := k) (c := c) le_rfl le_rfl
      (show mag (.prod a b) (x, foldrDen F ys z) ≤ G kR cR m + m + 1 by
        simp only [mag_prod]; omega)
    have z1 := sz_le (.prod (.list a) b) (ys, z)
    have z2 := sz_le (.prod a b) (x, foldrDen F ys z)
    simp only [mag_prod] at z1 z2 hm'
    refine ⟨?_, ?_, ?_⟩
    · simp only [foldrCost, List.length_cons, Nat.succ_mul]; omega
    · simp only [foldrDepth, List.length_cons]; omega
    · simp only [foldrMsize, max_le_iff]
      refine ⟨i3, by omega, ?_⟩
      simp only [Ty.enc_prod, Val.size_cons, Ty.sz_prod] at z1 z2 ⊢
      omega

/-- **`foldr` bounded through its results.** -/
theorem foldr_polyB_res (F : FnSig (.prod a b) b) (i : ℕ) (hF : PolyB F) {kR cR : ℕ}
    (hS : ∀ (xs : List a.den) (z : b.den),
      mag b (foldrDen F xs z) ≤ G kR cR (mag (.prod (.list a) b) (xs, z))) :
    PolyB (foldrF F i) := by
  obtain ⟨k, c, hFk⟩ := hF
  refine ⟨k + kR + 5, c + cR + 300, fun p => ?_⟩
  obtain ⟨xs, z⟩ := p
  obtain ⟨i1, i2, i3⟩ := foldr_aux F hFk hS _ xs z le_rfl
  generalize hm : mag (.prod (.list a) b) (xs, z) = m at i1 i2 i3 ⊢
  have hR := hS xs z
  rw [hm] at hR
  have hY : G k c (G kR cR m + m + 1) ≤ G (k + kR + 2) (c + cR) m := by
    have h1 : G kR cR m + m + 1 ≤ G (kR + 1) cR m := by
      have := G_succ kR cR m; have := le_G kR cR m; omega
    exact (G_mono le_rfl le_rfl h1).trans ((G_comp k c (kR + 1) cR m).trans
      (G_mono (by omega) le_rfl le_rfl))
  generalize G k c (G kR cR m + m + 1) = Y at i1 i2 i3 hY
  have hl := mag_list_len a xs
  have hlen : xs.length ≤ m := by rw [← hm]; simp only [mag_prod]; omega
  have L0 := le_G (k + kR + 2) (c + cR) m
  have Gs : (G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1) + 16 ≤
      G (k + kR + 3) (c + cR) m := G_sq _ _ _
  have q1 : xs.length * (Y + 12) ≤ G (k + kR + 2) (c + cR) m * (G (k + kR + 2) (c + cR) m + 12) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : G (k + kR + 2) (c + cR) m * (G (k + kR + 2) (c + cR) m + 12) ≤
      12 * ((G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1)) := by nlinarith
  have hRle : G kR cR m ≤ G (k + kR + 2) (c + cR) m := G_mono (by omega) (by omega) le_rfl
  have g3 : 100 * G (k + kR + 3) (c + cR + 300) m + 100 ≤ G (k + kR + 4) (c + cR + 300) m :=
    G_lin100 _ _ _ (by omega)
  have g2 : G (k + kR + 3) (c + cR) m ≤ G (k + kR + 3) (c + cR + 300) m :=
    G_mono le_rfl (by omega) le_rfl
  have g4 : 5 * G (k + kR + 4) (c + cR + 300) m + 16 ≤ G (k + kR + 5) (c + cR + 300) m :=
    G_succ _ _ _
  have g5 : G (k + kR + 2) (c + cR) m ≤ G (k + kR + 3) (c + cR) m := G_mono (by omega) le_rfl le_rfl
  simp only [foldrF_cost, foldrF_depth, foldrF_msize, foldrF_den]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem foldl_aux (F : FnSig (.prod b a) b) {k c kR cR : ℕ} (hF : FnB (G k c) F)
    (z0 : b.den) (xs0 : List a.den)
    (hS : ∀ ys zs, xs0 = ys ++ zs →
      mag b (foldlDen F z0 ys) ≤ G kR cR (mag (.prod b (.list a)) (z0, xs0))) :
    ∀ (zs ys : List a.den), xs0 = ys ++ zs →
      foldlCost F (foldlDen F z0 ys) zs ≤ zs.length *
        (G k c (G kR cR (mag (.prod b (.list a)) (z0, xs0)) + mag (.prod b (.list a)) (z0, xs0) + 1)
          + 12) + 10 ∧
      foldlDepth F (foldlDen F z0 ys) zs ≤ zs.length +
        G k c (G kR cR (mag (.prod b (.list a)) (z0, xs0)) + mag (.prod b (.list a)) (z0, xs0) + 1)
          + 1 ∧
      foldlMsize F (foldlDen F z0 ys) zs ≤
        G k c (G kR cR (mag (.prod b (.list a)) (z0, xs0)) + mag (.prod b (.list a)) (z0, xs0) + 1)
          + 10 * mag (.prod b (.list a)) (z0, xs0) +
          10 * G kR cR (mag (.prod b (.list a)) (z0, xs0)) + 20
  | [], ys, _ => by simp
  | x :: zs, ys, hxs => by
    have hxs' : xs0 = (ys ++ [x]) ++ zs := by simp [hxs]
    obtain ⟨i1, i2, i3⟩ := foldl_aux F hF z0 xs0 hS zs (ys ++ [x]) hxs'
    have hacc := hS ys (x :: zs) hxs
    have hacc2 := hS (ys ++ [x]) zs hxs'
    generalize hm : mag (.prod b (.list a)) (z0, xs0) = m at hS i1 i2 i3 hacc hacc2 ⊢
    have hmem : x ∈ xs0 := by rw [hxs]; simp
    have hx : mag a x ≤ m := by
      have := mag_mem a hmem; rw [← hm]; simp only [mag_prod]; omega
    have hzs : mag (.list a) (x :: zs) ≤ m := by
      have := mag_sublist a (show (x :: zs).Sublist xs0 by rw [hxs]; exact List.sublist_append_right _ _)
      rw [← hm]; simp only [mag_prod]; omega
    have eF : foldlDen F z0 (ys ++ [x]) = F.den (foldlDen F z0 ys, x) := by
      simp [foldlDen, List.foldl_append]
    rw [eF] at hacc2 i1 i2 i3
    obtain ⟨f1, f2, f3, -⟩ := hF (foldlDen F z0 ys, x)
    have e := G_mono (k := k) (c := c) le_rfl le_rfl
      (show mag (.prod b a) (foldlDen F z0 ys, x) ≤ G kR cR m + m + 1 by
        simp only [mag_prod]; omega)
    have z1 := sz_le (.prod b a) (foldlDen F z0 ys, x)
    have z2 := sz_le (.prod b (.list a)) (F.den (foldlDen F z0 ys, x), zs)
    have hzs' : mag (.list a) zs ≤ m := by
      have := mag_cons a x zs; omega
    simp only [mag_prod] at z1 z2
    refine ⟨?_, ?_, ?_⟩
    · simp only [foldlCost, List.length_cons, Nat.succ_mul]; omega
    · simp only [foldlDepth, List.length_cons]; omega
    · simp only [foldlMsize, max_le_iff]
      refine ⟨i3, by omega, ?_⟩
      simp only [Ty.enc_prod, Val.size_cons, Ty.sz_prod] at z1 z2 ⊢
      omega

/-- **`foldl` bounded through its prefix accumulators.** -/
theorem foldl_polyB_pre (F : FnSig (.prod b a) b) (i : ℕ) (hF : PolyB F) {kR cR : ℕ}
    (hS : ∀ (z : b.den) (xs ys zs : List a.den), xs = ys ++ zs →
      mag b (foldlDen F z ys) ≤ G kR cR (mag (.prod b (.list a)) (z, xs))) :
    PolyB (foldlF F i) := by
  obtain ⟨k, c, hFk⟩ := hF
  refine ⟨k + kR + 5, c + cR + 300, fun p => ?_⟩
  obtain ⟨z, xs⟩ := p
  obtain ⟨i1, i2, i3⟩ := foldl_aux F hFk z xs (hS z xs) xs [] (by simp)
  have hR := hS z xs xs [] (by simp)
  simp only [foldlDen_nil] at i1 i2 i3
  generalize hm : mag (.prod b (.list a)) (z, xs) = m at i1 i2 i3 hR ⊢
  have hY : G k c (G kR cR m + m + 1) ≤ G (k + kR + 2) (c + cR) m := by
    have h1 : G kR cR m + m + 1 ≤ G (kR + 1) cR m := by
      have := G_succ kR cR m; have := le_G kR cR m; omega
    exact (G_mono le_rfl le_rfl h1).trans ((G_comp k c (kR + 1) cR m).trans
      (G_mono (by omega) le_rfl le_rfl))
  generalize G k c (G kR cR m + m + 1) = Y at i1 i2 i3 hY
  have hl := mag_list_len a xs
  have hlen : xs.length ≤ m := by rw [← hm]; simp only [mag_prod]; omega
  have L0 := le_G (k + kR + 2) (c + cR) m
  have Gs : (G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1) + 16 ≤
      G (k + kR + 3) (c + cR) m := G_sq _ _ _
  have q1 : xs.length * (Y + 12) ≤ G (k + kR + 2) (c + cR) m * (G (k + kR + 2) (c + cR) m + 12) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : G (k + kR + 2) (c + cR) m * (G (k + kR + 2) (c + cR) m + 12) ≤
      12 * ((G (k + kR + 2) (c + cR) m + 1) * (G (k + kR + 2) (c + cR) m + 1)) := by nlinarith
  have hRle : G kR cR m ≤ G (k + kR + 2) (c + cR) m := G_mono (by omega) (by omega) le_rfl
  have g3 : 100 * G (k + kR + 3) (c + cR + 300) m + 100 ≤ G (k + kR + 4) (c + cR + 300) m :=
    G_lin100 _ _ _ (by omega)
  have g2 : G (k + kR + 3) (c + cR) m ≤ G (k + kR + 3) (c + cR + 300) m :=
    G_mono le_rfl (by omega) le_rfl
  have g4 : 5 * G (k + kR + 4) (c + cR + 300) m + 16 ≤ G (k + kR + 5) (c + cR + 300) m :=
    G_succ _ _ _
  have g5 : G (k + kR + 2) (c + cR) m ≤ G (k + kR + 3) (c + cR) m := G_mono (by omega) le_rfl le_rfl
  simp only [foldlF_cost, foldlF_depth, foldlF_msize, foldlF_den]
  refine ⟨by omega, by omega, by omega, by omega⟩

end Folds

/-! ## Wire invariants of scatter and reverse -/

theorem pinv_of_mag (P : ProgP) : PInv (mag TProg P) P := by
  have e : mag TProg P = mag (.list TGate) P.1 + mag (.list .nat) P.2 + 1 := rfl
  refine ⟨fun g hg => ?_, fun o ho => ?_⟩
  · have h1 := mag_mem TGate hg
    have e2 : mag TGate g = g.2.2.1 + g.2.2.2 + 5 := by simp only [mag, magL]; omega
    omega
  · have := mag_mem .nat ho; simp only [mag_nat] at this; omega

theorem PInv.mono {W W' : ℕ} {P : ProgP} (h : PInv W P) (hW : W ≤ W') : PInv W' P :=
  ⟨fun g hg => ⟨(h.1 g hg).1.trans hW, (h.1 g hg).2.trans hW⟩, fun o ho => (h.2 o ho).trans hW⟩

theorem pAddWire_inv {W n : ℕ} {P : ProgP} (t s : ℕ) (hP : PInv (W + P.1.length) P) (hn : n ≤ W)
    (hs : s ≤ W + P.1.length) :
    PInv (W + P.1.length + 1) (pAddWire n P t s) ∧ (pAddWire n P t s).1.length = P.1.length + 1 ∧
      (pAddWire n P t s).2.length = P.2.length := by
  obtain ⟨h1, h2⟩ := hP
  have g := getD_le h2 t
  simp only [pAddWire, List.length_append, List.length_cons, List.length_nil, List.length_set]
  refine ⟨⟨fun x hx => ?_, set_le (fun a ha => (h2 a ha).trans (by omega)) t _ (by omega)⟩,
    by simp, by simp⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨(h1 x hx).1.trans (by omega), (h1 x hx).2.trans (by omega)⟩
  · simp only [List.mem_singleton] at hx; subst hx; dsimp only; omega

theorem scatterP_inv {W n : ℕ} (hn : n ≤ W) (P : ProgP) (hP : PInv (W + P.1.length) P) :
    ∀ xs : List (ℕ × ℕ), (∀ x ∈ xs, x.2 ≤ W) →
    PInv (W + P.1.length + xs.length) (scatterP n P xs) ∧
      (scatterP n P xs).1.length = P.1.length + xs.length ∧ (scatterP n P xs).2.length = P.2.length
  | [], _ => by simpa [scatterP] using hP
  | ts :: xs, hx => by
    obtain ⟨i1, i2, i3⟩ := scatterP_inv hn P hP xs (fun y hy => hx y (by simp [hy]))
    have hts := hx ts (by simp)
    obtain ⟨j1, j2, j3⟩ := pAddWire_inv (n := n) (W := W) ts.1 ts.2 (i1.mono (by omega)) hn
      (by omega)
    simp only [scatterP, List.length_cons]
    exact ⟨j1.mono (by omega), by omega, by omega⟩

theorem revStep_inv {W n : ℕ} (hn : n ≤ W) (P : ProgP) (g : GateP) (hP : PInv (W + P.1.length) P) :
    PInv (W + (revStep n P g).1.length) (revStep n P g) ∧
      (revStep n P g).1.length ≤ P.1.length + 2 ∧ (revStep n P g).2.length ≤ P.2.length := by
  unfold revStep
  split
  · refine ⟨⟨hP.1, fun o ho => hP.2 o (List.dropLast_sublist _ |>.subset ho)⟩, by simp,
      by simp⟩
  · have s1 := getD_le hP.2 (P.2.length - 1)
    obtain ⟨j1, j2, j3⟩ := pAddWire_inv (n := n) g.2.2.1 (P.2.getD (P.2.length - 1) 0) hP hn s1
    have s2 := getD_le j1.2 (P.2.length - 1)
    obtain ⟨k1, k2, k3⟩ := pAddWire_inv (n := n) (W := W)
      g.2.2.2 ((pAddWire n P g.2.2.1 (P.2.getD (P.2.length - 1) 0)).2.getD (P.2.length - 1) 0)
      (j1.mono (by omega)) hn (by omega)
    refine ⟨⟨fun x hx => ?_, fun o ho => ?_⟩, by dsimp only; omega, ?_⟩
    · have := k1.1 x hx; dsimp only; omega
    · have := k1.2 o (List.dropLast_sublist _ |>.subset ho); dsimp only; omega
    · dsimp only; rw [List.length_dropLast]; omega

theorem revP_inv {W n : ℕ} (hn : n ≤ W) : ∀ (gs : List GateP) (P : ProgP),
    PInv (W + P.1.length) P →
    PInv (W + (revP n gs P).1.length) (revP n gs P) ∧
      (revP n gs P).1.length ≤ P.1.length + 2 * gs.length ∧ (revP n gs P).2.length ≤ P.2.length
  | [], P, hP => by simpa [revP] using hP
  | g :: gs, P, hP => by
    obtain ⟨i1, i2, i3⟩ := revStep_inv hn P g hP
    obtain ⟨j1, j2, j3⟩ := revP_inv hn gs (revStep n P g) i1
    simp only [revP, List.length_cons]
    exact ⟨j1, by omega, by omega⟩

/-! ## The folds of `transF` -/

theorem scatFold_P {iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg}
    (haw : PolyB iaw) (hawd : ∀ x, iaw.den x = pAddWire x.1 x.2.1 x.2.2.1 x.2.2.2) (is i : ℕ) :
    PolyB (foldrF (scatStepF iaw is) i) := by
  refine foldr_polyB_res _ _ (scatStepF_P haw hawd is) (kR := 2) (cR := 40) (fun xs z => ?_)
  obtain ⟨(n : ℕ), P⟩ := z
  have hden : foldrDen (scatStepF iaw is) xs (n, P) = (n, scatterP n P xs) := by
    rw [← scatterP_foldr]
    simp only [foldrDen, scatStepF, exactSig_den]
    try rfl
  rw [hden]
  have hxs : ∀ x ∈ xs, x.2 ≤ n + mag TProg P + mag (.list (.prod .nat .nat)) xs := by
    rintro ⟨(a : ℕ), (b : ℕ)⟩ hx
    have h1 := mag_mem (.prod .nat .nat) hx
    have h2 : mag (.prod .nat .nat) (a, b) = a + b + 1 := rfl
    show b ≤ _
    omega
  have hnW : n ≤ n + mag TProg P + mag (.list (.prod .nat .nat)) xs := by omega
  have hPW : PInv (n + mag TProg P + mag (.list (.prod .nat .nat)) xs + P.1.length) P :=
    (pinv_of_mag P).mono (by omega)
  obtain ⟨i1, i2, i3⟩ := scatterP_inv hnW P hPW xs hxs
  have hm : mag TProg (scatterP n P xs) ≤ ((scatterP n P xs).1.length + (scatterP n P xs).2.length + 2) *
      (2 * (n + mag TProg P + mag (.list (.prod .nat .nat)) xs + P.1.length + xs.length) + 10) :=
    mag_prog_le _ i1
  rw [i2, i3] at hm
  have l1 := mag_list_len TGate P.1
  have l2 := mag_list_len .nat P.2
  have l3 := mag_list_len (.prod .nat .nat) xs
  have eP : mag TProg P = mag (.list TGate) P.1 + mag (.list .nat) P.2 + 1 := rfl
  have e1 : mag TNP (n, scatterP n P xs) = n + mag TProg (scatterP n P xs) + 1 := rfl
  have e2 : mag (.prod (.list (.prod .nat .nat)) TNP) (xs, (n, P)) =
      mag (.list (.prod .nat .nat)) xs + (n + mag TProg P + 1) + 1 := rfl
  rw [e1, e2]
  generalize hm' : mag (.list (.prod .nat .nat)) xs + (n + mag TProg P + 1) + 1 = m
  have q1 : (P.1.length + xs.length + P.2.length + 2) *
      (2 * (n + mag TProg P + mag (.list (.prod .nat .nat)) xs + P.1.length + xs.length) + 10) ≤
      (2 * m) * (6 * m + 10) := Nat.mul_le_mul (by omega) (by omega)
  have q2 : (2 * m) * (6 * m + 10) + m + 1 ≤ 40 * ((m + 1) * (m + 1)) := by nlinarith
  have q3 := quad_le 40 m
  omega

theorem revFold_P {iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg}
    {idl : FnSig (.list .nat) (.list .nat)} {igd0 : FnSig (.prod (.list .nat) .nat) .nat}
    {ipred ilen : ℕ} (haw : PolyB iaw)
    (hawd : ∀ x, iaw.den x = pAddWire x.1 x.2.1 x.2.2.1 x.2.2.2) (hdl : PolyB idl)
    (hdld : ∀ x, idl.den x = x.dropLast) (hgd : PolyB igd0)
    (hgdd : ∀ x, igd0.den x = x.1.getD x.2 0) (ir i : ℕ) :
    PolyB (foldlF (revStepF iaw idl igd0 ipred ilen ir) i) := by
  refine foldl_polyB_pre _ _ (revStepF_P haw hawd hdl hdld hgd hgdd ir) (kR := 2) (cR := 60)
    (fun z xs ys zs hxs => ?_)
  obtain ⟨(n : ℕ), P⟩ := z
  have hden : foldlDen (revStepF iaw idl igd0 ipred ilen ir) (n, P) ys = (n, revP n ys P) := by
    rw [← revP_foldl]
    simp only [foldlDen, revStepF, exactSig_den]
    try rfl
  rw [hden]
  have hnW : n ≤ n + mag TProg P := by omega
  have hPW : PInv (n + mag TProg P + P.1.length) P := (pinv_of_mag P).mono (by omega)
  obtain ⟨i1, i2, i3⟩ := revP_inv hnW ys P hPW
  have hm : mag TProg (revP n ys P) ≤ ((revP n ys P).1.length + (revP n ys P).2.length + 2) *
      (2 * (n + mag TProg P + (revP n ys P).1.length) + 10) := mag_prog_le _ i1
  have hys : ys.length ≤ xs.length := by rw [hxs]; simp
  have l1 := mag_list_len TGate P.1
  have l2 := mag_list_len .nat P.2
  have l3 := mag_list_len TGate xs
  have eP : mag TProg P = mag (.list TGate) P.1 + mag (.list .nat) P.2 + 1 := rfl
  have e1 : mag TNP (n, revP n ys P) = n + mag TProg (revP n ys P) + 1 := rfl
  have e2 : mag (.prod TNP (.list TGate)) ((n, P), xs) =
      n + mag TProg P + 1 + mag (.list TGate) xs + 1 := rfl
  rw [e1, e2]
  generalize hm' : n + mag TProg P + 1 + mag (.list TGate) xs + 1 = m
  have q1 : ((revP n ys P).1.length + (revP n ys P).2.length + 2) *
      (2 * (n + mag TProg P + (revP n ys P).1.length) + 10) ≤
      (3 * m) * (8 * m + 10) := Nat.mul_le_mul (by omega) (by omega)
  have q2 : (3 * m) * (8 * m + 10) + m + 1 ≤ 60 * ((m + 1) * (m + 1)) := by nlinarith
  have q3 := quad_le 60 m
  omega

/-- **The `trans` callee of `hash_on` is polynomially bounded.** -/
theorem transF_P {ilen iadd irep irev iip : ℕ}
    {iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg}
    {idl : FnSig (.list .nat) (.list .nat)} {igd0 : FnSig (.prod (.list .nat) .nat) .nat}
    {ipred ilen' : ℕ} (haw : PolyB iaw)
    (hawd : ∀ x, iaw.den x = pAddWire x.1 x.2.1 x.2.2.1 x.2.2.2) (hdl : PolyB idl)
    (hdld : ∀ x, idl.den x = x.dropLast) (hgd : PolyB igd0)
    (hgdd : ∀ x, igd0.den x = x.1.getD x.2 0) (is isc ir irv i : ℕ) :
    PolyB (transF ilen iadd irep irev iip (foldrF (scatStepF iaw is) isc)
      (foldlF (revStepF iaw idl igd0 ipred ilen' ir) irv) i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨k, C⟩ := x
      have h1 := scatterP_foldr C.2.length ([constGate false], List.replicate (k + C.1.length)
        C.2.length) (idxPairs C.2 0)
      have h2 := revP_foldl C.2.length C.1.reverse (scatterP C.2.length ([constGate false],
        List.replicate (k + C.1.length) C.2.length) (idxPairs C.2 0))
      rw [idxPairs_eq] at h1
      have hFsd : ∀ x, (scatStepF iaw is).den x = scatStep x.1 x.2 := fun x => by
        simp only [scatStepF, exactSig_den]
      have hFrd : ∀ x, (revStepF iaw idl igd0 ipred ilen' ir).den x = revFold x.1 x.2 := fun x => by
        simp only [revStepF, exactSig_den, revFold]
      simp only [transBody, tm_simp, foldrF_den, foldlF_den, foldrDen, foldlDen, hFsd, hFrd,
        ipairsF_den, lengthF_den, addF_den, replicateF_den, reverseF_den, transP]
      rw [show (fun x acc => scatStep (x : ℕ × ℕ) acc) = scatStep from rfl, h1]
      rw [show (fun acc x => revFold acc (x : GateP)) = revFold from rfl, ← idxPairs_eq, h2])
    (by simp [Tm.CallsP, transBody, polyB, scatFold_P haw hawd is isc,
      revFold_P haw hawd hdl hdld hgd hgdd ir irv])

end QecReliability.Trans.BoundsQH
