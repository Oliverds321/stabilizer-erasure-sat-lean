import Trans.BoundsQH.HAff

/-!
# Trans.BoundsEnc.Basic: pointwise bound tools for the encoder oracle

The encoder's callees are polynomially bounded only on restricted argument sets (the
power-graph walk accumulates a port word `< 16^K`, polynomial only for a fixed walk length
`K`), and the top level is bounded in `2^ell` rather than in the magnitude of `ell`. Tools:

* `FnBAt.lift`, `fnBAt_P` (a `PolyB` fact at any argument for large constants);
* `fnBAt_exactP`: the generic term bound for `exactSig` at one argument with **explicit
  constants** (`Tm.boundP`), so that ell-dependent constants can be threaded through;
* `mapEnvH_At`: `Hash.mapEnvF` with callee bounds only at the elements of the list;
* `foldl_At`: `foldlF` with a step-indexed invariant, callee bounds only at the visited
  accumulators, and an arbitrary magnitude `m ≥ mag (z, xs)` (`foldl_FnBAt` at `m = mag`);
* arithmetic: `G_shift_le`, `G_two_mul`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsEnc
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH QecReliability.Trans.Hash

/-! ## Lifting -/

theorem FnBAt.lift {a b : Ty} {F : FnSig a b} {x : a.den} {k c k' c' : ℕ}
    (h : FnBAt (G k c) F x) (hk : k ≤ k') (hc : c ≤ c') : FnBAt (G k' c') F x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e := G_mono (m := mag a x) hk hc le_rfl
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e⟩

/-- A `PolyB` callee, at every argument, below any large enough `G K C`. -/
theorem fnBAt_P {a b : Ty} {F : FnSig a b} (h : PolyB F) :
    ∃ k c, ∀ K C, k ≤ K → c ≤ C → ∀ y, FnBAt (G K C) F y := by
  obtain ⟨k, c, hF⟩ := h
  exact ⟨k, c, fun K C hk hc y => fnBAt_of hF hk hc y⟩

/-! ## Arithmetic -/

/-- A bound at an external magnitude `M` is a bound with constant `C + M`. -/
theorem G_shift_le {k c K C M : ℕ} (hk : k ≤ K) (hc : c ≤ C) (y : ℕ) :
    G k c M ≤ G K (C + M) y := by
  rw [← G_shift]
  exact G_mono hk hc (by omega)

/-- `G k c (2 M) ≤ G (k + 1) c M`. -/
theorem G_two_mul (k c M : ℕ) : G k c (M + M) ≤ G (k + 1) c M := by
  unfold G
  rw [Function.iterate_succ_apply]
  apply adm_B0.iter_mono k
  have := B0_ge (M + c)
  omega

/-- `G k (c + M) y ≤ G (k + 1) c M` for `y ≤ M`. -/
theorem G_absorb {k c M y : ℕ} (hy : y ≤ M) : G k (c + M) y ≤ G (k + 1) c M := by
  rw [← G_shift]
  exact (G_mono le_rfl le_rfl (by omega : y + M ≤ M + M)).trans (G_two_mul k c M)

/-! ## Explicit-constant term bound for `exactSig` -/

/-- **Pointwise bound of an `exactSig` function with explicit constants.** -/
theorem fnBAt_exactP {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den) {K C : ℕ}
    (x : a.den) (hden : body.den (Env.one x) = den x)
    (hc : Tm.CallsBP (G (K + 1) C) body (Env.one x)) :
    FnBAt (G ((Tm.nodes body + 1) * (K + 1 + 1)) (C + Tm.litc body)) (exactSig i body den) x := by
  obtain ⟨h1, h2, h3, h4⟩ := Tm.boundP (adm_G (k := K + 1) (by omega) C) body (Tm.litc body)
    le_rfl (Env.one x) hc
  have he : envMag (Env.one x) = mag a x := by simp [envMag]
  rw [he] at h1 h2 h3 h4
  have hst := (adm_G (k := K + 1) (by omega) C).step (k := Tm.nodes body)
    (j := Tm.nodes body + 1) le_rfl (mag a x + Tm.litc body)
  have hi := G_iter (K + 1) C (Tm.nodes body + 1) (mag a x + Tm.litc body)
  rw [G_shift] at hi
  unfold FnBAt
  rw [exactSig_den, ← hden, exactSig_cost, exactSig_depth, exactSig_msize]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-! ## `mapEnvF` with pointwise callee bounds -/

theorem elem_leAt {a b : Ty} {F : FnSig a b} {k c : ℕ} {x : a.den} (hF : FnBAt (G k c) F x)
    {m : ℕ} (hx : mag a x ≤ m) : F.cost x + 40 ≤ G k (c + 40) m ∧ F.depth x + 40 ≤ G k (c + 40) m ∧
      F.msize x + 40 ≤ G k (c + 40) m ∧ mag b (F.den x) + 40 ≤ G k (c + 40) m := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  have e1 := G_mono (k := k) (c := c) le_rfl le_rfl hx
  have e2 := G_add_c k c 40 m
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **`Hash.mapEnvF` with callee bounds at the list elements.** -/
theorem mapEnvH_At {e a b : Ty} {F : FnSig (.prod e a) b} {k c : ℕ} (i : ℕ) (u : e.den)
    (xs : List a.den) (hF : ∀ x ∈ xs, FnBAt (G k c) F (u, x)) :
    FnBAt (G (k + 2) (c + 40)) (Hash.mapEnvF F i) (u, xs) := by
  obtain ⟨m, hm⟩ : ∃ m, mag (.prod e (.list a)) (u, xs) = m := ⟨_, rfl⟩
  have hl := env_len u xs
  unfold FnBAt
  rw [hm] at hl ⊢
  have hF' := fun x (h : x ∈ xs) => elem_leAt (hF x h) ((env_elem u h).trans hm.le)
  have Y1 := G_succ k (c + 40) m
  have Y2 : 5 * G (k + 1) (c + 40) m + 16 ≤ G (k + 2) (c + 40) m := G_succ (k + 1) (c + 40) m
  have hl0 := le_G k (c + 40) m
  have hcost := comb_le xs (fun x => F.cost (u, x) + 16) (k := k) (c := c + 40)
    (show xs.length ≤ m by omega) (fun x h => by (try dsimp only); have := (hF' x h).1; omega)
    (d := 10) (by omega)
  have hmax := maxOf_bound xs (fun x => F.depth (u, x)) (M := G k (c + 40) m)
    (fun x h => by (try dsimp only); have := (hF' x h).2.1; omega)
  have hmsz := maxOf_bound xs (fun x => F.msize (u, x)) (M := G k (c + 40) m)
    (fun x h => by (try dsimp only); have := (hF' x h).2.2.1; omega)
  have hres := mag_map_le xs (fun x => F.den (u, x)) (G k (c + 40) m)
    (fun x h => by (try dsimp only); have := (hF' x h).2.2.2; omega)
  have hres2 := len_mul_le (k := k) (c := c + 40) (show xs.length ≤ m by omega) le_rfl
  have hsz := sz_le (.list b) (xs.map (fun x => F.den (u, x)))
  have hsz2 := sz_le (.prod e (.list a)) (u, xs)
  simp only [Hash.mapEnvF_cost, Hash.mapEnvF_depth, Hash.mapEnvF_msize, Hash.mapEnvF_den]
  refine ⟨by omega, by omega, ?_, by omega⟩
  exact max_le (max_le (by omega) (by omega)) (by omega)

/-! ## `foldlF` with pointwise callee bounds -/

section Fold
variable {a b : Ty}

theorem fold_step_leAt {k c : ℕ} {F : FnSig (.prod b a) b} {acc : b.den} {x : a.den}
    (hF : FnBAt (G k c) F (acc, x)) {R m : ℕ} (hacc : mag b acc ≤ R) (hx : mag a x ≤ m) :
    F.cost (acc, x) ≤ G k c (R + m + 1) ∧ F.depth (acc, x) ≤ G k c (R + m + 1) ∧
      F.msize (acc, x) ≤ G k c (R + m + 1) ∧ mag b (F.den (acc, x)) ≤ G k c (R + m + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  have e := G_mono (k := k) (c := c) le_rfl le_rfl
    (show mag (.prod b a) (acc, x) ≤ R + m + 1 by simp only [mag_prod]; omega)
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e⟩

/-- **`foldl` with step-indexed invariant and pointwise callee bounds**, measured at any
`m ≥ mag (z, xs)`. -/
theorem foldl_At (F : FnSig (.prod b a) b) (i : ℕ) {k c kR cR : ℕ} (z : b.den)
    (xs : List a.den) (m : ℕ) (hm : mag (.prod b (.list a)) (z, xs) ≤ m) (S : ℕ → b.den → Prop)
    (hz : S 0 z)
    (hstep : ∀ x ∈ xs, ∀ n, n < xs.length → ∀ acc, S n acc → S (n + 1) (F.den (acc, x)))
    (hR : ∀ n, n ≤ xs.length → ∀ acc, S n acc → mag b acc ≤ G kR cR m)
    (hF : ∀ x ∈ xs, ∀ n, n < xs.length → ∀ acc, S n acc → FnBAt (G k c) F (acc, x)) :
    (foldlF F i).cost (z, xs) ≤ G (k + kR + 5) (c + cR + 300) m ∧
    (foldlF F i).depth (z, xs) ≤ G (k + kR + 5) (c + cR + 300) m ∧
    (foldlF F i).msize (z, xs) ≤ G (k + kR + 5) (c + cR + 300) m ∧
    mag b ((foldlF F i).den (z, xs)) ≤ G (k + kR + 5) (c + cR + 300) m := by
  have hY : G k c (G kR cR m + m + 1) ≤ G (k + kR + 2) (c + cR) m := by
    have h1 : G kR cR m + m + 1 ≤ G (kR + 1) cR m := by
      have := G_succ kR cR m; have := le_G kR cR m; omega
    exact (G_mono le_rfl le_rfl h1).trans ((G_comp k c (kR + 1) cR m).trans
      (G_mono (by omega) le_rfl le_rfl))
  generalize hRd : G kR cR m = R at hR hY
  generalize hYd : G k c (R + m + 1) = Y at hY
  have hxs : ∀ x ∈ xs, mag a x ≤ m := fun x hx => by
    have := mag_mem a hx; simp only [mag_prod] at hm; omega
  let S' : ℕ → b.den → Prop := fun n acc => n ≤ xs.length ∧ S n acc
  obtain ⟨r1, r2, r3, r4, r5⟩ := foldl_bounds_idx F S' Y Y (Y + 5 * R + 1) xs.length xs z 0
    (by omega) ⟨Nat.zero_le _, hz⟩ (by have := sz_le b z; have := hR 0 (Nat.zero_le _) z hz; omega)
    (fun x hx n hn acc hacc _ => by
      have hacc' := hR n hacc.1 acc hacc.2
      obtain ⟨f1, f2, f3, f4⟩ := fold_step_leAt (hF x hx n hn acc hacc.2) hacc' (hxs x hx)
      rw [hYd] at f1 f2 f3 f4
      have s1 := hstep x hx n hn acc hacc.2
      have := sz_le b (F.den (acc, x))
      have := hR (n + 1) (by omega) _ s1
      exact ⟨⟨by omega, s1⟩, by omega, f1, f2, by omega⟩)
  have hl := mag_list_len a xs
  have hlen : xs.length ≤ m := by simp only [mag_prod] at hm; omega
  have hsx := sz_le (.list a) xs
  have hmx : mag (.list a) xs ≤ m := by simp only [mag_prod] at hm; omega
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
  have g5 : G (k + kR + 2) (c + cR) m ≤ G (k + kR + 3) (c + cR) m :=
    G_mono (by omega) le_rfl le_rfl
  simp only [foldlF_cost, foldlF_depth, foldlF_msize, foldlF_den]
  refine ⟨by omega, by omega, by omega, ?_⟩
  have := hR _ (by omega) _ r1.2
  omega

/-- `foldl_At` at `m = mag (z, xs)`. -/
theorem foldl_FnBAt (F : FnSig (.prod b a) b) (i : ℕ) {k c kR cR : ℕ} (z : b.den)
    (xs : List a.den) (S : ℕ → b.den → Prop) (hz : S 0 z)
    (hstep : ∀ x ∈ xs, ∀ n, n < xs.length → ∀ acc, S n acc → S (n + 1) (F.den (acc, x)))
    (hR : ∀ n, n ≤ xs.length → ∀ acc, S n acc →
      mag b acc ≤ G kR cR (mag (.prod b (.list a)) (z, xs)))
    (hF : ∀ x ∈ xs, ∀ n, n < xs.length → ∀ acc, S n acc → FnBAt (G k c) F (acc, x)) :
    FnBAt (G (k + kR + 5) (c + cR + 300)) (foldlF F i) (z, xs) :=
  foldl_At F i z xs _ le_rfl S hz hstep hR hF

end Fold

end QecReliability.Trans.BoundsEnc
