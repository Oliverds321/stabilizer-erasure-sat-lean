import Trans.BoundsQH.HFold

/-!
# Trans.BoundsQH.HParams: the scalar parameters of the hash program

* `dyFoldF_P`, `csFoldF_P`: the dyadic and ceil-square scans (`foldlF dyStepF`, `foldlF csStepF`)
  are `PolyB` (step-indexed accumulator invariants: the exponent/side grow by `≤ 1` per step,
  the dyadic value stays `≤ max p₀ (2T)`).
* `paramsF_on`: for fixed `base`, `den`, `paramsF` is bounded by one `G K C` at every
  `(base, den, q)` — the power scan `16^k`, `k = 256 den²`, runs on a fixed argument and enters as
  a constant. This is the `params` hypothesis of `hash_on`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Hash QecReliability.Trans.Query.Plain

theorem dyFoldF_P (ile isucc imul is i : ℕ) : PolyB (foldlF (dyStepF ile isucc imul is) i) := by
  refine foldl_polyB_idx _ _ (dyStepF_P ile isucc imul is) (kR := 1) (cR := 0) (fun z xs => ?_)
  obtain ⟨(T : ℕ), d0, (e0 : ℕ), (p0 : ℕ)⟩ := z
  refine ⟨fun n acc => (acc.1 : ℕ) = T ∧ (acc.2.2.1 : ℕ) ≤ e0 + n ∧ (acc.2.2.2 : ℕ) ≤ max p0 (2 * T),
    ⟨by simp, by simp, by simp⟩, ?_, ?_⟩
  · rintro x - n - ⟨(T' : ℕ), d, (e : ℕ), (p : ℕ)⟩ ⟨h1, h2, h3⟩
    have h1' : T' = T := h1
    have h2' : e ≤ e0 + n := h2
    have h3' : p ≤ max p0 (2 * T) := h3
    subst h1'
    simp only [dyStepF, exactSig_den, dyStep]
    split_ifs with hd hle
    · exact ⟨rfl, show e ≤ e0 + (n + 1) by omega, h3'⟩
    · exact ⟨rfl, show e ≤ e0 + (n + 1) by omega, h3'⟩
    · refine ⟨rfl, show e + 1 ≤ e0 + (n + 1) by omega, ?_⟩
      show 2 * p ≤ max p0 (2 * T')
      exact le_trans (by omega) (le_max_right _ _)
  · rintro n hn ⟨(T' : ℕ), d, (e : ℕ), (p : ℕ)⟩ ⟨h1, h2, h3⟩
    have h1' : T' = T := h1
    have h2' : e ≤ e0 + n := h2
    have h3' : p ≤ p0 + 2 * T := h3.trans (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
    subst h1'
    have hl := mag_list_len .nat xs
    have e : mag (.prod .nat (.prod .bool (.prod .nat .nat))) (T', d, e, p) = T' + (1 + (e + p + 1) + 1) + 1 :=
      rfl
    have e2 : mag (.prod (.prod .nat (.prod .bool (.prod .nat .nat))) (.list .nat)) ((T', d0, e0, p0), xs) =
        T' + (1 + (e0 + p0 + 1) + 1) + 1 + mag (.list .nat) xs + 1 := rfl
    rw [e, e2]
    generalize hm : T' + (1 + (e0 + p0 + 1) + 1) + 1 + mag (.list .nat) xs + 1 = m
    have g1 : 5 * (m + 0) + 16 ≤ G 1 0 m := G_succ 0 0 m
    omega

theorem csFoldF_P (ile isucc imul is i : ℕ) : PolyB (foldlF (csStepF ile isucc imul is) i) := by
  refine foldl_polyB_idx _ _ (csStepF_P ile isucc imul is) (kR := 1) (cR := 0) (fun z xs => ?_)
  obtain ⟨(N : ℕ), d0, (s0 : ℕ)⟩ := z
  refine ⟨fun n acc => (acc.1 : ℕ) = N ∧ (acc.2.2 : ℕ) ≤ s0 + n, ⟨by simp, by simp⟩, ?_, ?_⟩
  · rintro x - n - ⟨(N' : ℕ), d, (s : ℕ)⟩ ⟨h1, h2⟩
    have h1' : N' = N := h1
    have h2' : s ≤ s0 + n := h2
    subst h1'
    simp only [csStepF, exactSig_den, csStep]
    split_ifs
    · exact ⟨rfl, show s ≤ s0 + (n + 1) by omega⟩
    · exact ⟨rfl, show s ≤ s0 + (n + 1) by omega⟩
    · exact ⟨rfl, show s + 1 ≤ s0 + (n + 1) by omega⟩
  · rintro n hn ⟨(N' : ℕ), d, (s : ℕ)⟩ ⟨h1, h2⟩
    have h1' : N' = N := h1
    have h2' : s ≤ s0 + n := h2
    subst h1'
    have hl := mag_list_len .nat xs
    have e : mag (.prod .nat (.prod .bool .nat)) (N', d, s) = N' + (1 + s + 1) + 1 := rfl
    have e2 : mag (.prod (.prod .nat (.prod .bool .nat)) (.list .nat)) ((N', d0, s0), xs) =
        N' + (1 + s0 + 1) + 1 + mag (.list .nat) xs + 1 := rfl
    rw [e, e2]
    generalize hm : N' + (1 + s0 + 1) + 1 + mag (.list .nat) xs + 1 = m
    have g1 : 5 * (m + 0) + 16 ≤ G 1 0 m := G_succ 0 0 m
    omega


/-- The power scan is called at one fixed argument once `den` is fixed. -/
abbrev pwArg (den : ℕ) : (Ty.prod (.prod .nat .nat) (.list .nat)).den :=
  ((16, 1), List.range (256 * (den * den)))

/-- **`params` at fixed `(base, den)`.** -/
theorem paramsF_on (irange imul a1 a2 a3 a4 idy b1 b2 b3 b4 ics c1 c2 ipw i base den : ℕ) :
    ∃ K C, ∀ q, FnBAt (G K C) (paramsF irange imul (foldlF (dyStepF a1 a2 a3 a4) idy)
      (foldlF (csStepF b1 b2 b3 b4) ics) (foldlF (powStepF c1 c2) ipw) i) (base, den, q) := by
  obtain ⟨kd, cd, hd⟩ := dyFoldF_P a1 a2 a3 a4 idy
  obtain ⟨kc, cc, hc⟩ := csFoldF_P b1 b2 b3 b4 ics
  set PW := foldlF (powStepF c1 c2) ipw
  set cpw := PW.cost (pwArg den) + PW.depth (pwArg den) + PW.msize (pwArg den) +
    mag (.prod .nat .nat) (PW.den (pwArg den))
  set K := kd + kc + 2
  set C := cd + cc + cpw + 300
  have ed : ∀ y M, FnBAtE (G (K + 1) C) (foldlF (dyStepF a1 a2 a3 a4) idy) y M := fun y M =>
    fnBAtE_of hd (by omega) (by omega) y M
  have ec : ∀ y M, FnBAtE (G (K + 1) C) (foldlF (csStepF b1 b2 b3 b4) ics) y M := fun y M =>
    fnBAtE_of hc (by omega) (by omega) y M
  have em : ∀ y M, FnBAtE (G (K + 1) C) (mulF imul) y M := fun y M =>
    fnBAtE_of (mulF_B imul) (by omega) (by omega) y M
  have er : ∀ y M, FnBAtE (G (K + 1) C) (rangeF irange) y M := fun y M =>
    fnBAtE_of (rangeF_B irange) (by omega) (by omega) y M
  have ep : ∀ M, FnBAtE (G (K + 1) C) PW (pwArg den) M := fun M => by
    have h0 : C ≤ G (K + 1) C (max (mag (Ty.prod (.prod .nat .nat) (.list .nat)) (pwArg den)) M) :=
      G_const le_rfl
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨K', C', h⟩ := fnBOn_of_bodyE (K := K) (C := C) (paramsF irange imul
      (foldlF (dyStepF a1 a2 a3 a4) idy) (foldlF (csStepF b1 b2 b3 b4) ics) PW i) (paramsBody irange imul
      (foldlF (dyStepF a1 a2 a3 a4) idy) (foldlF (csStepF b1 b2 b3 b4) ics) PW)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun x => by
      obtain ⟨base, den, q⟩ := x
      have e1 : (fun acc x => dyStep acc (x : ℕ)) = dyStep := rfl
      have e2 : (fun acc x => csStep acc (x : ℕ)) = csStep := rfl
      have e3 : (fun acc x => powStep acc (x : ℕ)) = powStep := rfl
      rw [eq_comm]
      simp only [paramsF, exactSig_den, PW, paramsBody, Tm.den, Env.get, Env.one, mulF_den,
        rangeF_den, foldlF_den, foldlDen, dyStepF, csStepF, powStepF, exactSig_den, e1, e2, e3,
        dy_fst, dy_snd, ceilSquare_foldl, pow16]
      simp only [params, Params.tuple, UniformAdapter.walkClock, UniformAdapter.dyadicValue]
      ring_nf)
    (fun x => x.1 = base ∧ x.2.1 = den) (fun x hx => by
      obtain ⟨b', d', q⟩ := x
      obtain ⟨rfl, rfl⟩ := hx
      simp only [Tm.CallsBE, paramsBody, ed, ec, em, er, true_and, and_true]
      exact ep _)
  exact ⟨K', C', fun q => h _ ⟨rfl, rfl⟩⟩

end QecReliability.Trans.BoundsQH
