import Trans.BoundsEnc.Gates

/-!
# Trans.BoundsEnc.Amp: the amplifier for a fixed walk length

The power-graph rotation `powRotF` walks `K` steps and accumulates the reversed port word
`< 16^K`: it is polynomially bounded only for a bounded walk length. All bounds of this file
hold on the arguments whose walk-length component is `≤ K0` (constants depend on `K0`, through
`16^K0`, which is never evaluated):

* `lazyRotP_fst_le`, `lazyRotP_snd_lt`: the rotation's values;
* `pwFold_At` (the walk `foldlF pwStepF`), `powRotF_At`, `portRefF_At`, `ampGateF_At`,
  **`ampF_At`**: `∃ k c, ∀ x, (walk length of x) ≤ K0 → FnBAt (G k c) F x`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.BoundsEnc
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH QecReliability.Trans.Hash QecReliability.Trans.HashCallees
open QecReliability.Trans.Query.Plain

/-! ## Values of the rotation -/

theorem mggRotP_fst_le (s v p : ℕ) : (mggRotP s v p).1 ≤ v + s * s + 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp only [mggRotP, coordP, bitNat, Nat.div_zero, Nat.mod_zero, Nat.mul_zero, Nat.zero_add,
      Nat.add_zero]
    split_ifs <;> omega
  · have h1 := coordP_lt s (v / s) (v % s) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hs
    have h2 := coordP_lt s (v % s) (v / s) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hs
    have h3 := Nat.div_mul_le_self v s
    have h4 := Nat.mod_lt v hs
    have h5 : s ≤ s * s := Nat.le_mul_of_pos_left s hs
    simp only [mggRotP]
    split_ifs
    · omega
    · have h6 : coordP s (v / s) (v % s) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) * s ≤
          (s - 1) * s := Nat.mul_le_mul_right s (by omega)
      have h7 : (s - 1) * s + s = s * s := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hs]
      omega

theorem lazyRotP_fst_le (s v p : ℕ) : (lazyRotP s v p).1 ≤ v + s * s + 1 := by
  unfold lazyRotP
  split_ifs
  · exact mggRotP_fst_le s v p
  · simp only; omega

theorem lazyRotP_snd_lt (s v p : ℕ) (hp : p < 16) : (lazyRotP s v p).2 < 16 := by
  unfold lazyRotP mggRotP
  split_ifs <;> simp only <;> omega

/-! ## The walk -/

/-- Invariant of the walk after `n` steps from `(s, v, j, 0)`. -/
def WalkInv (s v j : ℕ) (n : ℕ) (acc : ℕ × ℕ × ℕ × ℕ) : Prop :=
  acc.1 = s ∧ acc.2.1 ≤ v + n * (s * s + 1) ∧ acc.2.2.1 ≤ j ∧ acc.2.2.2 + 1 ≤ 16 ^ n

theorem walkInv_step (s v j n : ℕ) (acc : ℕ × ℕ × ℕ × ℕ) (x : ℕ) (h : WalkInv s v j n acc) :
    WalkInv s v j (n + 1) (HashCallees.powStep acc x) := by
  obtain ⟨s', v', w, a⟩ := acc
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  subst h1
  have l1 := lazyRotP_fst_le s' v' (w % 16)
  have l2 := lazyRotP_snd_lt s' v' (w % 16) (Nat.mod_lt _ (by omega))
  have e1 : (n + 1) * (s' * s' + 1) = n * (s' * s' + 1) + (s' * s' + 1) := Nat.succ_mul _ _
  have e2 : 16 ^ (n + 1) = 16 ^ n * 16 := pow_succ 16 n
  have e3 := Nat.div_le_self w 16
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp only [HashCallees.powStep] <;> omega

theorem walkInv_mag (s v j K0 n : ℕ) (hn : n ≤ K0) (acc : ℕ × ℕ × ℕ × ℕ)
    (h : WalkInv s v j n acc) (m : ℕ) (hm : s + v + j ≤ m) :
    mag (.prod .nat (.prod .nat (.prod .nat .nat))) acc ≤ G 2 (K0 + 16 ^ K0 + 4) m := by
  obtain ⟨s', v', w, a⟩ := acc
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  subst h1
  have e : mag (.prod .nat (.prod .nat (.prod .nat .nat))) (s', v', w, a) =
      s' + (v' + (w + a + 1) + 1) + 1 := rfl
  rw [e]
  have q := quad_le (K0 + 16 ^ K0 + 4) m
  have p1 : 16 ^ n ≤ 16 ^ K0 := Nat.pow_le_pow_right (by omega) hn
  have p2 : n * (s' * s' + 1) ≤ K0 * ((m + 1) * (m + 1)) :=
    Nat.mul_le_mul hn (by nlinarith)
  generalize hX : (m + 1) * (m + 1) = X at q p2
  have p3 : 16 ^ K0 ≤ 16 ^ K0 * X := Nat.le_mul_of_pos_right _ (by rw [← hX]; positivity)
  have p4 : 3 * m + 3 ≤ 4 * X := by rw [← hX]; nlinarith
  have e2 : (K0 + 16 ^ K0 + 4) * X = K0 * X + 16 ^ K0 * X + 4 * X := by ring
  generalize 16 ^ K0 = P at *
  omega

/-- **The walk** `foldlF pwStepF` from `(s, v, j, 0)` over `range K`, `K ≤ K0`. -/
theorem pwFold_At (L : HashCallees.Lib) (R : RotIx) (ist ifo K0 : ℕ) :
    ∃ k c, ∀ s v j K : ℕ, K ≤ K0 →
      FnBAt (G k c) (foldlF (pwStepF L R ist) ifo) ((s, v, j, 0), List.range K) := by
  obtain ⟨k1, c1, h1⟩ := pwStepF_P L R ist
  refine ⟨k1 + 2 + 5, c1 + (K0 + 16 ^ K0 + 4) + 300, fun s v j K hK => ?_⟩
  refine foldl_FnBAt _ _ _ _ (fun n (acc : ℕ × ℕ × ℕ × ℕ) => WalkInv s v j n acc)
    ⟨rfl, by simp, le_rfl, by simp⟩ ?_ ?_ (fun x _ n _ acc _ => h1 (acc, x))
  · intro x _ n _ acc hacc
    exact walkInv_step s v j n acc x hacc
  · intro n hn acc hacc
    rw [List.length_range] at hn
    refine walkInv_mag s v j K0 n (hn.trans hK) acc hacc _ ?_
    have : mag (.prod .nat (.prod .nat (.prod .nat .nat))) ((s, v, j, 0) : ℕ × ℕ × ℕ × ℕ) =
        s + (v + (j + 0 + 1) + 1) + 1 := rfl
    simp only [mag_prod, mag_nat]
    omega

/-! ## Power rotation -/

theorem powRotF_At (L : HashCallees.Lib) (R : RotIx) (ist ifo i K0 : ℕ) :
    ∃ k c, ∀ x : T4.den, x.2.1 ≤ K0 → FnBAt (G k c) (powRotF L R ist ifo i) x := by
  obtain ⟨kf, cf, hf⟩ := pwFold_At L R ist ifo K0
  obtain ⟨kr, cr, hr⟩ := fnBAt_P (rangeF_P (i := L.range))
  refine ⟨_, _, fun x hx => fnBAt_exactP (K := kf + kr) (C := cf + cr) _ _ _ x ?_ ?_⟩
  · obtain ⟨s, K, v, j⟩ := x
    simp only [powRotBody, tm_simp, foldlF_den, foldlDen, rangeF_den, pwStepF, exactSig_den,
      powRotP, Env.one]
  · obtain ⟨s, K, v, j⟩ := x
    simp only [Tm.CallsBP, powRotBody, tm_simp, Env.one, rangeF_den, and_true, true_and]
    exact ⟨(hf s v j K hx).lift (by omega) (by omega), hr _ _ (by omega) (by omega) _⟩

/-! ## Port references -/

theorem portRefF_At (L : HashCallees.Lib) {iprot : FnSig T4 (.prod .nat .nat)} {K0 : ℕ}
    (hpr : ∃ k c, ∀ y : T4.den, y.2.1 ≤ K0 → FnBAt (G k c) iprot y)
    (hprd : ∀ x : T4.den, iprot.den x = powRotP x.1 x.2.1 x.2.2.1 x.2.2.2) (i : ℕ) :
    ∃ k c, ∀ x : T6.den, x.2.1 ≤ K0 → FnBAt (G k c) (portRefF L iprot i) x := by
  obtain ⟨kp, cp, hp⟩ := hpr
  obtain ⟨k1, c1, hlt⟩ := fnBAt_P (ltF_P (i := L.lt))
  obtain ⟨k2, c2, hadd⟩ := fnBAt_P (addF_P (i := L.add))
  obtain ⟨k3, c3, hmul⟩ := fnBAt_P (mulF_P (i := L.mul))
  obtain ⟨k4, c4, hsub⟩ := fnBAt_P (subF_P (i := L.sub))
  have e1 := hlt (kp + k1 + k2 + k3 + k4 + 1) (cp + c1 + c2 + c3 + c4) (by omega) (by omega)
  have e2 := hadd (kp + k1 + k2 + k3 + k4 + 1) (cp + c1 + c2 + c3 + c4) (by omega) (by omega)
  have e3 := hmul (kp + k1 + k2 + k3 + k4 + 1) (cp + c1 + c2 + c3 + c4) (by omega) (by omega)
  have e4 := hsub (kp + k1 + k2 + k3 + k4 + 1) (cp + c1 + c2 + c3 + c4) (by omega) (by omega)
  refine ⟨_, _, fun x hx => fnBAt_exactP (K := kp + k1 + k2 + k3 + k4)
    (C := cp + c1 + c2 + c3 + c4) _ _ _ x ?_ ?_⟩
  · obtain ⟨D, K, T, s, v, j⟩ := x
    simp only [portRefBody, tm_simp, ltF_den, addF_den, mulF_den, subF_den, hprd, portRef,
      padRef, portRefF, exactSig_den, Env.one]
    by_cases h1 : j < D <;> simp [h1]
  · obtain ⟨D, K, T, s, v, j⟩ := x
    simp only at hx
    simp only [Tm.CallsBP, portRefBody, e1, e2, e3, e4, true_and, and_true, ite_self]
    split
    · trivial
    · refine FnBAt.lift (hp _ ?_) (by omega) (by omega)
      simpa [tm_simp] using hx

/-! ## Amplifier gates -/

theorem ampGateF_At (L : HashCallees.Lib) (itb : ℕ) {ipref : FnSig T6 .nat} {K0 : ℕ}
    (hpr : ∃ k c, ∀ y : T6.den, y.2.1 ≤ K0 → FnBAt (G k c) ipref y)
    (hprd : ∀ x : T6.den, ipref.den x = portRef x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
    (i : ℕ) :
    ∃ k c, ∀ x : (Ty.prod TAEnv .nat).den, x.1.2.2.1 ≤ K0 →
      FnBAt (G k c) (ampGateF L itb ipref i) x := by
  obtain ⟨kp, cp, hp⟩ := hpr
  obtain ⟨k1, c1, hdm⟩ := fnBAt_P (divModF_P L.le L.sub L.dm)
  obtain ⟨k2, c2, hadd⟩ := fnBAt_P (addF_P (i := L.add))
  obtain ⟨k3, c3, hmul⟩ := fnBAt_P (mulF_P (i := L.mul))
  obtain ⟨k4, c4, hd2⟩ := fnBAt_P (div2F_P (i := L.div2))
  obtain ⟨k5, c5, htb⟩ := fnBAt_P (testBitF_P L itb)
  have e1 := hdm (kp + k1 + k2 + k3 + k4 + k5 + 1) (cp + c1 + c2 + c3 + c4 + c5) (by omega) (by omega)
  have e2 := hadd (kp + k1 + k2 + k3 + k4 + k5 + 1) (cp + c1 + c2 + c3 + c4 + c5) (by omega) (by omega)
  have e3 := hmul (kp + k1 + k2 + k3 + k4 + k5 + 1) (cp + c1 + c2 + c3 + c4 + c5) (by omega) (by omega)
  have e4 := hd2 (kp + k1 + k2 + k3 + k4 + k5 + 1) (cp + c1 + c2 + c3 + c4 + c5) (by omega) (by omega)
  have e5 := htb (kp + k1 + k2 + k3 + k4 + k5 + 1) (cp + c1 + c2 + c3 + c4 + c5) (by omega) (by omega)
  refine ⟨_, _, fun x hx => fnBAt_exactP (K := kp + k1 + k2 + k3 + k4 + k5)
    (C := cp + c1 + c2 + c3 + c4 + c5) _ _ _ x ?_ ?_⟩
  · obtain ⟨⟨code, D, K, T, s⟩, g⟩ := x
    simp only [ampGateBody, tm_simp, Lib.dmF_den, addF_den, mulF_den, div2F_den, testBitF_den,
      hprd, gateP, ampRef, coeffP, exactSig_den, Env.one, Tm.den_isZero, Nat.div_div_eq_div_mul]
    by_cases h0 : g % (D + D) = 0 <;> simp [h0]
  obtain ⟨⟨code, D, K, T, s⟩, g⟩ := x
  simp only at hx
  simp only [Tm.CallsBP, ampGateBody, e1, e2, e3, e4, e5, true_and, and_true, ite_self]
  split
  · refine FnBAt.lift (hp _ ?_) (by omega) (by omega)
    simpa [tm_simp] using hx
  · trivial

/-- The amplifier's gate function at its installed indices. -/
theorem gateIx_At (L : HashCallees.Lib) (I : AmpIx) (K0 : ℕ) :
    ∃ k c, ∀ x : (Ty.prod TAEnv .nat).den, x.1.2.2.1 ≤ K0 → FnBAt (G k c) (I.gateF L) x :=
  ampGateF_At L I.tb (portRefF_At L (powRotF_At L I.rot I.pstep I.pfold I.prot K0)
    (fun _ => rfl) I.pref) (fun _ => rfl) I.gate

/-- The gate map over the amplifier's gate numbers. -/
theorem gateMapIx_At (L : HashCallees.Lib) (I : AmpIx) (K0 : ℕ) :
    ∃ k c, ∀ p : (Ty.prod TAEnv (.list .nat)).den, p.1.2.2.1 ≤ K0 →
      FnBAt (G k c) (mapEnvF (I.gateF L) I.gmap) p := by
  obtain ⟨k, c, h⟩ := gateIx_At L I K0
  exact ⟨k + 2, c + 40, fun p hp => mapEnvH_At (k := k) (c := c) I.gmap p.1 p.2
    (fun x _ => h (p.1, x) hp)⟩

/-! ## The amplifier -/

/-- **The amplifier** `ampF` on arguments with walk length `≤ K0`. -/
theorem ampF_At (L : HashCallees.Lib) (I : AmpIx) (K0 : ℕ) :
    ∃ k c, ∀ x : (Ty.prod TE .nat).den, x.1.2.1 ≤ K0 → FnBAt (G k c) (ampF L I) x := by
  obtain ⟨kg, cg, hg⟩ := gateMapIx_At L I K0
  obtain ⟨k1, c1, hdm⟩ := fnBAt_P (divModF_P L.le L.sub L.dm)
  obtain ⟨k2, c2, hadd⟩ := fnBAt_P (addF_P (i := L.add))
  obtain ⟨k3, c3, hmul⟩ := fnBAt_P (mulF_P (i := L.mul))
  obtain ⟨k4, c4, hd2⟩ := fnBAt_P (div2F_P (i := L.div2))
  obtain ⟨k5, c5, hcs⟩ := fnBAt_P (csFoldF_P L.le L.succ L.mul I.cs I.csf)
  obtain ⟨k6, c6, hrg⟩ := fnBAt_P (rangeF_P (i := L.range))
  obtain ⟨k7, c7, hout⟩ := fnBAt_P (mapEnvH_P (ampOutF_P L I.out) I.omap)
  have e1 := hdm (kg + k1 + k2 + k3 + k4 + k5 + k6 + k7 + 1) (cg + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (by omega) (by omega)
  have e2 := hadd (kg + k1 + k2 + k3 + k4 + k5 + k6 + k7 + 1) (cg + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (by omega) (by omega)
  have e3 := hmul (kg + k1 + k2 + k3 + k4 + k5 + k6 + k7 + 1) (cg + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (by omega) (by omega)
  have e4 := hd2 (kg + k1 + k2 + k3 + k4 + k5 + k6 + k7 + 1) (cg + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (by omega) (by omega)
  have e5 := hcs (kg + k1 + k2 + k3 + k4 + k5 + k6 + k7 + 1) (cg + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (by omega) (by omega)
  have e6 := hrg (kg + k1 + k2 + k3 + k4 + k5 + k6 + k7 + 1) (cg + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (by omega) (by omega)
  have e7 := hout (kg + k1 + k2 + k3 + k4 + k5 + k6 + k7 + 1) (cg + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (by omega) (by omega)
  refine ⟨_, _, fun x hx => fnBAt_exactP (K := kg + k1 + k2 + k3 + k4 + k5 + k6 + k7)
    (C := cg + c1 + c2 + c3 + c4 + c5 + c6 + c7) _ _ _ x ?_ ?_⟩
  · obtain ⟨⟨D, K, code⟩, T⟩ := x
    have hcs := ceilSquare_foldl (T / D)
    simp only [ampBody, tm_simp, Lib.dmF_den, addF_den, mulF_den, div2F_den, mapEnvF_den,
      rangeF_den, foldlF_den, foldlDen, AmpIx.csF, csStepF_den', AmpIx.gateF, ampGateF,
      ampOutF, exactSig_den, Env.one, ampP, emitP, Nat.div_div_eq_div_mul, hcs]
  · obtain ⟨⟨D, K, code⟩, T⟩ := x
    simp only at hx
    simp only [Tm.CallsBP, ampBody, e1, e2, e3, e4, e5, e6, e7, true_and, and_true]
    refine FnBAt.lift (hg _ ?_) (by omega) (by omega)
    simpa [tm_simp] using hx

end QecReliability.Trans.BoundsEnc
