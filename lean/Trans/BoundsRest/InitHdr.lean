import Trans.BoundsRest.InitMany

/-!
# Trans.BoundsRest.InitHdr: header and coordinate readers on any input

With `N = bs.length` (every bound is in the *length* of the remaining input, never in a header
value): `onesFold_bounds`, `wordFold_bounds` (the two `foldr` scans), **`hdr_bounds`**
(`hdrF`: cost `≤ 400 (N+2)²`, depth `≤ 10 N + 20`, msize `≤ 100 N + 100`), **`coord_bounds`**
(`coordF`, the same plus a constant); `hdr_rest_suffix`, `hdr_val_sz` (the value read has
encoded size `≤ 4N + 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.BoundsRest
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_cost bodySig_depth bodySig_msize)
open QecReliability.Trans.Wire

/-! ## Plain facts -/

theorem ones_le_length : ∀ bs : List Bool, ones bs ≤ bs.length
  | [] => by simp [ones]
  | b :: bs => by
    have := ones_le_length bs
    have e : ones (b :: bs) = onesStep b (ones bs) := rfl
    rw [e, List.length_cons]
    unfold onesStep; split <;> omega

theorem wordVal_lt : ∀ bs : List Bool, wordVal bs < 2 ^ bs.length
  | [] => by simp [wordVal]
  | b :: bs => by
    have := wordVal_lt bs
    have e : wordVal (b :: bs) = bitNat b (wordVal bs) := rfl
    rw [e, List.length_cons, pow_succ]
    unfold bitNat; split <;> omega

theorem sz_nat_lt_pow {v n : ℕ} (h : v < 2 ^ n) : (Ty.enc .nat v).size ≤ 4 * n + 1 := by
  have h1 := Ty.sz_nat_le v
  have h2 : v.size ≤ n := Nat.size_le.mpr h
  omega

theorem sz_bools (bs : List Bool) : (Ty.enc (.list .bool) bs).size ≤ 4 * bs.length + 1 :=
  Bounds.sz_boolList bs

theorem nat_sz_le_self (v : ℕ) : (Ty.enc .nat v).size ≤ 4 * v + 1 := Bounds.sz_nat_le_self v

section Hdr
variable (L : Wire.Lib) (h : HIx)

/-! ## The two scans -/

theorem onesStep_bounds (b : Bool) (acc : ℕ) :
    (onesStepF L h).cost (b, acc) ≤ 25 * acc.size + 40 ∧
      (onesStepF L h).depth (b, acc) ≤ acc.size + 3 ∧
      (onesStepF L h).msize (b, acc) ≤ 4 * acc.size + 12 := by
  cases b <;> simp [onesStepF, bodySig_cost, bodySig_depth, bodySig_msize, onesStepBody, tm_simp]
    <;> omega

theorem onesFold_den (bs : List Bool) : foldrDen (onesStepF L h) bs 0 = ones bs :=
  onesF_den L h bs

theorem onesFold_bounds : ∀ bs : List Bool,
    foldrCost (onesStepF L h) bs 0 ≤ bs.length * (25 * bs.length + 52) + 10 ∧
      foldrDepth (onesStepF L h) bs 0 ≤ 2 * bs.length + 4 ∧
      foldrMsize (onesStepF L h) bs 0 ≤ 2 * (Ty.enc (.list .bool) bs).size + 8 * bs.length + 20
  | [] => by simp
  | x :: xs => by
    obtain ⟨i1, i2, i3⟩ := onesFold_bounds xs
    have hk := ones_le_length xs
    rw [← onesFold_den L h] at hk
    obtain ⟨s1, s2, s3⟩ := onesStep_bounds L h x (foldrDen (onesStepF L h) xs 0)
    have hs := NatSize.size_le_self (foldrDen (onesStepF L h) xs 0)
    have hn := nat_sz_le_self (foldrDen (onesStepF L h) xs 0)
    have hb := Ty.sz_bool_le x
    have e3 := Ty.sz_list_cons .bool x xs
    have h0 : (Ty.enc .nat (0 : ℕ)).size = 1 := by show (Enc.nat 0).size = 1; rw [Enc.nat_zero]; rfl
    have h0' : (Ty.enc .nat (0 : Ty.den .nat)).size = 1 := h0
    simp only [foldrCost, foldrDepth, foldrMsize, List.length_cons, Ty.sz_prod, max_le_iff]
    try dsimp only
    have q : xs.length * (25 * xs.length + 52) + 25 * xs.length + 52 ≤
        (xs.length + 1) * (25 * (xs.length + 1) + 52) := by nlinarith
    refine ⟨by omega, ⟨by omega, by omega⟩, by omega, by omega, by omega⟩

theorem bitStep_bounds (b : Bool) (acc : ℕ) :
    (bitStepF h).cost (b, acc) ≤ 20 ∧ (bitStepF h).depth (b, acc) ≤ 1 ∧
      (bitStepF h).msize (b, acc) ≤ (Ty.enc .nat (bitNat b acc)).size + 5 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bitStepF, bodySig_cost, bitStepBody, tm_simp]
  · simp [bitStepF, bodySig_depth, bitStepBody, tm_simp]
  · simp only [bitStepF, bodySig_msize, bitStepBody, Tm.msize, Tm.den, Env.get, max_le_iff]
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    show (Enc.nat (bitNat b acc)).size ≤ (Ty.enc .nat (bitNat b acc)).size + 5
    exact Nat.le_add_right _ _

theorem wordFold_den (bs : List Bool) : foldrDen (bitStepF h) bs 0 = wordVal bs :=
  wordValF_den h bs

theorem wordFold_bounds : ∀ bs : List Bool,
    foldrCost (bitStepF h) bs 0 ≤ 32 * bs.length + 10 ∧
      foldrDepth (bitStepF h) bs 0 ≤ bs.length + 2 ∧
      foldrMsize (bitStepF h) bs 0 ≤ 2 * (Ty.enc (.list .bool) bs).size + 8 * bs.length + 20
  | [] => by simp
  | x :: xs => by
    obtain ⟨i1, i2, i3⟩ := wordFold_bounds xs
    obtain ⟨s1, s2, s3⟩ := bitStep_bounds h x (foldrDen (bitStepF h) xs 0)
    have hw := wordVal_lt xs
    rw [← wordFold_den h] at hw
    have hw2 : bitNat x (foldrDen (bitStepF h) xs 0) < 2 ^ (xs.length + 1) := by
      rw [pow_succ]; unfold bitNat; split <;> omega
    have hn := sz_nat_lt_pow hw
    have hn2 := sz_nat_lt_pow hw2
    have hb := Ty.sz_bool_le x
    have e3 := Ty.sz_list_cons .bool x xs
    have h0 : (Ty.enc .nat (0 : ℕ)).size = 1 := by show (Enc.nat 0).size = 1; rw [Enc.nat_zero]; rfl
    have h0' : (Ty.enc .nat (0 : Ty.den .nat)).size = 1 := h0
    simp only [foldrCost, foldrDepth, foldrMsize, List.length_cons, Ty.sz_prod, max_le_iff]
    try dsimp only
    refine ⟨by omega, ⟨by omega, by omega⟩, by omega, by omega, by omega⟩

/-! ## One header -/

theorem hdr_arith {N k r t : ℕ} (hk : k ≤ N) (hr : r ≤ N) (ht : t ≤ N) (sk : k.size ≤ N)
    (sk1 : (k + 1).size ≤ N + 1) {oc wc : ℕ} (hoc : oc ≤ N * (25 * N + 52) + 10)
    (hwc : wc ≤ 32 * t + 10) :
    1 + 1 + 1 + oc + (1 + (25 * k.size + 25) + 1 + 1 + 50 * (N + 1) * ((k + 1).size + 1) +
      (1 + 1 + 1 + 50 * (r + 1) * (k.size + 1) + 1 + 1 + wc +
        (1 + 1 + 1 + 50 * (r + 1) * (k.size + 1)) + 1) + 1) + 1 + 2 ≤ 400 * ((N + 2) * (N + 2)) := by
  have m1 : 50 * (N + 1) * ((k + 1).size + 1) ≤ 50 * ((N + 2) * (N + 2)) := by
    have := Nat.mul_le_mul (show N + 1 ≤ N + 2 by omega) (show (k + 1).size + 1 ≤ N + 2 by omega)
    nlinarith
  have m2 : 50 * (r + 1) * (k.size + 1) ≤ 50 * ((N + 2) * (N + 2)) := by
    have := Nat.mul_le_mul (show r + 1 ≤ N + 2 by omega) (show k.size + 1 ≤ N + 2 by omega)
    nlinarith
  have m3 : N * (25 * N + 52) ≤ 52 * ((N + 2) * (N + 2)) := by nlinarith
  have m4 : N + 2 ≤ (N + 2) * (N + 2) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **One header**, on any input of length `N`. -/
theorem hdr_bounds (bs : List Bool) :
    (hdrF L h).cost bs ≤ 400 * ((bs.length + 2) * (bs.length + 2)) ∧
      (hdrF L h).depth bs ≤ 10 * bs.length + 20 ∧
      (hdrF L h).msize bs ≤ 100 * bs.length + 100 := by
  have hk := ones_le_length bs
  rw [← onesFold_den L h] at hk
  obtain ⟨o1, o2, o3⟩ := onesFold_bounds L h bs
  have hS := sz_bools bs
  have h0 : (Ty.enc .nat (0 : ℕ)).size = 1 := by show (Enc.nat 0).size = 1; rw [Enc.nat_zero]; rfl
  have h0' : (Ty.enc .nat (0 : Ty.den .nat)).size = 1 := h0
  refine ⟨?_, ?_, ?_⟩
  · simp only [hdrF, bodySig_cost, hdrBody, Tm.cost, Tm.den, Env.get, foldrF_cost, foldrF_den,
      dropF_cost, dropF_den, takeF_cost, takeF_den, succF_cost, succF_den, onesF, wordValF]
    generalize foldrDen (onesStepF L h) bs 0 = k at hk o1 ⊢
    generalize foldrCost (onesStepF L h) bs 0 = oc at o1 ⊢
    obtain ⟨w1, -, -⟩ := wordFold_bounds h (List.take k (List.drop (k + 1) bs))
    generalize foldrCost (bitStepF h) (List.take k (List.drop (k + 1) bs)) 0 = wc at w1 ⊢
    have hr : (List.drop (k + 1) bs).length ≤ bs.length := by simp only [List.length_drop]; omega
    have ht : (List.take k (List.drop (k + 1) bs)).length ≤ bs.length := by
      simp only [List.length_take, List.length_drop]; omega
    exact hdr_arith hk hr ht ((NatSize.size_le_self k).trans hk)
      ((NatSize.size_le_self (k + 1)).trans (by omega)) o1 w1
  · simp only [hdrF, bodySig_depth, hdrBody, Tm.depth, Tm.den, Env.get, foldrF_depth, foldrF_den,
      dropF_depth, dropF_den, takeF_depth, takeF_den, succF_depth, succF_den, onesF, wordValF]
    generalize foldrDen (onesStepF L h) bs 0 = k at hk o2 ⊢
    obtain ⟨-, w2, -⟩ := wordFold_bounds h (List.take k (List.drop (k + 1) bs))
    have hr : (List.drop (k + 1) bs).length ≤ bs.length := by simp only [List.length_drop]; omega
    have ht : (List.take k (List.drop (k + 1) bs)).length ≤ bs.length := by
      simp only [List.length_take, List.length_drop]; omega
    have s1 := (NatSize.size_le_self k).trans hk
    have s2 := NatSize.size_le_self (k + 1)
    omega
  · simp only [hdrF, bodySig_msize, hdrBody, Tm.msize, Tm.den, Env.get, foldrF_msize, foldrF_den,
      dropF_msize, dropF_den, takeF_msize, takeF_den, succF_msize, succF_den, onesF, wordValF,
      Ty.sz_prod]
    try dsimp only
    generalize foldrDen (onesStepF L h) bs 0 = k at hk o3 ⊢
    obtain ⟨-, -, w3⟩ := wordFold_bounds h (List.take k (List.drop (k + 1) bs))
    have hw := wordVal_lt (List.take k (List.drop (k + 1) bs))
    rw [← wordFold_den h] at hw
    have hv := sz_nat_lt_pow hw
    have hr : (List.drop (k + 1) bs).length ≤ bs.length := by simp only [List.length_drop]; omega
    have ht : (List.take k (List.drop (k + 1) bs)).length ≤ bs.length := by
      simp only [List.length_take, List.length_drop]; omega
    have hr2 : (List.drop k (List.drop (k + 1) bs)).length ≤ bs.length := by
      simp only [List.length_drop]; omega
    have z1 := sz_bools (List.drop (k + 1) bs)
    have z2 := sz_bools (List.take k (List.drop (k + 1) bs))
    have z3 := sz_bools (List.drop k (List.drop (k + 1) bs))
    have n1 := nat_sz_le_self k
    have n2 := nat_sz_le_self (k + 1)
    have s1 := (NatSize.size_le_self k).trans hk
    have s2 := NatSize.size_le_self (k + 1)
    simp only [max_le_iff]
    repeat' apply And.intro
    all_goals omega

theorem hdr_suffix (bs : List Bool) : (hdr bs).2 <:+ bs := by
  unfold hdr
  exact (List.drop_suffix _ _).trans (List.drop_suffix _ _)

theorem hdr_val_sz (bs : List Bool) : (Ty.enc .nat (hdr bs).1).size ≤ 4 * bs.length + 1 := by
  unfold hdr
  have hw := wordVal_lt ((bs.drop (ones bs + 1)).take (ones bs))
  have : ((bs.drop (ones bs + 1)).take (ones bs)).length ≤ bs.length := by
    simp only [List.length_take, List.length_drop]; omega
  have h2 : 2 ^ ((bs.drop (ones bs + 1)).take (ones bs)).length ≤ 2 ^ bs.length :=
    Nat.pow_le_pow_right (by omega) this
  exact sz_nat_lt_pow (by omega)

/-! ## One coordinate -/

theorem coord_bounds (bs : List Bool) :
    (coordF L h).cost bs ≤ 400 * ((bs.length + 2) * (bs.length + 2)) + 20 ∧
      (coordF L h).depth bs ≤ 10 * bs.length + 22 ∧
      (coordF L h).msize bs ≤ 120 * bs.length + 200 := by
  cases bs with
  | nil => simp [coordF, bodySig_cost, bodySig_depth, bodySig_msize, coordBody, tm_simp]
  | cons b tl =>
    obtain ⟨c1, c2, c3⟩ := hdr_bounds L h tl
    have hv := hdr_val_sz tl
    have hs := sz_bools (hdr tl).2
    have hsl := (hdr_suffix tl).length_le
    have hb := Ty.sz_bool_le b
    have hd := hdrF_den L h tl
    have m : (tl.length + 2) * (tl.length + 2) ≤ (tl.length + 1 + 2) * (tl.length + 1 + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have ec : (coordF L h).cost (b :: tl) =
        1 + (1 + (hdrF L h).cost tl + (1 + (1 + 1) + 1 + (1 + 1) + 1) + 1) + 1 + 2 := rfl
    have ed : (coordF L h).depth (b :: tl) =
        max 0 (max (max 0 ((hdrF L h).depth tl)) (max (max (max 0 0) 0) 0)) + 1 := rfl
    have em : (coordF L h).msize (b :: tl) =
        max 0 (max (max 0 ((hdrF L h).msize tl))
          (max (max (max (max 0 0) (Ty.enc (.prod .bool .nat) (b, ((hdrF L h).den tl).1)).size) 0)
            (Ty.enc (.prod (.prod .bool .nat) (.list .bool))
              ((b, ((hdrF L h).den tl).1), ((hdrF L h).den tl).2)).size)) := rfl
    rw [hd, Bounds.shape2, Bounds.shape2, Bounds.shape2] at em
    try simp only [List.length_cons]
    refine ⟨by rw [ec]; omega, by rw [ed]; omega, ?_⟩
    rw [em]
    simp only [max_le_iff]
    repeat' apply And.intro
    all_goals omega

end Hdr

end QecReliability.Trans.BoundsRest
