import Trans.HashCallees.MGG
import Trans.Query.Bounds

/-!
# Trans.HashCallees.MGGBounds: closed-form bounds for the neighbour oracle

Bounds in the bit lengths of the arguments (`T = n.size + a.size + b.size + 3` etc.):
`coordF_cost/depth/msize`: `600 T²`, `4T + 10`, `20T + 50`;
`mggRotF_cost/depth/msize` (`n > 0`): `5000 T²`, `12T + 40`, `100T + 300`;
**`nbrF_cost/depth/msize`** (all arguments): `6000 T²`, `12T + 50`, `100T + 300`
with `T = s.size + v.size + i.size + 3`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.HashCallees
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.Trans.Hash

theorem coordP_lt (n a b : ℕ) (c inv : Bool) (hn : 0 < n) : coordP n a b c inv < n := by
  unfold coordP; split_ifs <;> exact Nat.mod_lt _ hn

theorem size_mod_le (v n : ℕ) (hn : 0 < n) : (v % n).size ≤ n.size :=
  size_mono (Nat.mod_lt v hn).le

theorem coordF_cost (L : Lib) (i n a b : ℕ) (c inv : Bool) :
    (coordF L i).cost (n, a, b, c, inv) ≤ 600 * (n.size + a.size + b.size + 3) ^ 2 := by
  have hb := size_bitNat_le c b
  have hn2 := size_bitNat_le false n
  have hn3 := size_double_le n
  have h1 := size_add_le' a (bitNat c b)
  have h2 := size_add_le' a (bitNat false n)
  have h2' := size_add_le' a (2 * n)
  have h3 := size_sub_le (a + bitNat false n) (bitNat c b)
  have h3' := size_sub_le (a + 2 * n) (bitNat c b)
  simp only [coordF, exactSig_cost]
  have p1 : ((a + bitNat c b).size + 1) * (n.size + 2) ≤
      (n.size + a.size + b.size + 3) * (n.size + a.size + b.size + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have p2 : ((a + 2 * n - bitNat c b).size + 1) * (n.size + 2) ≤
      (n.size + a.size + b.size + 3) * (n.size + a.size + b.size + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  cases inv <;> tm_unfold [coordBody, Lib.dmF, divModF_cost, addF_cost, subF_cost, addF_den,
    subF_den, divModF_den] <;> nlinarith

theorem coordF_depth (L : Lib) (i n a b : ℕ) (c inv : Bool) :
    (coordF L i).depth (n, a, b, c, inv) ≤ 4 * (n.size + a.size + b.size + 3) + 10 := by
  have hb := size_bitNat_le c b
  have hn2 := size_bitNat_le false n
  have hn3 := size_double_le n
  have h1 := size_add_le' a (bitNat c b)
  have h2 := size_add_le' a (bitNat false n)
  have h2' := size_add_le' a (2 * n)
  have h3 := size_sub_le (a + bitNat false n) (bitNat c b)
  have h3' := size_sub_le (a + 2 * n) (bitNat c b)
  simp only [coordF, exactSig_depth]
  cases inv <;> tm_unfold [coordBody, Lib.dmF, divModF_depth, addF_depth, subF_depth, addF_den,
    subF_den, divModF_den] <;> omega

theorem coordF_msize (L : Lib) (i n a b : ℕ) (c inv : Bool) :
    (coordF L i).msize (n, a, b, c, inv) ≤ 20 * (n.size + a.size + b.size + 3) + 50 := by
  simp only [coordF, exactSig_msize]
  cases inv <;> tm_unfold [coordBody, Lib.dmF, divModF_msize, addF_msize, subF_msize, addF_den,
    subF_den, divModF_den] <;>
  · have hb := size_bitNat_le c b
    have hn3 := size_double_le n
    have h1 := size_add_le' a (bitNat c b)
    have h2' := size_add_le' a (2 * n)
    have h3' := size_sub_le (a + 2 * n) (bitNat c b)
    have e1 := Enc.nat_size_le a
    have e2 := Enc.nat_size_le n
    have e3 := Enc.nat_size_le (bitNat c b)
    have e4 := Enc.nat_size_le (2 * n)
    have e5 := Enc.nat_size_le (a + bitNat c b)
    have e6 := Enc.nat_size_le (a + 2 * n)
    have e7 := Enc.nat_size_le (a + 2 * n - bitNat c b)
    omega

theorem coordP_size (n a b : ℕ) (c inv : Bool) (hn : 0 < n) : (coordP n a b c inv).size ≤ n.size :=
  size_mono (coordP_lt n a b c inv hn).le

set_option maxHeartbeats 2000000 in
/-- Bounds of `mggRotF` with `T = n.size + v.size + p.size + 3`. -/
theorem mggRotF_cost (L : Lib) (icoord i n v p : ℕ) (hn : 0 < n) :
    (mggRotF L icoord i).cost (n, v, p) ≤ 5000 * (n.size + v.size + p.size + 3) ^ 2 := by
  have hx : (v / n).size ≤ v.size := size_div_le v n
  have hy : (v % n).size ≤ n.size := size_mod_le v n hn
  have hcA := coordP_size n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hn
  have hcB := coordP_size n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hn
  have dA : (coordF L icoord).den (n, v / n, v % n, decide (p / 2 / 2 % 2 = 1), decide (p % 2 = 1)) =
      coordP n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) := rfl
  have dB : (coordF L icoord).den (n, v % n, v / n, decide (p / 2 / 2 % 2 = 1), decide (p % 2 = 1)) =
      coordP n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) := rfl
  have s1 : (v / n * n).size ≤ v.size := size_mono (Nat.div_mul_le_self v n)
  have s2 := size_mul_le (coordP n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))) n
  have kA := coordF_cost L icoord n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))
  have kB := coordF_cost L icoord n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))
  have sA : (n.size + (v / n).size + (v % n).size + 3) ^ 2 ≤ (2 * (n.size + v.size + p.size + 3)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have sB : (n.size + (v % n).size + (v / n).size + 3) ^ 2 ≤ (2 * (n.size + v.size + p.size + 3)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hdm : (v.size + 1) * (n.size + 2) ≤ (n.size + v.size + p.size + 3) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have m1 := mulCost_le (v / n) n (v.size + n.size) (by omega)
  have m2 := mulCost_le (coordP n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))) n
    (2 * n.size + v.size) (by omega)
  have m4 : (2 * n.size + v.size + 1) * (2 * n.size + v.size + 1) ≤
      (2 * (n.size + v.size + p.size + 3)) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have m3 : (v.size + n.size + 1) * (v.size + n.size + 1) ≤ (n.size + v.size + p.size + 3) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  simp only [mggRotF, exactSig_cost]
  tm_unfold [mggRotBody, Lib.dmF, divModF_cost, addF_cost, mulF_cost, predF_cost, succF_cost,
    oddF_cost, div2F_cost, divModF_den, oddF_den, div2F_den, mulF_den]
  (try rw [dA]); (try rw [dB])
  split_ifs <;> nlinarith

theorem mggRotF_depth (L : Lib) (icoord i n v p : ℕ) (hn : 0 < n) :
    (mggRotF L icoord i).depth (n, v, p) ≤ 12 * (n.size + v.size + p.size + 3) + 40 := by
  have hx : (v / n).size ≤ v.size := size_div_le v n
  have hy : (v % n).size ≤ n.size := size_mod_le v n hn
  have hcA := coordP_size n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hn
  have hcB := coordP_size n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hn
  have dA : (coordF L icoord).den (n, v / n, v % n, decide (p / 2 / 2 % 2 = 1), decide (p % 2 = 1)) =
      coordP n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) := rfl
  have dB : (coordF L icoord).den (n, v % n, v / n, decide (p / 2 / 2 % 2 = 1), decide (p % 2 = 1)) =
      coordP n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) := rfl
  have s1 : (v / n * n).size ≤ v.size := size_mono (Nat.div_mul_le_self v n)
  have s2 := size_mul_le (coordP n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))) n
  have kA := coordF_depth L icoord n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))
  have kB := coordF_depth L icoord n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))
  simp only [mggRotF, exactSig_depth]
  tm_unfold [mggRotBody, Lib.dmF, divModF_depth, addF_depth, mulF_depth, predF_depth, succF_depth,
    oddF_depth, div2F_depth, divModF_den, oddF_den, div2F_den, mulF_den]
  (try rw [dA]); (try rw [dB])
  split_ifs <;> omega

set_option maxHeartbeats 1000000 in
theorem mggRotF_msize (L : Lib) (icoord i n v p : ℕ) (hn : 0 < n) :
    (mggRotF L icoord i).msize (n, v, p) ≤ 100 * (n.size + v.size + p.size + 3) + 300 := by
  simp only [mggRotF, exactSig_msize]
  simp only [mggRotBody, tm_simp, Ty.enc_prod, Ty.enc_nat, Ty.enc_bool, Val.size_cons, Lib.dmF,
    divModF_msize, addF_msize, mulF_msize, predF_msize, succF_msize, oddF_msize, div2F_msize,
    divModF_den, oddF_den, div2F_den, mulF_den, addF_den, predF_den, succF_den, Env.one,
    max_le_iff] <;>
  · have hx : (v / n).size ≤ v.size := size_div_le v n
    have hy : (v % n).size ≤ n.size := size_mod_le v n hn
    have hcA := coordP_size n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hn
    have hcB := coordP_size n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hn
    have dA : (coordF L icoord).den (n, v / n, v % n, decide (p / 2 / 2 % 2 = 1), decide (p % 2 = 1)) =
      coordP n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) := rfl
    have dB : (coordF L icoord).den (n, v % n, v / n, decide (p / 2 / 2 % 2 = 1), decide (p % 2 = 1)) =
      coordP n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) := rfl
    have s1 : (v / n * n).size ≤ v.size := size_mono (Nat.div_mul_le_self v n)
    have s2 := size_mul_le (coordP n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))) n
    have kA := coordF_msize L icoord n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))
    have kB := coordF_msize L icoord n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))
    (try rw [dA]); (try rw [dB])
    split_ifs <;> (strip_mdata; size_bounds; omega)

set_option maxHeartbeats 1000000 in
/-- **Cost of the neighbour oracle**: quadratic in the bit length `T = s.size + v.size + i.size + 3`. -/
theorem nbrF_cost (L : Lib) (irot icoord i s v p : ℕ) :
    (nbrF L irot icoord i).cost (s, v, p) ≤ 6000 * (s.size + v.size + p.size + 3) ^ 2 := by
  have m1 := mulCost_le s s (s.size + s.size) le_rfl
  have m2 : (s.size + s.size + 1) * (s.size + s.size + 1) ≤ 4 * (s.size + v.size + p.size + 3) ^ 2 := by
    have := Nat.mul_le_mul (show s.size + s.size + 1 ≤ 2 * (s.size + v.size + p.size + 3) by omega)
      (show s.size + s.size + 1 ≤ 2 * (s.size + v.size + p.size + 3) by omega)
    nlinarith
  have ss := size_mul_le s s
  have h3 : (3 : ℕ).size ≤ 3 := size_le_self 3
  have h16 : (16 : ℕ).size ≤ 16 := size_le_self 16
  have h8 : (8 : ℕ).size ≤ 8 := size_le_self 8
  have hT : 3 * (s.size + v.size + p.size + 3) ≤ (s.size + v.size + p.size + 3) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega)
  have hT9 : 9 ≤ (s.size + v.size + p.size + 3) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul (show 3 ≤ _ by omega) (show 3 ≤ _ by omega)
  simp only [nbrF, exactSig_cost]
  tm_unfold [nbrBody, leF_cost, ltF_cost, mulF_cost, mulF_den, leF_den, ltF_den]
  have e3 := Enc.nat_size_le 3
  have e16 := Enc.nat_size_le 16
  have e8 := Enc.nat_size_le 8
  have hss : (s * s).size ≤ s.size + s.size := size_mul_le s s
  by_cases hs : 3 ≤ s
  · have hr := mggRotF_cost L icoord irot s v p (by omega)
    split_ifs <;> linarith
  · split_ifs <;> linarith

theorem nbrF_depth (L : Lib) (irot icoord i s v p : ℕ) :
    (nbrF L irot icoord i).depth (s, v, p) ≤ 12 * (s.size + v.size + p.size + 3) + 50 := by
  have ss := size_mul_le s s
  have h3 : (3 : ℕ).size ≤ 3 := size_le_self 3
  have h16 : (16 : ℕ).size ≤ 16 := size_le_self 16
  have h8 : (8 : ℕ).size ≤ 8 := size_le_self 8
  simp only [nbrF, exactSig_depth]
  tm_unfold [nbrBody, leF_depth, ltF_depth, mulF_depth, mulF_den, leF_den, ltF_den]
  by_cases hs : 3 ≤ s
  · have hr := mggRotF_depth L icoord irot s v p (by omega)
    split_ifs <;> omega
  · split_ifs <;> omega

set_option maxHeartbeats 1000000 in
theorem nbrF_msize (L : Lib) (irot icoord i s v p : ℕ) :
    (nbrF L irot icoord i).msize (s, v, p) ≤ 100 * (s.size + v.size + p.size + 3) + 300 := by
  have ss := size_mul_le s s
  have h3 : (3 : ℕ).size ≤ 3 := size_le_self 3
  have h16 : (16 : ℕ).size ≤ 16 := size_le_self 16
  have h8 : (8 : ℕ).size ≤ 8 := size_le_self 8
  have e3 := Enc.nat_size_le 3
  have e16 := Enc.nat_size_le 16
  have e8 := Enc.nat_size_le 8
  simp only [nbrF, exactSig_msize]
  by_cases c1 : 3 ≤ s <;> by_cases c2 : v < s * s <;> by_cases c3 : p < 16 <;>
    by_cases c4 : p < 8 <;>
    simp only [nbrBody, tm_simp, Ty.enc_prod, Ty.enc_nat, Ty.enc_bool, Val.size_cons, leF_msize,
      ltF_msize, mulF_msize, mulF_den, leF_den, ltF_den, Env.one, max_le_iff, den_and, c1, c2, c3,
      c4, decide_true, decide_false, Bool.true_and, Bool.false_and, if_true, if_false,
      Bool.false_eq_true, Nat.zero_max, ↓reduceIte] <;>
    (try have hr := mggRotF_msize L icoord irot s v p (by omega)) <;>
    (strip_mdata; size_bounds; omega)

/-! ## In the magnitude form of `Trans/Query/Bounds.lean` -/

theorem coordP_le (n a b : ℕ) (c inv : Bool) (hn : 0 < n) : coordP n a b c inv + 1 ≤ n :=
  coordP_lt n a b c inv hn

theorem nbrP_le (s v p : ℕ) : nbrP s v p ≤ s * s := by
  unfold nbrP lazyRotP
  split_ifs with h h8
  · have hs : 0 < s := by omega
    have hx := coordP_le s (v / s) (v % s) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hs
    have hy := coordP_le s (v % s) (v / s) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)) hs
    have hvs : v / s < s := (Nat.div_lt_iff_lt_mul hs).mpr h.2.1
    have hm : v % s < s := Nat.mod_lt v hs
    simp only [mggRotP]
    split_ifs
    · have := Nat.mul_le_mul_right s (show v / s + 1 ≤ s by omega); nlinarith
    · have := Nat.mul_le_mul_right s hx; nlinarith
  · exact h.2.1.le
  · exact Nat.zero_le _

/-- **`nbrF` in the magnitude form** (`FnB`, `Trans/Query/Bounds.lean`): all four quantities
are `≤ 6000 (m + 4)²` for an argument of magnitude `m`. -/
theorem nbrF_FnB (L : Lib) (irot icoord i : ℕ) :
    Query.Bound.FnB (fun m => 6000 * (m + 4) ^ 2) (nbrF L irot icoord i) := by
  rintro ⟨(s : ℕ), (v : ℕ), (p : ℕ)⟩
  have hs := size_le_self s
  have hv := size_le_self v
  have hp := size_le_self p
  have hm : Query.Bound.mag (.prod .nat (.prod .nat .nat)) (s, v, p) = s + (v + p + 1) + 1 := rfl
  rw [hm]
  have hT : s.size + v.size + p.size + 3 ≤ s + (v + p + 1) + 1 + 4 := by omega
  have hT2 := Nat.pow_le_pow_left hT 2
  have h1 := nbrF_cost L irot icoord i s v p
  have h2 := nbrF_depth L irot icoord i s v p
  have h3 := nbrF_msize L irot icoord i s v p
  have h4 : Query.Bound.mag .nat ((nbrF L irot icoord i).den (s, v, p)) ≤ s * s :=
    nbrP_le s v p
  have hss : s * s ≤ (s + (v + p + 1) + 1 + 4) ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have hlin : s + (v + p + 1) + 1 + 4 ≤ (s + (v + p + 1) + 1 + 4) ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (nbrF L irot icoord i).cost (s, v, p) ≤ 6000 * (s.size + v.size + p.size + 3) ^ 2 := h1
      _ ≤ 6000 * (s + (v + p + 1) + 1 + 4) ^ 2 := Nat.mul_le_mul_left _ hT2
  · show (nbrF L irot icoord i).depth (s, v, p) ≤ 6000 * (s + (v + p + 1) + 1 + 4) ^ 2
    nlinarith [hlin, h2, hT]
  · show (nbrF L irot icoord i).msize (s, v, p) ≤ 6000 * (s + (v + p + 1) + 1 + 4) ^ 2
    nlinarith [hlin, h3, hT]
  · show Query.Bound.mag .nat ((nbrF L irot icoord i).den (s, v, p)) ≤
      6000 * (s + (v + p + 1) + 1 + 4) ^ 2
    nlinarith [hss, h4]

end QecReliability.Trans.HashCallees
