import Trans.BoundsQH.Poly
import Trans.Query.ListEnv
import Trans.Hash.FLBase

/-!
# Trans.BoundsQH.Lib: polynomial bounds of the FL library

Every function of `FL/Lib/{Nat,List}.lean` satisfies `FnB (G 2 300)` (quadratic in the
magnitude of its argument): `succF_B`, `addF_B`, `mulF_B`, `lengthF_B`, `getDF_B`, … and the
`PolyB` forms (`@[polyB]`). The higher-order combinators preserve polynomial bounds:
`mapF_B`, `filterF_B`, `flatMapF_B`, `Query.mapEnvF` (`mapEnvQ_B`), `Query.flatMapEnvF`
(`flatMapEnvQ_B`), `Hash.mapEnvF` (`mapEnvH_B`): from `FnB (G k c) F` to
`FnB (G (k+2) (c+40)) (comb F)`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound

theorem sq_ge (m : ℕ) : m + 1 ≤ (m + 1) * (m + 1) := Nat.le_mul_of_pos_left _ (by omega)

/-! ## Naturals -/

section Nat
variable (i : ℕ)

theorem succF_B : FnB (G 2 300) (succF i) := fnB_quad _ _ fun (n : ℕ) => by
  have h := natSize_le n
  have hX := sq_ge n
  simp only [mag_nat, succF_cost, succF_depth, succF_msize, succF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem predF_B : FnB (G 2 300) (predF i) := fnB_quad _ _ fun (n : ℕ) => by
  have h := natSize_le n
  have hX := sq_ge n
  simp only [mag_nat, predF_cost, predF_depth, predF_msize, predF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem addcF_B : FnB (G 2 300) (addcF i) := fnB_quad _ _ fun y => by
  obtain ⟨c, (a : ℕ), (b : ℕ)⟩ := y
  have ha := natSize_le a
  have hb := natSize_le b
  have hc := Bool.toNat_le c
  have hX := sq_ge (1 + (a + b + 1) + 1)
  simp only [mag_prod, mag_nat, mag_bool, addcF_cost, addcF_depth, addcF_msize, addcF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem subbF_B : FnB (G 2 300) (subbF i) := fnB_quad _ _ fun y => by
  obtain ⟨c, (a : ℕ), (b : ℕ)⟩ := y
  have ha := natSize_le a
  have hb := natSize_le b
  have hX := sq_ge (1 + (a + b + 1) + 1)
  simp only [mag_prod, mag_nat, mag_bool, subbF_cost, subbF_depth, subbF_msize, subbF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Binary operations with linear bounds. -/
theorem bin_quad (a b c d e r : ℕ) (hc : c ≤ 120 * (a.size + b.size) + 150)
    (hd : d ≤ a.size + b.size + 3) (he : e ≤ 4 * (a.size + b.size) + 20) (hr : r ≤ a + b + 1) :
    c ≤ 300 * ((a + b + 1 + 1) * (a + b + 1 + 1)) ∧ d ≤ 300 * ((a + b + 1 + 1) * (a + b + 1 + 1)) ∧
      e ≤ 300 * ((a + b + 1 + 1) * (a + b + 1 + 1)) ∧
      r ≤ 300 * ((a + b + 1 + 1) * (a + b + 1 + 1)) := by
  have ha := natSize_le a
  have hb := natSize_le b
  have hX := sq_ge (a + b + 1)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem addF_B : FnB (G 2 300) (addF i) := fnB_quad _ _ fun y => by
  obtain ⟨(a : ℕ), (b : ℕ)⟩ := y
  simp only [mag_prod, mag_nat, addF_cost, addF_depth, addF_msize, addF_den]
  exact bin_quad a b _ _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem subF_B : FnB (G 2 300) (subF i) := fnB_quad _ _ fun y => by
  obtain ⟨(a : ℕ), (b : ℕ)⟩ := y
  simp only [mag_prod, mag_nat, subF_cost, subF_depth, subF_msize, subF_den]
  exact bin_quad a b _ _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem leF_B : FnB (G 2 300) (leF i) := fnB_quad _ _ fun y => by
  obtain ⟨(a : ℕ), (b : ℕ)⟩ := y
  simp only [mag_prod, mag_nat, mag_bool, leF_cost, leF_depth, leF_msize, leF_den]
  exact bin_quad a b _ _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem ltF_B : FnB (G 2 300) (ltF i) := fnB_quad _ _ fun y => by
  obtain ⟨(a : ℕ), (b : ℕ)⟩ := y
  simp only [mag_prod, mag_nat, mag_bool, ltF_cost, ltF_depth, ltF_msize, ltF_den]
  exact bin_quad a b _ _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem eqF_B : FnB (G 2 300) (eqF i) := fnB_quad _ _ fun y => by
  obtain ⟨(a : ℕ), (b : ℕ)⟩ := y
  simp only [mag_prod, mag_nat, mag_bool, eqF_cost, eqF_depth, eqF_msize, eqF_den]
  exact bin_quad a b _ _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem maxF_B : FnB (G 2 300) (maxF i) := fnB_quad _ _ fun y => by
  obtain ⟨(a : ℕ), (b : ℕ)⟩ := y
  simp only [mag_prod, mag_nat, maxF_cost, maxF_depth, maxF_msize, maxF_den]
  exact bin_quad a b _ _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem minF_B : FnB (G 2 300) (minF i) := fnB_quad _ _ fun y => by
  obtain ⟨(a : ℕ), (b : ℕ)⟩ := y
  simp only [mag_prod, mag_nat, minF_cost, minF_depth, minF_msize, minF_den]
  exact bin_quad a b _ _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem div2F_B : FnB (G 2 300) (div2F i) := fnB_quad _ _ fun (n : ℕ) => by
  have hX := sq_ge n
  simp only [mag_nat, div2F_cost, div2F_depth, div2F_msize, div2F_den]
  have : n / 2 ≤ n := Nat.div_le_self n 2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem mod2F_B : FnB (G 2 300) (mod2F i) := fnB_quad _ _ fun (n : ℕ) => by
  have hX := sq_ge n
  simp only [mag_nat, mod2F_cost, mod2F_depth, mod2F_msize, mod2F_den]
  have : n % 2 < 2 := Nat.mod_lt n (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem oddF_B : FnB (G 2 300) (oddF i) := fnB_quad _ _ fun (n : ℕ) => by
  have hX := sq_ge n
  simp only [mag_nat, mag_bool, oddF_cost, oddF_depth, oddF_msize, oddF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem bitLenF_B : FnB (G 2 300) (bitLenF i) := fnB_quad _ _ fun (n : ℕ) => by
  have h := natSize_le n
  have hX := sq_ge n
  have hm : (n.size + 1) * (n.size + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e : 30 * (n.size + 1) * (n.size + 1) = 30 * ((n.size + 1) * (n.size + 1)) := by ring
  simp only [mag_nat, bitLenF_cost, bitLenF_depth, bitLenF_msize, bitLenF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem mulF_B : FnB (G 2 300) (mulF i) := fnB_quad _ _ fun y => by
  obtain ⟨(a : ℕ), (b : ℕ)⟩ := y
  have ha := natSize_le a
  have hb := natSize_le b
  have hX := sq_ge (a + b + 1)
  have hm : (a.size + 1) * (a.size + b.size + 1) ≤ (a + b + 1 + 1) * (a + b + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hab : a * b ≤ (a + b + 1 + 1) * (a + b + 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e : mulCost a b = 100 * ((a.size + 1) * (a.size + b.size + 1)) := by unfold mulCost; ring
  simp only [mag_prod, mag_nat, mulF_cost, mulF_depth, mulF_msize, mulF_den, e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end Nat

/-! ## Lists -/

section List
variable (t : Ty) (i : ℕ)

theorem lengthF_B : FnB (G 2 300) (lengthF t i) := fnB_quad _ _ fun xs => by
  have hl := mag_list_len t xs
  have hs := natSize_le xs.length
  have hX := sq_ge (mag (.list t) xs)
  have hm : (xs.length + 1) * (xs.length.size + 1) ≤ (mag (.list t) xs + 1) * (mag (.list t) xs + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : 30 * (xs.length + 1) * (xs.length.size + 1) =
      30 * ((xs.length + 1) * (xs.length.size + 1)) := by ring
  simp only [mag_nat, lengthF_cost, lengthF_depth, lengthF_msize, lengthF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem appendF_B : FnB (G 2 300) (appendF t i) := fnB_quad _ _ fun y => by
  obtain ⟨xs, ys⟩ := y
  have hl := mag_list_len t xs
  have hs := sz_le (.prod (.list t) (.list t)) (xs, ys)
  have hap := mag_append_le t xs ys
  have hX := sq_ge (mag (.list t) xs + mag (.list t) ys + 1)
  simp only [mag_prod] at hs ⊢
  simp only [appendF_cost, appendF_depth, appendF_msize, appendF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem revAppF_B : FnB (G 2 300) (revAppF t i) := fnB_quad _ _ fun y => by
  obtain ⟨xs, ys⟩ := y
  have hl := mag_list_len t xs
  have hs := sz_le (.prod (.list t) (.list t)) (xs, ys)
  have hap := mag_append_le t xs.reverse ys
  have hr := mag_reverse t xs
  have hX := sq_ge (mag (.list t) xs + mag (.list t) ys + 1)
  simp only [mag_prod] at hs ⊢
  simp only [revAppF_cost, revAppF_depth, revAppF_msize, revAppF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem reverseF_B : FnB (G 2 300) (reverseF t i) := fnB_quad _ _ fun xs => by
  have hl := mag_list_len t xs
  have hs := sz_le (.list t) xs
  have hr := mag_reverse t xs
  have hX := sq_ge (mag (.list t) xs)
  simp only [reverseF_cost, reverseF_depth, reverseF_msize, reverseF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem replicateF_B : FnB (G 2 300) (replicateF t i) := fnB_quad _ _ fun y => by
  obtain ⟨(n : ℕ), x⟩ := y
  have hs := natSize_le n
  have hr := mag_replicate t n x
  have h1 := sz_le (.list t) (List.replicate n x)
  have h2 := sz_le t x
  have hX := sq_ge (n + mag t x + 1)
  have hm : (n + 1) * (n.size + 1) ≤ (n + mag t x + 1 + 1) * (n + mag t x + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hm2 : n * (mag t x + 1) ≤ (n + mag t x + 1 + 1) * (n + mag t x + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : 40 * (n + 1) * (n.size + 1) = 40 * ((n + 1) * (n.size + 1)) := by ring
  simp only [mag_prod, mag_nat, replicateF_cost, replicateF_depth, replicateF_msize,
    replicateF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem getDF_B : FnB (G 2 300) (getDF t i) := fnB_quad _ _ fun y => by
  obtain ⟨xs, (j : ℕ), d⟩ := y
  have hl := mag_list_len t xs
  have hs := natSize_le j
  have hg := mag_getD t xs j d
  have h1 := sz_le (.list t) xs
  have h2 := sz_le t d
  have hX := sq_ge (mag (.list t) xs + (j + mag t d + 1) + 1)
  have hm : (xs.length + 1) * (j.size + 1) ≤
      (mag (.list t) xs + (j + mag t d + 1) + 1 + 1) * (mag (.list t) xs + (j + mag t d + 1) + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : 50 * (xs.length + 1) * (j.size + 1) = 50 * ((xs.length + 1) * (j.size + 1)) := by ring
  simp only [mag_prod, mag_nat, getDF_cost, getDF_depth, getDF_msize, getDF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem takeF_B : FnB (G 2 300) (takeF t i) := fnB_quad _ _ fun y => by
  obtain ⟨(n : ℕ), xs⟩ := y
  have hl := mag_list_len t xs
  have hs := natSize_le n
  have hg := mag_take t xs n
  have h1 := sz_le (.list t) xs
  have hX := sq_ge (n + mag (.list t) xs + 1)
  have hm : (xs.length + 1) * (n.size + 1) ≤
      (n + mag (.list t) xs + 1 + 1) * (n + mag (.list t) xs + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : 50 * (xs.length + 1) * (n.size + 1) = 50 * ((xs.length + 1) * (n.size + 1)) := by ring
  simp only [mag_prod, mag_nat, takeF_cost, takeF_depth, takeF_msize, takeF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem dropF_B : FnB (G 2 300) (dropF t i) := fnB_quad _ _ fun y => by
  obtain ⟨(n : ℕ), xs⟩ := y
  have hl := mag_list_len t xs
  have hs := natSize_le n
  have hg := mag_drop t xs n
  have h1 := sz_le (.list t) xs
  have hX := sq_ge (n + mag (.list t) xs + 1)
  have hm : (xs.length + 1) * (n.size + 1) ≤
      (n + mag (.list t) xs + 1 + 1) * (n + mag (.list t) xs + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : 50 * (xs.length + 1) * (n.size + 1) = 50 * ((xs.length + 1) * (n.size + 1)) := by ring
  simp only [mag_prod, mag_nat, dropF_cost, dropF_depth, dropF_msize, dropF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem mag_range' (k n : ℕ) : mag (.list .nat) (List.range' k n) ≤ n * (k + n + 1) + 1 := by
  have h := mag_list_le .nat (List.range' k n) (k + n) (fun x hx => by
    rw [List.mem_range'_1] at hx
    exact Nat.le_of_lt hx.2)
  rw [List.length_range'] at h
  exact h

theorem rangeFromF_B : FnB (G 2 300) (rangeFromF i) := fnB_quad _ _ fun y => by
  obtain ⟨(k : ℕ), (n : ℕ)⟩ := y
  have hs := natSize_le (k + n)
  have hr := mag_range' k n
  have h1 := sz_le (.list .nat) (List.range' k n)
  have hX := sq_ge (k + n + 1)
  have hm : (n + 1) * ((k + n).size + 1) ≤ (k + n + 1 + 1) * (k + n + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hm2 : n * (k + n + 1) ≤ (k + n + 1 + 1) * (k + n + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : 60 * (n + 1) * ((k + n).size + 1) = 60 * ((n + 1) * ((k + n).size + 1)) := by ring
  simp only [mag_prod, mag_nat, rangeFromF_cost, rangeFromF_depth, rangeFromF_msize,
    rangeFromF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem rangeF_B : FnB (G 2 300) (rangeF i) := fnB_quad _ _ fun (n : ℕ) => by
  have hs := natSize_le n
  have hr := mag_range' 0 n
  rw [← List.range_eq_range'] at hr
  have h1 := sz_le (.list .nat) (List.range n)
  have hX := sq_ge n
  have hm : (n + 1) * (n.size + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hm2 : n * (0 + n + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e : 60 * (n + 1) * (n.size + 1) = 60 * ((n + 1) * (n.size + 1)) := by ring
  simp only [mag_nat, rangeF_cost, rangeF_depth, rangeF_msize, rangeF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end List

/-! ## `PolyB` forms -/

section Poly
variable (t : Ty) (i : ℕ)
@[polyB] theorem succF_P : PolyB (succF i) := ⟨_, _, succF_B i⟩
@[polyB] theorem predF_P : PolyB (predF i) := ⟨_, _, predF_B i⟩
@[polyB] theorem addcF_P : PolyB (addcF i) := ⟨_, _, addcF_B i⟩
@[polyB] theorem subbF_P : PolyB (subbF i) := ⟨_, _, subbF_B i⟩
@[polyB] theorem addF_P : PolyB (addF i) := ⟨_, _, addF_B i⟩
@[polyB] theorem subF_P : PolyB (subF i) := ⟨_, _, subF_B i⟩
@[polyB] theorem leF_P : PolyB (leF i) := ⟨_, _, leF_B i⟩
@[polyB] theorem ltF_P : PolyB (ltF i) := ⟨_, _, ltF_B i⟩
@[polyB] theorem eqF_P : PolyB (eqF i) := ⟨_, _, eqF_B i⟩
@[polyB] theorem maxF_P : PolyB (maxF i) := ⟨_, _, maxF_B i⟩
@[polyB] theorem minF_P : PolyB (minF i) := ⟨_, _, minF_B i⟩
@[polyB] theorem div2F_P : PolyB (div2F i) := ⟨_, _, div2F_B i⟩
@[polyB] theorem mod2F_P : PolyB (mod2F i) := ⟨_, _, mod2F_B i⟩
@[polyB] theorem oddF_P : PolyB (oddF i) := ⟨_, _, oddF_B i⟩
@[polyB] theorem bitLenF_P : PolyB (bitLenF i) := ⟨_, _, bitLenF_B i⟩
@[polyB] theorem mulF_P : PolyB (mulF i) := ⟨_, _, mulF_B i⟩
@[polyB] theorem lengthF_P : PolyB (lengthF t i) := ⟨_, _, lengthF_B t i⟩
@[polyB] theorem appendF_P : PolyB (appendF t i) := ⟨_, _, appendF_B t i⟩
@[polyB] theorem revAppF_P : PolyB (revAppF t i) := ⟨_, _, revAppF_B t i⟩
@[polyB] theorem reverseF_P : PolyB (reverseF t i) := ⟨_, _, reverseF_B t i⟩
@[polyB] theorem replicateF_P : PolyB (replicateF t i) := ⟨_, _, replicateF_B t i⟩
@[polyB] theorem getDF_P : PolyB (getDF t i) := ⟨_, _, getDF_B t i⟩
@[polyB] theorem takeF_P : PolyB (takeF t i) := ⟨_, _, takeF_B t i⟩
@[polyB] theorem dropF_P : PolyB (dropF t i) := ⟨_, _, dropF_B t i⟩
@[polyB] theorem rangeFromF_P : PolyB (rangeFromF i) := ⟨_, _, rangeFromF_B i⟩
@[polyB] theorem rangeF_P : PolyB (rangeF i) := ⟨_, _, rangeF_B i⟩
end Poly

/-! ## Higher-order combinators -/

section Comb

theorem len_mul_le {n Y k c m : ℕ} (hn : n ≤ m) (hY : Y ≤ G k c m) :
    n * (Y + 1) + 1 ≤ G (k + 1) c m := by
  have h1 := le_G k c m
  have h2 : n * (Y + 1) ≤ G k c m * (G k c m + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h3 := G_sq k c m
  have h4 : (G k c m + 1) * (G k c m + 1) = G k c m * (G k c m + 1) + G k c m + 1 := by ring
  omega

/-- Generic list-combinator bound: `xs` of magnitude `≤ m`, per-element quantities `≤ G k c m`. -/
theorem comb_le {α : Type} (xs : List α) (f : α → ℕ) {k c m : ℕ} (hlen : xs.length ≤ m)
    (h : ∀ x ∈ xs, f x ≤ G k c m) {d : ℕ} (hd : d ≤ c) : (xs.map f).sum + d ≤ G (k + 2) c m :=
  (sum_bound xs f hlen h hd).trans (G_mono (by omega) le_rfl le_rfl)

theorem mapF_B {a b : Ty} {F : FnSig a b} {k c : ℕ} (hF : FnB (G k c) F) (i : ℕ) :
    FnB (G (k + 2) (c + 40)) (mapF F i) := fun xs => by
  set m := mag (.list a) xs
  have hl := mag_list_len a xs
  have hx : ∀ x ∈ xs, mag a x ≤ m := fun x h => by have := mag_mem a h; omega
  have hF' : ∀ x ∈ xs, F.cost x + 10 ≤ G k (c + 40) m ∧ F.depth x ≤ G k (c + 40) m ∧
      F.msize x ≤ G k (c + 40) m ∧ mag b (F.den x) + 1 ≤ G k (c + 40) m := fun x h => by
    obtain ⟨h1, h2, h3, h4⟩ := hF x
    have e1 := G_mono (k := k) (c := c) le_rfl le_rfl (hx x h)
    have e2 := G_add_c k c 40 m
    exact ⟨by omega, by omega, by omega, by omega⟩
  have Y1 := G_succ k (c + 40) m
  have Y2 : 5 * G (k + 1) (c + 40) m + 16 ≤ G (k + 2) (c + 40) m := G_succ (k + 1) (c + 40) m
  have hl0 := le_G k (c + 40) m
  have hcost := comb_le xs (fun x => F.cost x + 10) (by omega) (fun x h => (hF' x h).1)
    (d := 10) (by omega)
  have hmax := maxOf_bound xs F.depth (fun x h => (hF' x h).2.1)
  have hmsz := maxOf_bound xs F.msize (fun x h => (hF' x h).2.2.1)
  have hres := mag_map_le xs F.den (G k (c + 40) m) (fun x h => by have := (hF' x h).2.2.2; omega)
  have hres2 := len_mul_le (k := k) (c := c + 40) (show xs.length ≤ m by omega) le_rfl
  have hsz := sz_le (.list b) (xs.map F.den)
  simp only [mapF_cost, mapF_depth, mapF_msize, mapF_den]
  refine ⟨by omega, by omega, ?_, by omega⟩
  exact max_le (by omega) (by omega)

theorem filterF_B {a : Ty} {F : FnSig a .bool} {k c : ℕ} (hF : FnB (G k c) F) (i : ℕ) :
    FnB (G (k + 2) (c + 40)) (filterF F i) := fun xs => by
  set m := mag (.list a) xs
  have hl := mag_list_len a xs
  have hx : ∀ x ∈ xs, mag a x ≤ m := fun x h => by have := mag_mem a h; omega
  have hF' : ∀ x ∈ xs, F.cost x + 12 ≤ G k (c + 40) m ∧ F.depth x ≤ G k (c + 40) m ∧
      F.msize x ≤ G k (c + 40) m := fun x h => by
    obtain ⟨h1, h2, h3, h4⟩ := hF x
    have e1 := G_mono (k := k) (c := c) le_rfl le_rfl (hx x h)
    have e2 := G_add_c k c 40 m
    exact ⟨by omega, by omega, by omega⟩
  have Y1 := G_succ k (c + 40) m
  have Y2 : 5 * G (k + 1) (c + 40) m + 16 ≤ G (k + 2) (c + 40) m := G_succ (k + 1) (c + 40) m
  have hl0 := le_G k (c + 40) m
  have hl1 := le_G (k + 2) (c + 40) m
  have hcost := comb_le xs (fun x => F.cost x + 12) (by omega) (fun x h => (hF' x h).1)
    (d := 10) (by omega)
  have hmax := maxOf_bound xs F.depth (fun x h => (hF' x h).2.1)
  have hmsz := maxOf_bound xs F.msize (fun x h => (hF' x h).2.2)
  have hres := mag_filter a xs F.den
  have hsz := sz_le (.list a) xs
  simp only [filterF_cost, filterF_depth, filterF_msize, filterF_den]
  refine ⟨by omega, by omega, ?_, by omega⟩
  exact max_le (by omega) (by omega)

end Comb

end QecReliability.Trans.BoundsQH
