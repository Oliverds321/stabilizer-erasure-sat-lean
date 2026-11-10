import Trans.Wire.Init

/-!
# Final.Init.Arith: size-based bounds of the init arithmetic

`ceilDivF`, `cellBF`, `repBF` (`Trans/Wire/Init.lean`) at arguments whose bit sizes are `≤ T`:
cost quadratic, depth/msize linear in `T`, result size linear in `T`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QecReliability.Final.Init
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_cost bodySig_depth bodySig_msize)
open QecReliability.Trans.Wire

private theorem arith_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem arith_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

theorem mul3_le {c x y T : ℕ} (hx : x ≤ T) (hy : y ≤ T) : c * x * y ≤ c * (T * T) := by
  rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left c (Nat.mul_le_mul hx hy)

theorem sq_lin (T : ℕ) : 4 * T + 4 ≤ (T + 2) * (T + 2) := by nlinarith

theorem sz_enc_nat (x : ℕ) : (Ty.enc .nat x).size ≤ 4 * x.size + 1 := Ty.sz_nat_le x

variable (L : Lib) (a : AIx)

theorem size2_le : Nat.size 2 ≤ 2 := Nat.size_le.mpr (by norm_num)
theorem size144_le : Nat.size 144 ≤ 8 := Nat.size_le.mpr (by norm_num)
theorem lit2_le : (Ty.enc .nat 2).size ≤ 9 := by have := sz_enc_nat 2; have := size2_le; omega
theorem lit144_le : (Ty.enc .nat 144).size ≤ 33 := by
  have := sz_enc_nat 144; have := size144_le; omega

theorem ceilDiv_le (u v U : ℕ) (hu : u.size + 2 ≤ U) (hv : v.size + 2 ≤ U) :
    (ceilDivF L a).cost (u, v) ≤ 400 * (U * U) + 300 ∧
    (ceilDivF L a).depth (u, v) ≤ 4 * U + 20 ∧
    (ceilDivF L a).msize (u, v) ≤ 30 * U + 100 ∧
    ((ceilDivF L a).den (u, v)).size + 1 ≤ U := by
  have s1 := NatSize.size_add_le u v
  have s2 := NatSize.size_sub_le (u + v) 1
  have q : 2 * U ≤ U * U := Nat.mul_le_mul_right U (by omega)
  by_cases hv0 : v = 0
  · subst hv0
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [ceilDivF, bodySig_cost, ceilDivBody, Tm.cost, Tm.den, Env.one, arith_get_zero, arith_get_succ]
      simp; try omega
    · dsimp only [ceilDivF, bodySig_depth, ceilDivBody, Tm.depth, Tm.den, Env.one, arith_get_zero, arith_get_succ]
      simp
    · dsimp only [ceilDivF, bodySig_msize, ceilDivBody, Tm.msize, Tm.den, Env.one, arith_get_zero, arith_get_succ]
      simp
    · rw [ceilDivF_den]; simp [ceilDiv]; omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [ceilDivF, bodySig_cost, ceilDivBody, Tm.cost, Tm.den, Env.one, arith_get_zero, arith_get_succ, Lib.dmF,
        Trans.Hash.divModF_cost, predF_cost, predF_den, addF_cost, addF_den]
      simp only [hv0, Bool.false_eq_true, ↓reduceIte]
      have m := mul3_le (c := 300) (show (u + v - 1).size + 1 ≤ U by omega)
        (show v.size + 2 ≤ U by omega)
      set_option maxRecDepth 4096 in omega
    · dsimp only [ceilDivF, bodySig_depth, ceilDivBody, Tm.depth, Tm.den, Env.one, arith_get_zero, arith_get_succ, Lib.dmF,
        Trans.Hash.divModF_depth, predF_depth, predF_den, addF_depth, addF_den]
      simp only [hv0, Bool.false_eq_true, ↓reduceIte]
      omega
    · dsimp only [ceilDivF, bodySig_msize, ceilDivBody, Tm.msize, Tm.den, Env.one, arith_get_zero, arith_get_succ, Lib.dmF,
        Trans.Hash.divModF_msize, predF_msize, predF_den, addF_msize, addF_den]
      simp only [hv0, Bool.false_eq_true, ↓reduceIte, max_le_iff, Ty.sz_prod]
      have z1 := sz_enc_nat (u + v - 1)
      have z2 := sz_enc_nat v
      omega
    · rw [ceilDivF_den]
      unfold ceilDiv
      have := NatSize.size_div_le (u + v - 1) v
      omega

/-- `cellBF` at `(x, z)` with `x.size, z.size ≤ T`. -/
theorem cellB_le (x z T : ℕ) (hx : x.size ≤ T) (hz : z.size ≤ T) :
    (cellBF L a).cost (x, z) ≤ 1000 * ((2 * T + 10) * (2 * T + 10)) ∧
    (cellBF L a).depth (x, z) ≤ 20 * T + 100 ∧
    (cellBF L a).msize (x, z) ≤ 100 * T + 500 ∧
    ((cellBF L a).den (x, z)).size ≤ 2 * T + 10 := by
  have e1 := NatSize.size_mul_le 144 z
  have e2 := NatSize.size_mul_le (144 * z) z
  have e3 := NatSize.size_mul_le x x
  have t1 := size144_le
  have t2 := lit144_le
  obtain ⟨c1, c2, c3, c4⟩ := ceilDiv_le L a (144 * z * z) (x * x) (2 * T + 10) (by omega) (by omega)
  have q : 2 * T + 10 ≤ (2 * T + 10) * (2 * T + 10) := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [cellBF, bodySig_cost, cellBBody, Tm.cost, Tm.den, Env.one, arith_get_zero, arith_get_succ, mulF_cost, mulF_den,
      mulCost]
    have m1 := mul3_le (c := 100) (show Nat.size 144 + 1 ≤ 2 * T + 10 by omega)
      (show Nat.size 144 + z.size + 1 ≤ 2 * T + 10 by omega)
    have m2 := mul3_le (c := 100) (show (144 * z).size + 1 ≤ 2 * T + 10 by omega)
      (show (144 * z).size + z.size + 1 ≤ 2 * T + 10 by omega)
    have m3 := mul3_le (c := 100) (show x.size + 1 ≤ 2 * T + 10 by omega)
      (show x.size + x.size + 1 ≤ 2 * T + 10 by omega)
    omega
  · dsimp only [cellBF, bodySig_depth, cellBBody, Tm.depth, Tm.den, Env.one, arith_get_zero, arith_get_succ, mulF_depth, mulF_den]
    try simp only [max_le_iff]
    omega
  · dsimp only [cellBF, bodySig_msize, cellBBody, Tm.msize, Tm.den, Env.one, arith_get_zero, arith_get_succ, mulF_msize, mulF_den]
    simp only [max_le_iff, Ty.sz_prod]
    have z1 := sz_enc_nat z
    have z2 := sz_enc_nat x
    have z3 := sz_enc_nat (144 * z)
    have z4 := sz_enc_nat (144 * z * z)
    have z5 := sz_enc_nat (x * x)
    omega
  · show ((ceilDivF L a).den (144 * z * z, x * x)).size ≤ 2 * T + 10
    omega

/-- `repBF` at `(n, c, d)` with sizes `≤ T`. -/
theorem repB_le (n c d T : ℕ) (hn : n.size ≤ T) (hc : c.size ≤ T) (hd : d.size ≤ T) :
    (repBF L a).cost (n, c, d) ≤ 1000 * ((2 * T + 10) * (2 * T + 10)) + 1000 ∧
    (repBF L a).depth (n, c, d) ≤ 20 * T + 200 ∧
    (repBF L a).msize (n, c, d) ≤ 200 * T + 1000 ∧
    ((repBF L a).den (n, c, d)).size ≤ 2 * T + 10 := by
  have e0 := NatSize.size_succ_le n
  have e1 := NatSize.size_mul_le 2 (n + 1)
  have e2 := NatSize.size_mul_le (2 * (n + 1)) d
  have t1 := size2_le
  have t2 := lit2_le
  obtain ⟨c1, c2, c3, c4⟩ := ceilDiv_le L a (2 * (n + 1) * d) c (2 * T + 10) (by omega) (by omega)
  have q : 2 * T + 10 ≤ (2 * T + 10) * (2 * T + 10) := Nat.le_mul_of_pos_left _ (by omega)
  generalize hv : (ceilDivF L a).den (2 * (n + 1) * d, c) = v at c4
  have p1 := NatSize.size_sub_le v 1
  have p2 := NatSize.size_le_self (v - 1).size
  have p3 := NatSize.size_sub_le (v - 1).size 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [repBF, bodySig_cost, repBBody, Tm.cost, Tm.den, Env.one, arith_get_zero, arith_get_succ, mulF_cost, mulF_den,
      mulCost, succF_cost, succF_den, predF_cost, predF_den, bitLenF_cost, bitLenF_den, subF_cost]
    rw [hv]
    have m1 := mul3_le (c := 100) (show Nat.size 2 + 1 ≤ 2 * T + 10 by omega)
      (show Nat.size 2 + (n + 1).size + 1 ≤ 2 * T + 10 by omega)
    have m2 := mul3_le (c := 100) (show (2 * (n + 1)).size + 1 ≤ 2 * T + 10 by omega)
      (show (2 * (n + 1)).size + d.size + 1 ≤ 2 * T + 10 by omega)
    have m3 := mul3_le (c := 30) (show (v - 1).size + 1 ≤ 2 * T + 10 by omega)
      (show (v - 1).size + 1 ≤ 2 * T + 10 by omega)
    omega
  · dsimp only [repBF, bodySig_depth, repBBody, Tm.depth, Tm.den, Env.one, arith_get_zero, arith_get_succ, mulF_depth, mulF_den,
      succF_depth, succF_den, predF_depth, predF_den, bitLenF_depth, bitLenF_den, subF_depth]
    rw [hv]
    try simp only [max_le_iff]
    omega
  · dsimp only [repBF, bodySig_msize, repBBody, Tm.msize, Tm.den, Env.one, arith_get_zero, arith_get_succ, mulF_msize, mulF_den,
      succF_msize, succF_den, predF_msize, predF_den, bitLenF_msize, bitLenF_den, subF_msize]
    rw [hv]
    simp only [max_le_iff, Ty.sz_prod]
    have z1 := sz_enc_nat (n + 1)
    have z2 := sz_enc_nat (2 * (n + 1))
    have z3 := sz_enc_nat d
    have z4 := sz_enc_nat c
    have z5 := sz_enc_nat (2 * (n + 1) * d)
    have z6 := sz_enc_nat (v - 1).size
    omega
  · show (((ceilDivF L a).den (2 * (n + 1) * d, c) - 1).size - 2).size ≤ 2 * T + 10
    rw [hv]
    have p4 := NatSize.size_le_self ((v - 1).size - 2)
    omega

end QecReliability.Final.Init
