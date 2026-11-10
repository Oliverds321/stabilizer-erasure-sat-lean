import Final.Init.Arith
import Trans.Bounds.Size

/-!
# Final.Init.Ctx: the context function `ctxF` at a parsed tuple

`ctx_le`: at `(n, R, x, z, c, d, coins)` with `n ≤ Q`, sizes of `x z c d` summing to `≤ Q`,
`|coins| ≤ Q`, `size R ≤ 10 W` (`W = (2Q+10)²`) and the seed-length function bounded by `S` at
`q = 3n`: cost `≤ 3000 W + S`, depth `≤ 100 Q + 1000 + S`, msize `≤ 1000 W + 10 S`.
`ctx_res_le`: the encoded context is below `ctxF`'s msize.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QecReliability.Final.Init
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_cost bodySig_depth bodySig_msize
  TCtx)
open QecReliability.Trans.Wire

private theorem ctx_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem ctx_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable (L : Lib) (a : AIx) (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
  (base den : ℕ)

theorem ctx_res_le (X : TParsed.den) :
    (Ty.enc (TCtx TX) ((ctxF L a Fp base den).den X)).size ≤ (ctxF L a Fp base den).msize X :=
  le_max_of_le_right (le_max_right _ _)

theorem range_sq (n Q : ℕ) (hn : n ≤ Q) :
    n * (4 * n + 2) ≤ 2 * ((2 * Q + 10) * (2 * Q + 10)) := by nlinarith

theorem range_cost_sq (n Q : ℕ) (hn : n ≤ Q) :
    60 * (n + 1) * (n.size + 1) ≤ 60 * ((2 * Q + 10) * (2 * Q + 10)) := by
  have := NatSize.size_le_self n
  exact mul3_le (by omega) (by omega)

theorem ctx_le (n : ℕ) (R : TRowsW.den) (x z c d : ℕ) (coins : List Bool) (Q S : ℕ)
    (hn : n ≤ Q) (hsz : x.size + z.size + c.size + d.size ≤ Q)
    (hR : (Ty.enc TRowsW R).size ≤ 10 * ((2 * Q + 10) * (2 * Q + 10)))
    (hco : coins.length ≤ Q)
    (h1 : (seedBF L a Fp base den).cost (n + (n + n)) ≤ S)
    (h2 : (seedBF L a Fp base den).depth (n + (n + n)) ≤ S)
    (h3 : (seedBF L a Fp base den).msize (n + (n + n)) ≤ S)
    (h4 : (seedBF L a Fp base den).den (n + (n + n)) ≤ S) :
    (ctxF L a Fp base den).cost (n, R, x, z, c, d, coins) ≤
        3000 * ((2 * Q + 10) * (2 * Q + 10)) + S ∧
      (ctxF L a Fp base den).depth (n, R, x, z, c, d, coins) ≤ 100 * Q + 1000 + S ∧
      (ctxF L a Fp base den).msize (n, R, x, z, c, d, coins) ≤
        1000 * ((2 * Q + 10) * (2 * Q + 10)) + 10 * S := by
  have sn := NatSize.size_le_self n
  have s2 := NatSize.size_add_le n n
  have s3 := NatSize.size_add_le n (n + n)
  obtain ⟨b1, b2, b3, b4⟩ := cellB_le L a x z Q (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4⟩ := repB_le L a n c d Q (by omega) (by omega) (by omega)
  have q : 2 * Q + 10 ≤ (2 * Q + 10) * (2 * Q + 10) := Nat.le_mul_of_pos_left _ (by omega)
  have rg := range_cost_sq n Q hn
  have rs := range_sq n Q hn
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [ctxF, bodySig_cost, ctxBody, Tm.cost, Tm.den, Env.one, ctx_get_zero, ctx_get_succ, addF_cost, addF_den,
      rangeF_cost]
    omega
  · dsimp only [ctxF, bodySig_depth, ctxBody, Tm.depth, Tm.den, Env.one, ctx_get_zero, ctx_get_succ, addF_depth, addF_den,
      rangeF_depth]
    omega
  · dsimp only [ctxF, bodySig_msize, ctxBody, Tm.msize, Tm.den, Env.one, ctx_get_zero, ctx_get_succ, addF_msize, addF_den,
      rangeF_msize, rangeF_den]
    simp only [max_le_iff, Ty.sz_prod]
    have z1 := sz_enc_nat n
    have z2 := sz_enc_nat (n + n)
    have z3 := sz_enc_nat (n + (n + n))
    have z4 := sz_enc_nat ((cellBF L a).den (x, z))
    have z5 := sz_enc_nat ((repBF L a).den (n, c, d))
    have z6 := sz_enc_nat x
    have z7 := sz_enc_nat z
    have z8 := sz_enc_nat c
    have z9 := sz_enc_nat d
    have z10 := Trans.Bounds.sz_range_le n
    have z11 := Trans.Bounds.sz_boolList coins
    have z12 := Trans.Bounds.sz_nat_le_self ((seedBF L a Fp base den).den (n + (n + n)))
    have z13 := NatSize.size_le_self ((seedBF L a Fp base den).den (n + (n + n)))
    have z14 := Ty.sz_list_nil (.prod .bool (.prod .bool (.prod .nat .nat)))
    obtain ⟨sv, hsv⟩ : ∃ sv : ℕ, (seedBF L a Fp base den).den (n + (n + n)) = sv := ⟨_, rfl⟩
    rw [hsv] at h4 z12 z13 ⊢
    have h4' : sv ≤ S := h4
    repeat' apply And.intro
    all_goals omega

end QecReliability.Final.Init
