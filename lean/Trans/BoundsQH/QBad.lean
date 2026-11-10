import Trans.BoundsQH.QBlock
import Trans.Query.FLBad

/-!
# Trans.BoundsQH.QBad: polynomial bounds for `Trans/Query/FLBad.lean`

Recursions `parityGatesF`, `productParityGatesF` (via `polyB_chain`); everything else is an
`FnSig.exact` or a list combinator (`polyB_exact`, `mapEnvQ_P`, `filterF_P`, `mapF_P`).
Main result: `badBlockF_P`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Query

theorem G_lin100 (k c m : ℕ) (hc : 300 ≤ c) : 100 * G k c m + 100 ≤ G (k + 1) c m := by
  have h1 := G_sq k c m
  have h2 := le_G k c m
  nlinarith

section Bad
variable (x : Ix)

@[polyB] theorem coordWireF_P : PolyB (coordWireF x) :=
  polyB_exact _ _ _ (fun p => by obtain ⟨e, b, i⟩ := p; cases b <;> simp [tm_simp, coordWireBody])
    (by simp [Tm.CallsP, coordWireBody, polyB])

@[polyB] theorem rowWiresF_P : PolyB (rowWiresF x) := mapEnvQ_P (coordWireF_P x) _
@[polyB] theorem rowsWiresF_P : PolyB (rowsWiresF x) := mapEnvQ_P (rowWiresF_P x) _

theorem parityGatesF_P : PolyB (parityGatesF x) := by
  refine ⟨_, _, polyB_chain (parityGatesF x) (fun p => p.2.length)
    (fun p => by have := mag_list_len .nat p.2; simp only [mag_prod]; omega)
    (K := 3) (C := 300) le_rfl (fun p => ?_)⟩
  obtain ⟨(v : ℕ), xs⟩ := p
  set μ := mag (.prod .nat (.list .nat)) (v, xs) with hμ
  have L0 := le_G 2 300 μ
  have L1 : 20 * G 2 300 μ + 100 ≤ G 3 300 μ := G_lin20 2 300 μ le_rfl
  rcases xs with _ | ⟨(y : ℕ), xs⟩
  · left
    have e0 : mag TGates [Plain.constGate false] = 7 := rfl
    have z0 : (Ty.enc TGates [Plain.constGate false]).size = 13 := sz_constGate_list
    simp only [parityGatesF_cost, parityGatesF_depth, parityGatesF_msize, parityGatesF_den,
      parityCost, parityDepth, parityMsize, Plain.parityGates, e0]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · right
    have hy : mag (.prod .nat (.list .nat)) (v, xs) ≤ μ := by
      rw [hμ]; simp only [mag, magL]; omega
    refine ⟨(v, xs), by simp, hy, ?_⟩
    have hl := mag_list_len .nat xs
    have hvx : mag (.prod .nat .nat) (v, xs.length) ≤ μ := by
      rw [hμ]; simp only [mag, magL] at hl ⊢; omega
    have hxs : mag (.list .nat) xs ≤ μ := by rw [hμ]; simp only [mag, magL]; omega
    obtain ⟨a1, a2, a3, -⟩ := fnB_at (addF_B x.add) (K := 2) (C := 300) le_rfl le_rfl hvx
    obtain ⟨l1, l2, l3, -⟩ := fnB_at (lengthF_B .nat x.length) (K := 2) (C := 300) le_rfl le_rfl hxs
    have z1 := sz_le (.prod .nat (.list .nat)) (v, y :: xs)
    have z2 := sz_le TGates (Plain.parityGates v (y :: xs))
    have hs := natSize_le (v + xs.length)
    have hap := mag_append_le TGate (Plain.parityGates v xs) [(false, true, y, v + xs.length)]
    have hg : mag TGates [(false, true, y, v + xs.length)] = y + (v + xs.length) + 7 := by
      simp only [mag, magL]; omega
    have hpos := mag_list_len TGate (Plain.parityGates v (y :: xs))
    simp only [parityGatesF_cost, parityGatesF_depth, parityGatesF_msize, parityGatesF_den,
      parityCost, parityDepth, parityMsize]
    have hμ' : y + (v + xs.length) + 7 ≤ μ + 7 := by
      rw [hμ]; simp only [mag, magL] at hl ⊢; omega
    refine ⟨by omega, by omega, ?_, by omega⟩
    simp only [Plain.parityGates]
    omega

attribute [polyB] parityGatesF_P

@[polyB] theorem rowBlockF_P : PolyB (rowBlockF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, rowBlockBody, Plain.rowBlock])
    (by simp [Tm.CallsP, rowBlockBody, polyB])

@[polyB] theorem rowBlocksF_P : PolyB (rowBlocksF x) := mapEnvQ_P (rowBlockF_P x) _

@[polyB] theorem nonemptyF_P (t : Ty) : PolyB (nonemptyF t x) :=
  polyB_exact _ _ _ (fun p => by cases p <;> simp [tm_simp, nonemptyBody])
    (by simp [Tm.CallsP, nonemptyBody])

@[polyB] theorem filterNonemptyF_P : PolyB (filterNonemptyF x) := filterF_P (nonemptyF_P x _) _

@[polyB] theorem normalizerF_P : PolyB (normalizerF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, normalizerBody, Plain.normalizer])
    (by simp [Tm.CallsP, normalizerBody, polyB])

theorem productParityGatesF_P : PolyB (productParityGatesF x) := by
  refine ⟨_, _, polyB_chain (productParityGatesF x) (fun p => p.2.length)
    (fun p => by have := mag_list_len (.prod .nat .nat) p.2; simp only [mag_prod]; omega)
    (K := 5) (C := 300) le_rfl (fun p => ?_)⟩
  obtain ⟨(v : ℕ), ps⟩ := p
  set μ := mag (.prod .nat (.list (.prod .nat .nat))) (v, ps) with hμ
  have L0 := le_G 4 300 μ
  have L1 : 100 * G 4 300 μ + 100 ≤ G 5 300 μ := G_lin100 4 300 μ le_rfl
  have D1 : 5 * (μ + 0) + 16 ≤ G 1 0 μ := G_succ 0 0 μ
  have D2 : ∀ m, m ≤ G 1 0 μ → G 2 300 m ≤ G 4 300 μ := fun m hm =>
    (G_mono le_rfl le_rfl hm).trans ((G_comp 2 300 1 0 μ).trans (G_mono (by omega) le_rfl le_rfl))
  rcases ps with _ | ⟨⟨(a : ℕ), (b : ℕ)⟩, ps⟩
  · left
    have e0 : mag TGates [Plain.constGate false] = 7 := rfl
    have z0 : (Ty.enc TGates [Plain.constGate false]).size = 13 := sz_constGate_list
    simp only [productParityGatesF_cost, productParityGatesF_depth, productParityGatesF_msize,
      productParityGatesF_den, ppCost, ppDepth, ppMsize, Plain.productParityGates, e0]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · right
    have hl := mag_list_len (.prod .nat .nat) ps
    have hy : mag (.prod .nat (.list (.prod .nat .nat))) (v, ps) ≤ μ := by
      rw [hμ]; simp only [mag, magL]; omega
    refine ⟨(v, ps), by simp, hy, ?_⟩
    have hμv : v + 2 * ps.length + 2 ≤ μ + μ := by rw [hμ]; simp only [mag, magL] at hl ⊢; omega
    have hab : a + b ≤ μ := by rw [hμ]; simp only [mag, magL]; omega
    have hps : mag (.list (.prod .nat .nat)) ps ≤ μ := by rw [hμ]; simp only [mag, magL]; omega
    obtain ⟨a1, a2, a3, -⟩ := addF_B x.add (v, 2 * ps.length)
    obtain ⟨s1, s2, s3, -⟩ := succF_B x.succ (v + 2 * ps.length)
    obtain ⟨l1, l2, l3, -⟩ := lengthF_B (.prod .nat .nat) x.length ps
    simp only [mag_prod, mag_nat] at a1 a2 a3 s1 s2 s3
    have c1 := D2 (v + 2 * ps.length + 1) (by omega)
    have c2 := D2 (v + 2 * ps.length) (by omega)
    have c3 := D2 (mag (.list (.prod .nat .nat)) ps) (by omega)
    have z1 := sz_le (.prod .nat (.list (.prod .nat .nat))) (v, (a, b) :: ps)
    have z2 := sz_le TGates (Plain.productParityGates v ((a, b) :: ps))
    have hs := natSize_le (v + 2 * ps.length)
    have hs2 := natSize_le ps.length
    have hap := mag_append_le TGate (Plain.productParityGates v ps)
      [(false, false, a, b), (false, true, v + 2 * ps.length + 1, v + 2 * ps.length)]
    have hg : mag TGates [(false, false, a, b),
        (false, true, v + 2 * ps.length + 1, v + 2 * ps.length)] =
        a + b + (v + 2 * ps.length + 1) + (v + 2 * ps.length) + 13 := by
      simp only [mag, magL]; omega
    have hpos := mag_list_len TGate (Plain.productParityGates v ((a, b) :: ps))
    simp only [productParityGatesF_cost, productParityGatesF_depth, productParityGatesF_msize,
      productParityGatesF_den, ppCost, ppDepth, ppMsize]
    refine ⟨by omega, by omega, ?_, by omega⟩
    simp only [Plain.productParityGates]
    omega

attribute [polyB] productParityGatesF_P

@[polyB] theorem offsetPairF_P : PolyB (offsetPairF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, offsetPairBody])
    (by simp [Tm.CallsP, offsetPairBody, polyB])

@[polyB] theorem offsetPairsF_P : PolyB (offsetPairsF x) := mapEnvQ_P (offsetPairF_P x) _

@[polyB] theorem pairingPairsF_P : PolyB (pairingPairsF x) :=
  polyB_exact _ _ _
    (fun p => by simp [tm_simp, pairingPairsBody, Plain.pairingPairs, Plain.offsetPairs])
    (by simp [Tm.CallsP, pairingPairsBody, polyB])

@[polyB] theorem supportPairsF_P : PolyB (supportPairsF x) :=
  polyB_exact _ _ _
    (fun p => by simp [tm_simp, supportPairsBody, Plain.supportPairs, Plain.offsetPairs])
    (by simp [Tm.CallsP, supportPairsBody, polyB])

@[polyB] theorem supportClauseF_P : PolyB (supportClauseF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, supportClauseBody])
    (by simp [Tm.CallsP, supportClauseBody])

@[polyB] theorem supportClausesF_P : PolyB (supportClausesF x) := mapF_P (supportClauseF_P x) _

@[polyB] theorem pairingBlockF_P : PolyB (pairingBlockF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, pairingBlockBody, Plain.pairingBlock])
    (by simp [Tm.CallsP, pairingBlockBody, polyB])

@[polyB] theorem badBlockF_P : PolyB (badBlockF x) :=
  polyB_exact _ _ _
    (fun p => by
      simp [tm_simp, badBlockBody, badAnd, badNorm1, badNorm2, badSupport, badPairing,
        Plain.badBlock])
    (by simp [Tm.CallsP, badBlockBody, badAnd, badNorm1, badNorm2, badSupport, badPairing, polyB])

end Bad

end QecReliability.Trans.BoundsQH
