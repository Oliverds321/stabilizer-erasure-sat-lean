import Trans.BoundsQH.QCirc

/-!
# Trans.BoundsQH.QCodec: polynomial bounds for `Trans/Query/Codec.lean`

`wordF`, `natHeaderF`, `literalF` (closed forms, `FnB (G 2 400)`), `literalsF`, `clauseF`,
`bodyF`, `encodeF` (`PolyB`).
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Query QecReliability.OracleCost

theorem mag_bits (bs : List Bool) : mag (.list .bool) bs = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [mag, magL] at ih ⊢; simp only [List.length_cons]; omega

theorem wordCost_le' (k : ℕ) : wordCost k ≤ 105 * ((k + 1) * (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := natSize_le (k + 1)
    rw [wordCost_succ]
    nlinarith

theorem natHeaderCost_le' (n : ℕ) : natHeaderCost n ≤ 300 * ((n + 1) * (n + 1)) := by
  have h1 := natSize_le n
  have h2 := natSize_le n.size
  have h3 := wordCost_le' n.size
  have h4 : (n.size + 1) * (n.size + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h5 : (n.size + 1) * (n.size.size + 1) ≤ (n + 1) * (n + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h6 := sq_ge n
  unfold natHeaderCost
  have e1 : 30 * (n.size + 1) * (n.size + 1) = 30 * ((n.size + 1) * (n.size + 1)) := by ring
  have e2 : 40 * (n.size + 1) * (n.size.size + 1) = 40 * ((n.size + 1) * (n.size.size + 1)) := by
    ring
  rw [e1, e2]
  omega

section Codec
variable (i : ℕ)

theorem wordF_B : FnB (G 2 400) (wordF i) := fnB_quad _ _ fun y => by
  obtain ⟨(k : ℕ), (n : ℕ)⟩ := y
  have h1 := natSize_le k
  have h2 := natSize_le n
  have h3 := wordCost_le' k
  have hX := sq_ge (k + n + 1)
  have h4 : (k + 1) * (k + 1) ≤ (k + n + 1 + 1) * (k + n + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [mag_prod, mag_nat, wordF_cost, wordF_depth, wordF_msize, wordF_den, mag_bits,
    QueryCodec.word_length]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem natHeaderF_B : FnB (G 2 400) (natHeaderF i) := fnB_quad _ _ fun (n : ℕ) => by
  have h1 := natSize_le n
  have h2 := natSize_le n.size
  have h3 := natHeaderCost_le' n
  have hX := sq_ge n
  simp only [mag_nat, natHeaderF_cost, natHeaderF_depth, natHeaderF_msize, natHeaderF_den,
    mag_bits, QueryCodec.natHeader_length]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem literalF_B : FnB (G 2 400) (literalF i) := fnB_quad _ _ fun y => by
  obtain ⟨(k : ℕ), (j : ℕ), b⟩ := y
  have h1 := natSize_le k
  have h2 := natSize_le j
  have h3 := wordCost_le' k
  have hX := sq_ge (k + (j + 1 + 1) + 1)
  have h4 : (k + 1) * (k + 1) ≤ (k + (j + 1 + 1) + 1 + 1) * (k + (j + 1 + 1) + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [mag_prod, mag_nat, mag_bool, literalF_cost, literalF_depth, literalF_msize,
    literalF_den, mag_bits, QueryCodec.literal, List.length_cons, QueryCodec.word_length]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

@[polyB] theorem wordF_P : PolyB (wordF i) := ⟨_, _, wordF_B i⟩
@[polyB] theorem natHeaderF_P : PolyB (natHeaderF i) := ⟨_, _, natHeaderF_B i⟩
@[polyB] theorem literalF_P : PolyB (literalF i) := ⟨_, _, literalF_B i⟩

end Codec

@[polyB] theorem literalsF_P (il i : ℕ) : PolyB (literalsF il i) := flatMapEnvQ_P (literalF_P il) i

theorem clauseF_P (il ils i : ℕ) : PolyB (clauseF il ils i) := by
  obtain ⟨k1, c1, h1⟩ := literalsF_P il ils
  have h2 := lengthF_B TLit 0
  refine ⟨k1 + 4, c1 + 400, fun p => ?_⟩
  obtain ⟨(k : ℕ), c⟩ := p
  set μ := mag (.prod .nat TClause) (k, c)
  have hc : mag TClause c ≤ μ := by simp only [μ, mag_prod]; omega
  obtain ⟨a1, a2, a3, a4⟩ := fnB_at h1 (K := k1 + 2) (C := c1 + 400) (by omega) (by omega)
    (le_refl μ)
  obtain ⟨b1, b2, b3, -⟩ := fnB_at h2 (K := k1 + 2) (C := c1 + 400) (by omega) (by omega) hc
  have w := wordCost_le' 2
  have hs := natSize_le c.length
  have hl := mag_list_len TLit c
  have L := G_lin20 (k1 + 2) (c1 + 400) μ (by omega)
  have L2 : 20 * G (k1 + 2 + 1) (c1 + 400) μ + 100 ≤ G (k1 + 4) (c1 + 400) μ :=
    G_lin20 (k1 + 3) (c1 + 400) μ (by omega)
  have L0 := le_G (k1 + 2) (c1 + 400) μ
  have hap := mag_append_le .bool (QueryCodec.word 2 c.length) (QueryCodec.literals k c)
  simp only [clauseF_cost, clauseF_depth, clauseF_msize, clauseF_den, QueryCodec.clause]
  rw [mag_bits (QueryCodec.word 2 c.length), QueryCodec.word_length] at hap
  simp only [literalsF_den] at a4
  refine ⟨by omega, by omega, by omega, by omega⟩

attribute [polyB] clauseF_P

@[polyB] theorem bodyF_P (il ils ic i : ℕ) : PolyB (bodyF il ils ic i) :=
  flatMapEnvQ_P (clauseF_P il ils ic) i

theorem mag_encodePlain (v : ℕ) (F : List (List (ℕ × Bool))) :
    mag (.list .bool) (encodePlain v F) ≤
      mag (.list .bool) (QueryCodec.natHeader v) + mag (.list .bool) (QueryCodec.natHeader F.length) +
        mag (.list .bool) (QueryCodec.body v.size F) := by
  unfold encodePlain
  have h1 := mag_append_le .bool (QueryCodec.natHeader v ++ QueryCodec.natHeader F.length)
    (QueryCodec.body v.size F)
  have h2 := mag_append_le .bool (QueryCodec.natHeader v) (QueryCodec.natHeader F.length)
  omega

theorem encodeF_P (il ils ic ib i : ℕ) : PolyB (encodeF il ils ic ib i) := by
  obtain ⟨k1, c1, h1⟩ := bodyF_P il ils ic ib
  have hn := natHeaderF_B 0
  have hl := lengthF_B TClause 0
  refine ⟨k1 + 6, c1 + 400, fun p => ?_⟩
  obtain ⟨(v : ℕ), F⟩ := p
  set μ := mag (.prod .nat TForm) (v, F)
  have hv : v ≤ μ := by simp only [μ, mag_prod, mag_nat]; omega
  have hF : mag TForm F ≤ μ := by simp only [μ, mag_prod]; omega
  have hlen := mag_list_len TClause F
  have hvs := natSize_le v
  have hb : mag (.prod .nat TForm) (v.size, F) ≤ μ := by simp only [μ, mag_prod, mag_nat]; omega
  obtain ⟨a1, a2, a3, a4⟩ := fnB_at h1 (K := k1 + 2) (C := c1 + 400) (by omega) (by omega) hb
  obtain ⟨n1, n2, n3, n4⟩ := fnB_at hn (K := k1 + 2) (C := c1 + 400) (by omega) (by omega)
    (show mag .nat v ≤ μ from hv)
  obtain ⟨m1, m2, m3, m4⟩ := fnB_at hn (K := k1 + 2) (C := c1 + 400) (by omega) (by omega)
    (show mag .nat F.length ≤ μ by simp only [mag_nat]; omega)
  obtain ⟨l1, l2, l3, -⟩ := fnB_at hl (K := k1 + 2) (C := c1 + 400) (by omega) (by omega) hF
  simp only [natHeaderF_cost, natHeaderF_depth, natHeaderF_msize, natHeaderF_den, mag_nat] at n1 n2 n3 n4 m1 m2 m3 m4
  replace a4 : mag (.list .bool) (QueryCodec.body v.size F) ≤ G (k1 + 2) (c1 + 400) μ := a4
  have hss := natSize_le v.size
  have hsl := natSize_le F.length
  have hsl2 := natSize_le F.length.size
  have q1 : (v.size + 1) * (v.size + 1) ≤ (μ + 1) * (μ + 1) := Nat.mul_le_mul (by omega) (by omega)
  have q2 := G_sq (k1 + 2) (c1 + 400) μ
  have q3 := le_G (k1 + 2) (c1 + 400) μ
  have q4 : (μ + 1) * (μ + 1) ≤ (G (k1 + 2) (c1 + 400) μ + 1) * (G (k1 + 2) (c1 + 400) μ + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e30 : 30 * (v.size + 1) * (v.size + 1) = 30 * ((v.size + 1) * (v.size + 1)) := by ring
  have hme := mag_encodePlain v F
  have z1 := sz_le (.list .bool) (encodePlain v F)
  have z2 := sz_le TForm F
  -- one more level for the sums
  have hC : 300 ≤ c1 + 400 :=
    Nat.le_trans (by decide : 300 ≤ 400) (Nat.le_add_left 400 c1)
  have L1 : 20 * G (k1 + 3) (c1 + 400) μ + 100 ≤ G (k1 + 4) (c1 + 400) μ :=
    G_lin20 (k1 + 3) (c1 + 400) μ hC
  have L2 : 20 * G (k1 + 4) (c1 + 400) μ + 100 ≤ G (k1 + 5) (c1 + 400) μ :=
    G_lin20 (k1 + 4) (c1 + 400) μ hC
  have L3 : 20 * G (k1 + 5) (c1 + 400) μ + 100 ≤ G (k1 + 6) (c1 + 400) μ :=
    G_lin20 (k1 + 5) (c1 + 400) μ hC
  have e3 : G (k1 + 2 + 1) (c1 + 400) μ = G (k1 + 3) (c1 + 400) μ := rfl
  have q6 := G_succ (k1 + 2) (c1 + 400) μ
  simp only [encodeF_cost, encodeF_depth, encodeF_msize, encodeF_den, encodeCost, encodeDepth,
    encodeMsize]
  rw [e30]
  refine ⟨by omega, by omega, by omega, by omega⟩

attribute [polyB] encodeF_P

end QecReliability.Trans.BoundsQH
