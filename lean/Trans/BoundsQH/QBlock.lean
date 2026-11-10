import Trans.BoundsQH.QCirc

/-!
# Trans.BoundsQH.QBlock: `outputUnitsF`, `matchBlockF`, `blockMergeF`

`blockMerge` accumulates shifted formulas; its result magnitude is bounded by an invariant
(`blockMerge_inv`: aux count, literal count `lc`, and magnitude `≤ μ (μ + 1)`), using
`mag_formS : mag (formS e F) ≤ mag F + e.2 · lc F`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Query

/-! ## Output units and match blocks -/

section Units
variable (x : Ix)

theorem outputUnitsF_P : PolyB (outputUnitsF x) := by
  refine ⟨_, _, polyB_chain (outputUnitsF x) (fun p => p.1.length)
    (fun p => by have := mag_list_len .nat p.1; simp only [mag_prod]; omega)
    (K := 1) (C := 300) le_rfl (fun p => ?_)⟩
  obtain ⟨os, bs⟩ := p
  have L := le_G 1 300 (mag (.prod (.list .nat) (.list .bool)) (os, bs))
  have L5 : 5 * (mag (.prod (.list .nat) (.list .bool)) (os, bs) + 300) + 16 ≤
      G 1 300 (mag (.prod (.list .nat) (.list .bool)) (os, bs)) := G_succ 0 300 _
  have h1 := sz_le (.list .nat) os
  have h2 := sz_le (.list .bool) bs
  have h3 := mag_list_len .nat os
  rcases os with _ | ⟨o, os⟩
  · left
    simp only [outputUnitsF_cost, outputUnitsF_depth, outputUnitsF_msize, outputUnitsF_den,
      outputUnitsCost, outputUnitsMsize, Plain.outputUnits]
    simp only [mag, magL] at L L5 h3 ⊢
    refine ⟨by omega, by omega, by omega, by omega⟩
  rcases bs with _ | ⟨b, bs⟩
  · left
    simp only [outputUnitsF_cost, outputUnitsF_depth, outputUnitsF_msize, outputUnitsF_den,
      outputUnitsCost, outputUnitsMsize, Plain.outputUnits]
    simp only [mag, magL] at L L5 h3 ⊢
    refine ⟨by omega, by omega, by omega, by omega⟩
  · right
    refine ⟨(os, bs), by simp, ?_, ?_⟩
    · simp only [mag, magL]; omega
    have h4 := sz_le TForm (Plain.outputUnits (o :: os) (b :: bs))
    simp only [outputUnitsF_cost, outputUnitsF_depth, outputUnitsF_msize, outputUnitsF_den,
      outputUnitsCost, outputUnitsMsize, Plain.outputUnits] at h4 ⊢
    simp only [mag, magL, List.length_cons] at L L5 h1 h2 h3 h4 ⊢
    refine ⟨by omega, by omega, by omega, by omega⟩

attribute [polyB] outputUnitsF_P

@[polyB] theorem matchBlockF_P : PolyB (matchBlockF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, matchBlockBody, Plain.matchBlock])
    (by simp [Tm.CallsP, matchBlockBody, polyB])

end Units

/-! ## Shifted formulas -/

/-- Number of literals of a formula. -/
def lc (F : Plain.Form) : ℕ := (F.map List.length).sum

theorem lc_append (F H : Plain.Form) : lc (F ++ H) = lc F + lc H := by
  simp [lc]

theorem lc_formS (e : ℕ × ℕ) (F : Plain.Form) : lc (Plain.formS e F) = lc F := by
  simp [lc, Plain.formS, Plain.clauseS, Function.comp_def]

theorem lc_le_mag (F : Plain.Form) : lc F ≤ mag TForm F := by
  induction F with
  | nil => simp [lc]
  | cons c F ih =>
    have := mag_list_len TLit c
    simp only [lc, List.map_cons, List.sum_cons] at ih ⊢
    simp only [mag, magL] at this ih ⊢
    omega

theorem mag_clauseS (e : ℕ × ℕ) (c : Plain.Clause) :
    mag TClause (Plain.clauseS e c) ≤ mag TClause c + e.2 * c.length := by
  induction c with
  | nil => simp [Plain.clauseS]
  | cons l c ih =>
    have hs : Plain.shiftWire e l.1 ≤ l.1 + e.2 := by unfold Plain.shiftWire; split <;> omega
    have hm : e.2 * (c.length + 1) = e.2 * c.length + e.2 := by ring
    simp only [Plain.clauseS, List.map_cons, Plain.litS, List.length_cons] at ih ⊢
    simp only [mag, magL] at ih ⊢
    omega

theorem mag_formS (e : ℕ × ℕ) (F : Plain.Form) :
    mag TForm (Plain.formS e F) ≤ mag TForm F + e.2 * lc F := by
  induction F with
  | nil => simp [Plain.formS]
  | cons c F ih =>
    have h1 := mag_clauseS e c
    have hm : e.2 * lc (c :: F) = e.2 * c.length + e.2 * lc F := by
      simp only [lc, List.map_cons, List.sum_cons]; ring
    simp only [Plain.formS, List.map_cons] at ih ⊢
    simp only [mag, magL] at ih h1 ⊢
    rw [hm]
    omega

/-- **Invariant of `blockMerge`** (`μ = mag Bs`): aux count and literal count `≤ μ`,
formula magnitude `≤ μ (μ + 1)`. -/
theorem blockMerge_inv (n : ℕ) : ∀ Bs : List Plain.BlockP,
    (Plain.blockMerge n Bs).1 ≤ mag (.list TBlock) Bs ∧
    lc (Plain.blockMerge n Bs).2 ≤ mag (.list TBlock) Bs ∧
    mag TForm (Plain.blockMerge n Bs).2 ≤ mag (.list TBlock) Bs * (mag (.list TBlock) Bs + 1)
  | [] => ⟨Nat.zero_le _, by simp [Plain.blockMerge, lc], by show 1 ≤ 1 * (1 + 1); omega⟩
  | B :: Bs => by
    obtain ⟨i1, i2, i3⟩ := blockMerge_inv n Bs
    have hf := mag_formS (n, B.1) (Plain.blockMerge n Bs).2
    have hl := lc_formS (n, B.1) (Plain.blockMerge n Bs).2
    have ha := mag_append_le TClause B.2 (Plain.formS (n, B.1) (Plain.blockMerge n Bs).2)
    have hlc := lc_append B.2 (Plain.formS (n, B.1) (Plain.blockMerge n Bs).2)
    have hB := lc_le_mag B.2
    have e1 : mag (.list TBlock) (B :: Bs) = B.1 + mag TForm B.2 + 1 + 1 + mag (.list TBlock) Bs :=
      rfl
    simp only [Plain.blockMerge, Plain.blockAnd]
    rw [e1]
    generalize mag (.list TBlock) Bs = μ at *
    generalize (Plain.blockMerge n Bs).2 = M at *
    generalize (Plain.blockMerge n Bs).1 = A at *
    dsimp only at hf ⊢
    refine ⟨by omega, by omega, ?_⟩
    have h5 : B.1 * lc M ≤ B.1 * μ := Nat.mul_le_mul_left _ i2
    nlinarith

theorem mag_blockMerge_le (n : ℕ) (Bs : List Plain.BlockP) :
    mag TBlock (Plain.blockMerge n Bs) ≤ (mag (.list TBlock) Bs + 1) * (mag (.list TBlock) Bs + 1) := by
  obtain ⟨i1, -, i3⟩ := blockMerge_inv n Bs
  have : mag TBlock (Plain.blockMerge n Bs) =
      (Plain.blockMerge n Bs).1 + mag TForm (Plain.blockMerge n Bs).2 + 1 := rfl
  rw [this]
  nlinarith

section Merge
variable (x : Ix)

theorem blockMergeF_P : PolyB (blockMergeF x) := by
  obtain ⟨ka, ca, hba⟩ := blockAndF_P x
  refine ⟨_, _, polyB_chain (blockMergeF x) (fun p => p.2.length)
    (fun p => by have := mag_list_len TBlock p.2; simp only [mag_prod]; omega)
    (K := ka + 3) (C := ca + 300) (by omega) (fun p => ?_)⟩
  obtain ⟨n, Bs⟩ := p
  set μ := mag (.prod .nat (.list TBlock)) (n, Bs) with hμ
  -- the result is small
  have hres : mag TBlock (Plain.blockMerge n Bs) ≤ G (ka + 3) (ca + 300) μ := by
    have h1 := mag_blockMerge_le n Bs
    have h2 : mag (.list TBlock) Bs ≤ μ := by rw [hμ]; simp only [mag_prod]; omega
    have h3 : (mag (.list TBlock) Bs + 1) * (mag (.list TBlock) Bs + 1) ≤ (μ + 1) * (μ + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (μ + (ca + 300) + 1) * (μ + (ca + 300) + 1) + 16 ≤ G 1 (ca + 300) μ := G_sq 0 _ _
    have h5 : (μ + 1) * (μ + 1) ≤ (μ + (ca + 300) + 1) * (μ + (ca + 300) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h6 := G_mono (k := 1) (k' := ka + 3) (c := ca + 300) (c' := ca + 300) (by omega) le_rfl
      (le_refl μ)
    omega
  rcases Bs with _ | ⟨B, Bs⟩
  · left
    have L := le_G (ka + 3) (ca + 300) μ
    simp only [blockMergeF_cost, blockMergeF_depth, blockMergeF_msize, blockMergeF_den,
      blockMergeCost, blockMergeDepth, blockMergeMsize]
    exact ⟨by omega, by omega, hres, by omega⟩
  · right
    have hy : mag (.prod .nat (.list TBlock)) (n, Bs) ≤ μ := by
      rw [hμ]; simp only [mag, magL]; omega
    refine ⟨(n, Bs), by simp, hy, ?_⟩
    -- the blockAnd call
    have hM := mag_blockMerge_le n Bs
    have hz : mag (.prod .nat (.prod TBlock TBlock)) (n, B, Plain.blockMerge n Bs) ≤
        G 1 0 μ := by
      have e1 : mag (.prod .nat (.prod TBlock TBlock)) (n, B, Plain.blockMerge n Bs) =
          n + (mag TBlock B + mag TBlock (Plain.blockMerge n Bs) + 1) + 1 := rfl
      have e2 : μ = n + (mag TBlock B + 1 + mag (.list TBlock) Bs) + 1 := rfl
      have h3 : (mag (.list TBlock) Bs + 1) * (mag (.list TBlock) Bs + 1) ≤ μ * μ :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3' : (μ + 1) * (μ + 1) = μ * μ + 2 * μ + 1 := by ring
      have h4 : (μ + 1) * (μ + 1) + 16 ≤ G 1 0 μ := G_sq 0 0 μ
      rw [e1]
      omega
    obtain ⟨a1, a2, a3, -⟩ := hba (n, B, Plain.blockMerge n Bs)
    have c1 := G_mono (k := ka) (c := ca) le_rfl le_rfl hz
    have c2 : G ka ca (G 1 0 μ) ≤ G (ka + 2) (ca + 300) μ :=
      (G_comp ka ca 1 0 μ).trans (G_mono (by omega) (by omega) le_rfl)
    have c3 := G_lin20 (ka + 2) (ca + 300) μ (by omega)
    have c4 : 5 * G 1 0 μ + 16 ≤ G (ka + 2) (ca + 300) μ :=
      (G_succ 1 0 μ).trans (G_mono (by omega) (by omega) le_rfl)
    have z1 := sz_le (.prod .nat (.prod TBlock TBlock)) (n, B, Plain.blockMerge n Bs)
    have z2 := sz_le (.prod .nat (.list TBlock)) (n, Bs)
    have L0 := le_G (ka + 2) (ca + 300) μ
    have e3 : G (ka + 2 + 1) (ca + 300) μ = G (ka + 3) (ca + 300) μ := rfl
    simp only [blockMergeF_cost, blockMergeF_depth, blockMergeF_msize, blockMergeF_den,
      blockMergeCost, blockMergeDepth, blockMergeMsize]
    refine ⟨by omega, by omega, by omega, by omega⟩

attribute [polyB] blockMergeF_P

end Merge

end QecReliability.Trans.BoundsQH
