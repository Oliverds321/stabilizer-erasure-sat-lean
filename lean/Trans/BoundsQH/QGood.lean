import Trans.BoundsQH.QBad
import Trans.Query.FLGood

/-!
# Trans.BoundsQH.QGood: polynomial bounds for `Trans/Query/FLGood.lean`

Recursions `setF`, `condEqsF` (via `polyB_chain`); the accumulating recursions
`recAddRowF`, `synthesizeF` with the wire invariant `RecInv` (all wires of the reconstruction
are `≤ M + #gates`, `recAddRow_inv`, `synth_inv`, `mag_rec_le`). Main result: `goodBlockF_P`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Query

/-! ## Wire invariant of reconstructions -/

/-- All wires of a reconstruction are `≤ W`. -/
def RecInv (W : ℕ) (R : Plain.RecP) : Prop :=
  (∀ g ∈ R.1, g.2.2.1 ≤ W ∧ g.2.2.2 ≤ W) ∧ (∀ a ∈ R.2.1, a ≤ W) ∧ (∀ a ∈ R.2.2, a ≤ W)

theorem RecInv.mono {W W' : ℕ} {R : Plain.RecP} (h : RecInv W R) (hW : W ≤ W') : RecInv W' R :=
  ⟨fun g hg => ⟨(h.1 g hg).1.trans hW, (h.1 g hg).2.trans hW⟩, fun a ha => (h.2.1 a ha).trans hW,
    fun a ha => (h.2.2 a ha).trans hW⟩

theorem getD_le {xs : List ℕ} {W : ℕ} (h : ∀ a ∈ xs, a ≤ W) (i : ℕ) : xs.getD i 0 ≤ W := by
  induction xs generalizing i with
  | nil => simp
  | cons y ys ih =>
    cases i with
    | zero => simp only [List.getD_cons_zero]; exact h y (by simp)
    | succ i => simp only [List.getD_cons_succ]; exact ih (fun a ha => h a (by simp [ha])) i

theorem set_le {xs : List ℕ} {W : ℕ} (h : ∀ a ∈ xs, a ≤ W) (i val : ℕ) (hv : val ≤ W) :
    ∀ a ∈ xs.set i val, a ≤ W := fun a ha => by
  rcases List.mem_or_eq_of_mem_set ha with h1 | h1
  · exact h a h1
  · omega

theorem recAddInc_inv {M v coeff : ℕ} {R : Plain.RecP} (c : Plain.Coord)
    (hR : RecInv (M + R.1.length) R) (hv : v ≤ M) (hc : coeff ≤ M) :
    RecInv (M + R.1.length + 1) (Plain.recAddInc v R c coeff) ∧
    (Plain.recAddInc v R c coeff).1.length = R.1.length + 1 ∧
    (Plain.recAddInc v R c coeff).2.1.length = R.2.1.length ∧
    (Plain.recAddInc v R c coeff).2.2.length = R.2.2.length := by
  obtain ⟨gs, xs, zs⟩ := R
  obtain ⟨b, i⟩ := c
  obtain ⟨h1, h2, h3⟩ := hR
  dsimp only at h1 h2 h3
  have g2 := getD_le h2 i
  have g3 := getD_le h3 i
  cases b
  · simp only [Plain.recAddInc, Bool.false_eq_true, if_false, List.length_append,
      List.length_cons, List.length_nil, List.length_set]
    refine ⟨⟨fun g hg => ?_, set_le (fun a ha => (h2 a ha).trans (by omega)) i _ (by omega),
      fun a ha => (h3 a ha).trans (by omega)⟩, by simp, by simp, by simp⟩
    rcases List.mem_append.mp hg with hg | hg
    · exact ⟨(h1 g hg).1.trans (by omega), (h1 g hg).2.trans (by omega)⟩
    · simp only [List.mem_singleton] at hg; subst hg; dsimp only; omega
  · simp only [Plain.recAddInc, if_true, List.length_append,
      List.length_cons, List.length_nil, List.length_set]
    refine ⟨⟨fun g hg => ?_, fun a ha => (h2 a ha).trans (by omega),
      set_le (fun a ha => (h3 a ha).trans (by omega)) i _ (by omega)⟩, by simp, by simp, by simp⟩
    rcases List.mem_append.mp hg with hg | hg
    · exact ⟨(h1 g hg).1.trans (by omega), (h1 g hg).2.trans (by omega)⟩
    · simp only [List.mem_singleton] at hg; subst hg; dsimp only; omega

theorem recAddRow_inv {M v coeff : ℕ} {R : Plain.RecP} (hR : RecInv (M + R.1.length) R)
    (hv : v ≤ M) (hc : coeff ≤ M) : ∀ cs : List Plain.Coord,
    RecInv (M + R.1.length + cs.length) (Plain.recAddRow v R coeff cs) ∧
    (Plain.recAddRow v R coeff cs).1.length = R.1.length + cs.length ∧
    (Plain.recAddRow v R coeff cs).2.1.length = R.2.1.length ∧
    (Plain.recAddRow v R coeff cs).2.2.length = R.2.2.length
  | [] => by simpa [Plain.recAddRow] using hR
  | c :: cs => by
    obtain ⟨i1, i2, i3, i4⟩ := recAddRow_inv hR hv hc cs
    have i1' : RecInv (M + (Plain.recAddRow v R coeff cs).1.length) (Plain.recAddRow v R coeff cs) :=
      i1.mono (by omega)
    obtain ⟨j1, j2, j3, j4⟩ := recAddInc_inv c i1' hv hc
    simp only [Plain.recAddRow, List.length_cons]
    exact ⟨j1.mono (by omega), by omega, by omega, by omega⟩

theorem mag_gates_le {W : ℕ} (gs : List Plain.GateP) (h : ∀ g ∈ gs, g.2.2.1 ≤ W ∧ g.2.2.2 ≤ W) :
    mag TGates gs ≤ gs.length * (2 * W + 6) + 1 := by
  have := mag_list_le TGate gs (2 * W + 5) (fun g hg => by
    obtain ⟨a1, a2⟩ := h g hg
    have e : mag TGate g = g.2.2.1 + g.2.2.2 + 5 := by
      simp only [mag, magL]; omega
    omega)
  omega

theorem mag_wires_le {W : ℕ} (xs : List ℕ) (h : ∀ a ∈ xs, a ≤ W) :
    mag (.list .nat) xs ≤ xs.length * (W + 1) + 1 :=
  mag_list_le .nat xs W (fun a ha => h a ha)

theorem mag_rec_le {W : ℕ} (R : Plain.RecP) (h : RecInv W R) :
    mag TRec R ≤ (R.1.length + R.2.1.length + R.2.2.length + 3) * (2 * W + 10) := by
  have h1 := mag_gates_le R.1 h.1
  have h2 := mag_wires_le R.2.1 h.2.1
  have h3 := mag_wires_le R.2.2 h.2.2
  have e : mag TRec R = mag TGates R.1 + (mag (.list .nat) R.2.1 + mag (.list .nat) R.2.2 + 1) + 1 :=
    rfl
  have e2 : (R.1.length + R.2.1.length + R.2.2.length + 3) * (2 * W + 10) =
      R.1.length * (2 * W + 10) + R.2.1.length * (2 * W + 10) + R.2.2.length * (2 * W + 10) +
        3 * (2 * W + 10) := by ring
  have m1 : R.1.length * (2 * W + 6) ≤ R.1.length * (2 * W + 10) := Nat.mul_le_mul_left _ (by omega)
  have m2 : R.2.1.length * (W + 1) ≤ R.2.1.length * (2 * W + 10) := Nat.mul_le_mul_left _ (by omega)
  have m3 : R.2.2.length * (W + 1) ≤ R.2.2.length * (2 * W + 10) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem recInv_of_mag (R : Plain.RecP) : RecInv (mag TRec R) R := by
  have e : mag TRec R = mag TGates R.1 + (mag (.list .nat) R.2.1 + mag (.list .nat) R.2.2 + 1) + 1 :=
    rfl
  refine ⟨fun g hg => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · have h1 := mag_mem TGate hg
    have e2 : mag TGate g = g.2.2.1 + g.2.2.2 + 5 := by simp only [mag, magL]; omega
    omega
  · have := mag_mem .nat ha; simp only [mag_nat] at this; omega
  · have := mag_mem .nat ha; simp only [mag_nat] at this; omega

theorem sum_len_le_mag (rows : List (List Plain.Coord)) :
    (rows.map List.length).sum ≤ mag TRows rows := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    have := mag_list_len TCoord r
    simp only [List.map_cons, List.sum_cons]
    have e : mag TRows (r :: rows) = mag TRow r + 1 + mag TRows rows := rfl
    omega

theorem synth_inv (n v M : ℕ) (hv : v ≤ M) : ∀ (rows : List (List Plain.Coord)) (base : ℕ),
    base + rows.length ≤ M →
    RecInv (M + (Plain.synthesize n v base rows).1.length) (Plain.synthesize n v base rows) ∧
    (Plain.synthesize n v base rows).1.length = 1 + (rows.map List.length).sum ∧
    (Plain.synthesize n v base rows).2.1.length = n ∧ (Plain.synthesize n v base rows).2.2.length = n
  | [], base, _ => by
    simp only [Plain.synthesize, Plain.recZero, List.length_cons, List.length_nil,
      List.length_replicate, List.map_nil, List.sum_nil]
    refine ⟨⟨fun g hg => ?_, fun a ha => ?_, fun a ha => ?_⟩, by simp, by simp, by simp⟩
    · simp only [List.mem_singleton] at hg; subst hg; simp [Plain.constGate]
    · rw [List.eq_of_mem_replicate ha]; omega
    · rw [List.eq_of_mem_replicate ha]; omega
  | row :: rows, base, hb => by
    obtain ⟨i1, i2, i3, i4⟩ := synth_inv n v M hv rows (base + 1)
      (by simp only [List.length_cons] at hb; omega)
    obtain ⟨j1, j2, j3, j4⟩ := recAddRow_inv i1 hv (show base ≤ M by
      simp only [List.length_cons] at hb; omega) row
    simp only [Plain.synthesize, List.map_cons, List.sum_cons]
    refine ⟨j1.mono (by omega), by omega, by omega, by omega⟩

/-! ## Recursions -/

section Good
variable (x : Ix)

theorem setF_P : PolyB (setF x) := by
  refine ⟨_, _, polyB_chain (setF x) (fun p => p.1.length)
    (fun p => by have := mag_list_len .nat p.1; simp only [mag_prod]; omega)
    (K := 3) (C := 300) le_rfl (fun p => ?_)⟩
  obtain ⟨xs, (i : ℕ), (a : ℕ)⟩ := p
  set μ := mag (.prod (.list .nat) (.prod .nat .nat)) (xs, i, a) with hμ
  have L0 := le_G 2 300 μ
  have L1 : 100 * G 2 300 μ + 100 ≤ G 3 300 μ := G_lin100 2 300 μ le_rfl
  rcases xs with _ | ⟨(y : ℕ), ys⟩
  · left
    simp only [setF_cost, setF_depth, setF_msize, setF_den, setCost, setDepth, setMsize,
      List.set_nil]
    refine ⟨by omega, by omega, ?_, by omega⟩
    exact (le_of_eq (show mag (.list .nat) [] = 1 from rfl)).trans (by omega)
  · right
    have hy : mag (.prod (.list .nat) (.prod .nat .nat)) (ys, i - 1, a) ≤ μ := by
      rw [hμ]; simp only [mag, magL]; omega
    refine ⟨(ys, i - 1, a), by simp, hy, ?_⟩
    obtain ⟨p1, p2, p3, -⟩ := fnB_at (predF_B x.pred) (K := 2) (C := 300) le_rfl le_rfl
      (show mag .nat i ≤ μ by rw [hμ]; simp only [mag, magL]; omega)
    have z1 := sz_le (.list .nat) ((y :: ys).set i a)
    have z2 := sz_le (.prod (.list .nat) (.prod .nat .nat)) (ys, i - 1, a)
    have hpos := mag_list_len .nat ((y :: ys).set i a)
    simp only [setF_cost, setF_depth, setF_msize, setF_den, setCost, setDepth, setMsize]
    rcases i with _ | j
    · simp only [if_true, List.set_cons_zero]
      have e1 : mag (.list .nat) (a :: ys) = a + 1 + mag (.list .nat) ys := rfl
      have e2 : μ = y + 1 + mag (.list .nat) ys + (0 + a + 1) + 1 := rfl
      refine ⟨by omega, by omega, by omega, ?_⟩
      simp only [List.set_cons_zero] at z1 hpos
      omega
    · simp only [Nat.add_one_ne_zero, if_false, List.set_cons_succ, Nat.add_sub_cancel]
      have e1 : mag (.list .nat) (y :: ys.set j a) = y + 1 + mag (.list .nat) (ys.set j a) := rfl
      have e2 : μ = y + 1 + mag (.list .nat) ys + (j + 1 + a + 1) + 1 := rfl
      simp only [List.set_cons_succ] at z1 hpos
      simp only [Nat.add_sub_cancel] at p1 p2 p3 z2 hy
      refine ⟨by omega, by omega, by omega, by omega⟩

attribute [polyB] setF_P

@[polyB] theorem recZeroF_P : PolyB (recZeroF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, recZeroBody, Plain.recZero])
    (by simp [Tm.CallsP, recZeroBody, polyB])

@[polyB] theorem recAddIncF_P : PolyB (recAddIncF x) :=
  polyB_exact _ _ _
    (fun p => by
      obtain ⟨v, R, ⟨b, i⟩, c⟩ := p
      cases b <;> simp [tm_simp, recAddIncBody, incOld, incOuts, Plain.recAddInc])
    (by simp [Tm.CallsP, recAddIncBody, incOld, incOuts, polyB])

/-- The argument of the increments inside `recAddRow` is quadratically bounded. -/
theorem recAddRow_arg (v coeff : ℕ) (R : Plain.RecP) (c : Plain.Coord) (cs : List Plain.Coord) :
    mag (.prod .nat (.prod TRec (.prod TCoord .nat)))
        (v, Plain.recAddRow v R coeff cs, c, coeff) ≤
      G 2 43 (mag (.prod .nat (.prod .nat (.prod TRec TRow))) (v, coeff, R, c :: cs)) := by
  set μ := mag (.prod .nat (.prod .nat (.prod TRec TRow))) (v, coeff, R, c :: cs) with hμ
  have hR : mag TRec R ≤ μ := by rw [hμ]; simp only [mag_prod]; omega
  have hcs := mag_list_len TCoord cs
  have hcm : mag TCoord c + 1 + mag TRow cs ≤ mag TRow (c :: cs) := by
    have := mag_cons TCoord c cs; omega
  have hcR : mag TRow (c :: cs) ≤ μ := by rw [hμ]; simp only [mag_prod]; omega
  have hvc : v + coeff ≤ μ := by rw [hμ]; simp only [mag_prod, mag_nat]; omega
  have h0 := (recInv_of_mag R).mono (W' := μ + R.1.length) (by omega)
  obtain ⟨i1, i2, i3, i4⟩ := recAddRow_inv h0 (show v ≤ μ by omega) (show coeff ≤ μ by omega) cs
  have hm := mag_rec_le _ i1
  rw [i2, i3, i4] at hm
  have l1 := mag_list_len TGate R.1
  have l2 := mag_list_len .nat R.2.1
  have l3 := mag_list_len .nat R.2.2
  have eR : mag TRec R = mag TGates R.1 + (mag (.list .nat) R.2.1 + mag (.list .nat) R.2.2 + 1) + 1 :=
    rfl
  have q1 : (R.1.length + cs.length + R.2.1.length + R.2.2.length + 3) *
      (2 * (μ + R.1.length + cs.length) + 10) ≤ (4 * μ + 3) * (6 * μ + 10) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : (4 * μ + 3) * (6 * μ + 10) + 3 * μ + 3 ≤ 40 * ((μ + 1) * (μ + 1)) := by nlinarith
  have q3 := quad_le 43 μ
  have e : mag (.prod .nat (.prod TRec (.prod TCoord .nat))) (v, Plain.recAddRow v R coeff cs, c, coeff) =
      v + (mag TRec (Plain.recAddRow v R coeff cs) + (mag TCoord c + coeff + 1) + 1) + 1 := rfl
  rw [e]
  omega

set_option maxRecDepth 4096 in
theorem recAddRowF_P : PolyB (recAddRowF x) := by
  obtain ⟨ki, ci, hi⟩ := recAddIncF_P x
  refine ⟨_, _, polyB_chain (recAddRowF x) (fun p => p.2.2.2.length)
    (fun p => by have := mag_list_len TCoord p.2.2.2; simp only [mag_prod]; omega)
    (K := ki + 4) (C := ci + 343) (by omega) (fun p => ?_)⟩
  obtain ⟨(v : ℕ), (coeff : ℕ), R, cs⟩ := p
  set μ := mag (.prod .nat (.prod .nat (.prod TRec TRow))) (v, coeff, R, cs) with hμ
  have L0 := le_G (ki + 3) (ci + 343) μ
  have L1 : 100 * G (ki + 3) (ci + 343) μ + 100 ≤ G (ki + 4) (ci + 343) μ :=
    G_lin100 (ki + 3) (ci + 343) μ (by omega)
  have Q : G 2 43 μ ≤ G (ki + 3) (ci + 343) μ := G_mono (by omega) (by omega) le_rfl
  rcases cs with _ | ⟨c, cs⟩
  · left
    have hR : mag TRec R ≤ μ := by rw [hμ]; simp only [mag_prod]; omega
    simp only [recAddRowF_cost, recAddRowF_depth, recAddRowF_msize, recAddRowF_den,
      recAddRowCost, recAddRowDepth, recAddRowMsize, Plain.recAddRow]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · right
    have hy : mag (.prod .nat (.prod .nat (.prod TRec TRow))) (v, coeff, R, cs) ≤ μ := by
      rw [hμ]; simp only [mag_prod]; have := mag_cons TCoord c cs; omega
    refine ⟨(v, coeff, R, cs), by simp, hy, ?_⟩
    have ha := recAddRow_arg v coeff R c cs
    rw [← hμ] at ha
    have c1 : G ki ci (G 2 43 μ) ≤ G (ki + 3) (ci + 343) μ :=
      (G_comp ki ci 2 43 μ).trans (G_mono (by omega) (by omega) le_rfl)
    obtain ⟨a1, a2, a3, a4⟩ := hi (v, Plain.recAddRow v R coeff cs, c, coeff)
    have b1 := G_mono (k := ki) (c := ci) le_rfl le_rfl ha
    have z1 := sz_le (.prod .nat (.prod TRec (.prod TCoord .nat)))
      (v, Plain.recAddRow v R coeff cs, c, coeff)
    have z2 := sz_le (.prod .nat (.prod .nat (.prod TRec TRow))) (v, coeff, R, cs)
    simp only [recAddIncF_den] at a4
    simp only [recAddRowF_cost, recAddRowF_depth, recAddRowF_msize, recAddRowF_den,
      recAddRowCost, recAddRowDepth, recAddRowMsize, Plain.recAddRow]
    refine ⟨by omega, by omega, by omega, by omega⟩

attribute [polyB] recAddRowF_P

/-- The argument of the `recAddRow` call inside `synthesize` is quadratically bounded. -/
theorem synth_arg (n v base : ℕ) (row : List Plain.Coord) (rows : List (List Plain.Coord)) :
    mag (.prod .nat (.prod .nat (.prod TRec TRow)))
        (v, base, Plain.synthesize n v (base + 1) rows, row) ≤
      G 2 500 (mag (.prod .nat (.prod .nat (.prod .nat TRows))) (n, v, base, row :: rows)) := by
  set μ := mag (.prod .nat (.prod .nat (.prod .nat TRows))) (n, v, base, row :: rows) with hμ
  have hrows : mag TRows (row :: rows) ≤ μ := by rw [hμ]; simp only [mag_prod]; omega
  have hl := mag_list_len TRow (row :: rows)
  have hrow : mag TRow row + 2 ≤ mag TRows (row :: rows) := by
    have := mag_cons TRow row rows; have := mag_list_len TRow rows; omega
  have hs := sum_len_le_mag rows
  have hrs : mag TRows rows + 1 ≤ mag TRows (row :: rows) := by
    have := mag_cons TRow row rows; omega
  have hn : n + v + base ≤ μ := by rw [hμ]; simp only [mag_prod, mag_nat]; omega
  obtain ⟨i1, i2, i3, i4⟩ := synth_inv n v (2 * μ) (by omega) rows (base + 1)
    (by simp only [List.length_cons] at hl; omega)
  have hm := mag_rec_le _ i1
  rw [i2, i3, i4] at hm
  have q1 : (1 + (rows.map List.length).sum + n + n + 3) *
      (2 * (2 * μ + (1 + (rows.map List.length).sum)) + 10) ≤ (3 * μ + 4) * (6 * μ + 12) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : (3 * μ + 4) * (6 * μ + 12) + 3 * μ + 3 ≤ 500 * ((μ + 1) * (μ + 1)) := by nlinarith
  have q3 := quad_le 500 μ
  have e : mag (.prod .nat (.prod .nat (.prod TRec TRow)))
      (v, base, Plain.synthesize n v (base + 1) rows, row) =
      v + (base + (mag TRec (Plain.synthesize n v (base + 1) rows) + mag TRow row + 1) + 1) + 1 :=
    rfl
  rw [e]
  omega

/-- Magnitude of `synthesize` (quadratic). -/
theorem synth_mag (n v base : ℕ) (rows : List (List Plain.Coord)) :
    mag TRec (Plain.synthesize n v base rows) ≤
      G 2 500 (mag (.prod .nat (.prod .nat (.prod .nat TRows))) (n, v, base, rows)) := by
  set μ := mag (.prod .nat (.prod .nat (.prod .nat TRows))) (n, v, base, rows) with hμ
  have hl := mag_list_len TRow rows
  have hs := sum_len_le_mag rows
  have hrows : mag TRows rows ≤ μ := by rw [hμ]; simp only [mag_prod]; omega
  have hn : n + v + base ≤ μ := by rw [hμ]; simp only [mag_prod, mag_nat]; omega
  obtain ⟨i1, i2, i3, i4⟩ := synth_inv n v (2 * μ) (by omega) rows base (by omega)
  have hm := mag_rec_le _ i1
  rw [i2, i3, i4] at hm
  have q1 : (1 + (rows.map List.length).sum + n + n + 3) *
      (2 * (2 * μ + (1 + (rows.map List.length).sum)) + 10) ≤ (3 * μ + 4) * (6 * μ + 12) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : (3 * μ + 4) * (6 * μ + 12) ≤ 500 * ((μ + 1) * (μ + 1)) := by nlinarith
  have q3 := quad_le 500 μ
  omega

set_option maxRecDepth 4096 in
theorem synthesizeF_P : PolyB (synthesizeF x) := by
  obtain ⟨kr, cr, hr⟩ := recAddRowF_P x
  obtain ⟨kz, cz, hz⟩ := recZeroF_P x
  refine ⟨_, _, polyB_chain (synthesizeF x) (fun p => p.2.2.2.length)
    (fun p => by have := mag_list_len TRow p.2.2.2; simp only [mag_prod]; omega)
    (K := kr + kz + 4) (C := cr + cz + 800) (by omega) (fun p => ?_)⟩
  obtain ⟨(n : ℕ), (v : ℕ), (base : ℕ), rows⟩ := p
  set μ := mag (.prod .nat (.prod .nat (.prod .nat TRows))) (n, v, base, rows) with hμ
  have L0 := le_G (kr + kz + 3) (cr + cz + 800) μ
  have L1 : 100 * G (kr + kz + 3) (cr + cz + 800) μ + 100 ≤ G (kr + kz + 4) (cr + cz + 800) μ :=
    G_lin100 _ _ μ (by omega)
  have hres : mag TRec (Plain.synthesize n v base rows) ≤ G (kr + kz + 3) (cr + cz + 800) μ :=
    (synth_mag n v base rows).trans (G_mono (by omega) (by omega) le_rfl)
  rcases rows with _ | ⟨row, rows⟩
  · left
    obtain ⟨a1, a2, a3, -⟩ := fnB_at hz (K := kr + kz + 3) (C := cr + cz + 800) (by omega)
      (by omega) (show mag (.prod .nat .nat) (n, v) ≤ μ by
        rw [hμ]; simp only [mag_prod, mag_nat]; omega)
    have z1 := sz_le (.prod .nat .nat) (n, v)
    have hb := natSize_le base
    have hb2 : base ≤ μ := by rw [hμ]; simp only [mag_prod, mag_nat]; omega
    have hn : mag (.prod .nat .nat) (n, v) ≤ μ := by rw [hμ]; simp only [mag_prod, mag_nat]; omega
    simp only [synthesizeF_cost, synthesizeF_depth, synthesizeF_msize, synthesizeF_den,
      synthCost, synthDepth, synthMsize] at hres ⊢
    refine ⟨by omega, by omega, by omega, by omega⟩
  · right
    have hy : mag (.prod .nat (.prod .nat (.prod .nat TRows))) (n, v, base + 1, rows) ≤ μ := by
      rw [hμ]; simp only [mag_prod, mag_nat]
      have := mag_cons TRow row rows; have := mag_list_len TCoord row; omega
    refine ⟨(n, v, base + 1, rows), by simp, hy, ?_⟩
    have ha := synth_arg n v base row rows
    rw [← hμ] at ha
    have c1 : G kr cr (G 2 500 μ) ≤ G (kr + kz + 3) (cr + cz + 800) μ :=
      (G_comp kr cr 2 500 μ).trans (G_mono (by omega) (by omega) le_rfl)
    obtain ⟨a1, a2, a3, -⟩ := hr (v, base, Plain.synthesize n v (base + 1) rows, row)
    have b1 := G_mono (k := kr) (c := cr) le_rfl le_rfl ha
    obtain ⟨s1, s2, s3, -⟩ := fnB_at (succF_B x.succ) (K := kr + kz + 3) (C := cr + cz + 800)
      (by omega) (by omega) (show mag .nat base ≤ μ by rw [hμ]; simp only [mag_prod, mag_nat]; omega)
    have z1 := sz_le (.prod .nat (.prod .nat (.prod TRec TRow)))
      (v, base, Plain.synthesize n v (base + 1) rows, row)
    have z2 := sz_le (.prod .nat (.prod .nat (.prod .nat TRows))) (n, v, base + 1, rows)
    have Q : G 2 500 μ ≤ G (kr + kz + 3) (cr + cz + 800) μ := G_mono (by omega) (by omega) le_rfl
    simp only [synthesizeF_cost, synthesizeF_depth, synthesizeF_msize, synthesizeF_den,
      synthCost, synthDepth, synthMsize] at hres ⊢
    refine ⟨by omega, by omega, by omega, by omega⟩

attribute [polyB] synthesizeF_P

@[polyB] theorem condEqF_P : PolyB (condEqF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, condEqBody, Plain.condEq])
    (by simp [Tm.CallsP, condEqBody])

set_option maxRecDepth 4096 in
theorem condEqsF_P : PolyB (condEqsF x) := by
  obtain ⟨ke, ce, he⟩ := condEqF_P x
  refine ⟨_, _, polyB_chain (condEqsF x) (fun p => p.2.2.length)
    (fun p => by have := mag_list_len .nat p.2.2; simp only [mag_prod]; omega)
    (K := ke + 4) (C := ce + 300) (by omega) (fun p => ?_)⟩
  obtain ⟨(oz : ℕ), (i : ℕ), ss⟩ := p
  set μ := mag (.prod .nat (.prod .nat (.list .nat))) (oz, i, ss) with hμ
  have L0 := le_G (ke + 3) (ce + 300) μ
  have L1 : 100 * G (ke + 3) (ce + 300) μ + 100 ≤ G (ke + 4) (ce + 300) μ :=
    G_lin100 _ _ μ (by omega)
  rcases ss with _ | ⟨(s : ℕ), ss⟩
  · left
    simp only [condEqsF_cost, condEqsF_depth, condEqsF_msize, condEqsF_den, condEqsCost,
      condEqsDepth, condEqsMsize, Plain.condEqs]
    refine ⟨by omega, by omega, ?_, by omega⟩
    exact (le_of_eq (show mag TForm [] = 1 from rfl)).trans (by omega)
  · right
    have hy : mag (.prod .nat (.prod .nat (.list .nat))) (oz, i + 1, ss) ≤ μ := by
      rw [hμ]; simp only [mag, magL]; omega
    refine ⟨(oz, i + 1, ss), by simp, hy, ?_⟩
    have hz : mag (.prod .nat (.prod .nat .nat)) (i, s, oz + i) ≤ μ + μ := by
      rw [hμ]; simp only [mag, magL]; omega
    have D1 : 5 * (μ + 0) + 16 ≤ G 1 0 μ := G_succ 0 0 μ
    have c1 : G ke ce (G 1 0 μ) ≤ G (ke + 3) (ce + 300) μ :=
      (G_comp ke ce 1 0 μ).trans (G_mono (by omega) (by omega) le_rfl)
    obtain ⟨e1, e2, e3, e4⟩ := he (i, s, oz + i)
    have b1 := G_mono (k := ke) (c := ce) le_rfl le_rfl
      (show mag (.prod .nat (.prod .nat .nat)) (i, s, oz + i) ≤ G 1 0 μ by omega)
    obtain ⟨a1, a2, a3, -⟩ := fnB_at (addF_B x.add) (K := ke + 3) (C := ce + 300) (by omega)
      (by omega) (show mag (.prod .nat .nat) (oz, i) ≤ μ by rw [hμ]; simp only [mag, magL]; omega)
    obtain ⟨s1, s2, s3, -⟩ := fnB_at (succF_B x.succ) (K := ke + 3) (C := ce + 300) (by omega)
      (by omega) (show mag .nat i ≤ μ by rw [hμ]; simp only [mag, magL]; omega)
    have z1 := sz_le (.prod .nat (.prod .nat .nat)) (i, s, oz + i)
    have z2 := sz_le (.prod .nat (.prod .nat (.list .nat))) (oz, i + 1, ss)
    have z3 := sz_le TForm (Plain.condEqs oz i (s :: ss))
    have hap := mag_append_le TClause (Plain.condEq i s (oz + i)) (Plain.condEqs oz (i + 1) ss)
    have hpos := mag_list_len TClause (Plain.condEqs oz i (s :: ss))
    simp only [condEqF_den] at e4
    simp only [condEqsF_cost, condEqsF_depth, condEqsF_msize, condEqsF_den, condEqsCost,
      condEqsDepth, condEqsMsize]
    refine ⟨by omega, by omega, ?_, by omega⟩
    simp only [Plain.condEqs]
    omega

attribute [polyB] condEqsF_P

@[polyB] theorem cleaningF_P : PolyB (cleaningF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, cleaningBody, Plain.cleaning])
    (by simp [Tm.CallsP, cleaningBody, polyB])

@[polyB] theorem filterNonemptyCF_P : PolyB (filterNonemptyCF x) :=
  filterF_P (nonemptyF_P x _) _

@[polyB] theorem goodBlockF_P : PolyB (goodBlockF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, goodBlockBody, goodNorm, goodClean, Plain.goodBlock])
    (by simp [Tm.CallsP, goodBlockBody, goodNorm, goodClean, polyB])

end Good

end QecReliability.Trans.BoundsQH
