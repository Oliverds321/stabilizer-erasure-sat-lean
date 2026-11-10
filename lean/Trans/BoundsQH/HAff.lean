import Trans.BoundsQH.HTrans

/-!
# Trans.BoundsQH.HAff: local affine hashing (`abitF`, `affF`)

Wire invariants: `abitFold_inv` (the `abitStep` fold: gates `≤ #steps`, wires `≤ W + #gates`),
`abit_inv` (`Plain.abit`), `affFold_inv` (the `affStep` fold: renamed programs keep wires
`≤ X + #gates`, `tableWire (range v, v, v + a)` shifts by `≤ a`). Results: `abitFold_P`,
`abitF_P`, `affFold_P`, **`affF_P`** (the `aff` callee of `hash_on`).
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Hash QecReliability.Trans.Query.Plain

/-! ## The `abit` fold -/

theorem abitFold_inv (v W : ℕ) (gs0 : List GateP) (o0 : ℕ) (hv : v ≤ W)
    (h0 : (∀ g ∈ gs0, g.2.2.1 ≤ W + gs0.length ∧ g.2.2.2 ≤ W + gs0.length) ∧ o0 ≤ W + gs0.length) :
    ∀ xs : List (Bool × ℕ), (∀ x ∈ xs, x.2 ≤ W) →
    (xs.foldr abitStep (v, gs0, o0)).1 = v ∧
    (xs.foldr abitStep (v, gs0, o0)).2.1.length ≤ gs0.length + xs.length ∧
    (∀ g ∈ (xs.foldr abitStep (v, gs0, o0)).2.1,
      g.2.2.1 ≤ W + (xs.foldr abitStep (v, gs0, o0)).2.1.length ∧
      g.2.2.2 ≤ W + (xs.foldr abitStep (v, gs0, o0)).2.1.length) ∧
    (xs.foldr abitStep (v, gs0, o0)).2.2 ≤ W + (xs.foldr abitStep (v, gs0, o0)).2.1.length
  | [], _ => ⟨rfl, by simp, h0.1, h0.2⟩
  | x :: xs, hx => by
    obtain ⟨i1, i2, i3, i4⟩ := abitFold_inv v W gs0 o0 hv h0 xs (fun y hy => hx y (by simp [hy]))
    have hxW := hx x (by simp)
    simp only [List.foldr_cons]
    generalize xs.foldr abitStep (v, gs0, o0) = r at i1 i2 i3 i4
    obtain ⟨v', gs, o⟩ := r
    dsimp only at i1 i2 i3 i4
    subst i1
    unfold abitStep
    split
    · simp only [List.length_append, List.length_cons, List.length_nil, List.length_cons]
      refine ⟨by simp, by omega, fun g hg => ?_, by omega⟩
      rcases List.mem_append.mp hg with hg | hg
      · have := i3 g hg; omega
      · simp only [List.mem_singleton] at hg; subst hg; dsimp only; omega
    · simp only [List.length_cons]
      exact ⟨by simp, by omega, i3, i4⟩

theorem abitFold_P (iapp iadd ilen is i : ℕ) : PolyB (foldrF (abitStepF iapp iadd ilen is) i) := by
  refine foldr_polyB_res _ _ (abitStepF_P iapp iadd ilen is) (kR := 2) (cR := 20)
    (fun xs z => ?_)
  obtain ⟨(v : ℕ), (gs0 : List GateP), (o0 : ℕ)⟩ := z
  have hden : foldrDen (abitStepF iapp iadd ilen is) xs (v, gs0, o0) =
      xs.foldr abitStep (v, gs0, o0) := by
    simp only [foldrDen, abitStepF, exactSig_den]
  rw [hden]
  have hgs : ∀ g ∈ gs0, g.2.2.1 ≤ mag (.list TGate) gs0 ∧ g.2.2.2 ≤ mag (.list TGate) gs0 :=
    fun g hg => by
      have h1 := mag_mem TGate hg
      have e2 : mag TGate g = g.2.2.1 + g.2.2.2 + 5 := by simp only [mag, magL]; omega
      omega
  have hxs : ∀ x ∈ xs, x.2 ≤ v + mag (.list TGate) gs0 + o0 + mag (.list (.prod .bool .nat)) xs := by
    rintro ⟨c, (j : ℕ)⟩ hx
    have h1 := mag_mem (.prod .bool .nat) hx
    have h2 : mag (.prod .bool .nat) (c, j) = 1 + j + 1 := rfl
    show j ≤ _
    omega
  obtain ⟨i1, i2, i3, i4⟩ := abitFold_inv v (v + mag (.list TGate) gs0 + o0 +
    mag (.list (.prod .bool .nat)) xs) gs0 o0 (by omega)
    ⟨fun g hg => by have := hgs g hg; omega, by omega⟩ xs hxs
  generalize xs.foldr abitStep (v, gs0, o0) = r at i1 i2 i3 i4
  obtain ⟨(v' : ℕ), (gs : List GateP), (o : ℕ)⟩ := r
  dsimp only at i1 i2 i3 i4
  subst i1
  have hm : mag (.list TGate) gs ≤ gs.length * (2 * (v' + mag (.list TGate) gs0 + o0 +
      mag (.list (.prod .bool .nat)) xs + gs.length) + 6) + 1 := mag_gates_le gs i3
  have l1 := mag_list_len TGate gs0
  have l2 := mag_list_len (.prod .bool .nat) xs
  have e1 : mag TAb (v', gs, o) = v' + (mag (.list TGate) gs + o + 1) + 1 := rfl
  have e2 : mag (.prod (.list (.prod .bool .nat)) TAb) (xs, (v', gs0, o0)) =
      mag (.list (.prod .bool .nat)) xs + (v' + (mag (.list TGate) gs0 + o0 + 1) + 1) + 1 := rfl
  rw [e1, e2]
  generalize hm' : mag (.list (.prod .bool .nat)) xs + (v' + (mag (.list TGate) gs0 + o0 + 1) + 1)
    + 1 = m
  have q1 : gs.length * (2 * (v' + mag (.list TGate) gs0 + o0 + mag (.list (.prod .bool .nat)) xs +
      gs.length) + 6) ≤ (2 * m) * (6 * m + 6) := Nat.mul_le_mul (by omega) (by omega)
  have q2 : (2 * m) * (6 * m + 6) + 6 * m + 6 ≤ 20 * ((m + 1) * (m + 1)) := by nlinarith
  have q3 := quad_le 20 m
  omega

theorem abitF_P (iip iapp iadd ilen is ifo i : ℕ) :
    PolyB (abitF iip (foldrF (abitStepF iapp iadd ilen is) ifo) i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨v, cs, b, x0⟩ := x
      have h := abit_foldr v cs b x0
      cases b <;>
      · simp only [abitBody, tm_simp, foldrF_den, ipairsF_den, foldrDen, abitStepF, exactSig_den]
        simp only [constGate, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [show (fun x acc => abitStep (x : Bool × ℕ) acc) = abitStep from rfl, h])
    (by simp [Tm.CallsP, abitBody, polyB, abitFold_P])

/-! ## `abit` and the `affStep` fold -/

theorem abit_inv (v : ℕ) (b : Bool) : ∀ (cs : List Bool) (x0 : ℕ),
    (abit v cs b x0).1.length ≤ cs.length + 1 ∧
    (∀ g ∈ (abit v cs b x0).1, g.2.2.1 ≤ x0 + cs.length + v + (abit v cs b x0).1.length ∧
      g.2.2.2 ≤ x0 + cs.length + v + (abit v cs b x0).1.length) ∧
    (abit v cs b x0).2 ≤ v + (abit v cs b x0).1.length
  | [], x0 => by
    simp only [abit, List.length_cons, List.length_nil, List.mem_singleton]
    refine ⟨le_rfl, fun g hg => ?_, by omega⟩
    subst hg; simp only [constGate]; split <;> omega
  | c :: cs, x0 => by
    obtain ⟨i1, i2, i3⟩ := abit_inv v b cs (x0 + 1)
    simp only [abit, List.length_cons]
    split
    · simp only [List.length_append, List.length_cons, List.length_nil]
      refine ⟨by omega, fun g hg => ?_, by omega⟩
      rcases List.mem_append.mp hg with hg | hg
      · have := i2 g hg; omega
      · simp only [List.mem_singleton] at hg; subst hg; dsimp only; omega
    · refine ⟨by omega, fun g hg => ?_, by omega⟩
      have := i2 g hg; omega

theorem range_getD (v w : ℕ) (h : w < v) : (List.range v).getD w 0 = w := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_range]

theorem tableWire_shift (v a w : ℕ) : tableWire (List.range v, v, v + a) w ≤ w + a := by
  unfold tableWire
  dsimp only
  split
  · rename_i h; rw [range_getD v w h]; omega
  · omega

theorem gmapW_shift (v a : ℕ) (g : GateP) {W : ℕ} (h : g.2.2.1 ≤ W ∧ g.2.2.2 ≤ W) :
    (gmapW (tableWire (List.range v, v, v + a)) g).2.2.1 ≤ W + a ∧
      (gmapW (tableWire (List.range v, v, v + a)) g).2.2.2 ≤ W + a := by
  have s1 := tableWire_shift v a g.2.2.1
  have s2 := tableWire_shift v a g.2.2.2
  unfold gmapW
  split
  · split
    · omega
    · dsimp only; omega
  · dsimp only; omega

theorem affFold_inv (v t X : ℕ) (P : ProgP) (hP : PInv (X + P.1.length) P) :
    ∀ xs : List ((List Bool × Bool) × ℕ), (∀ x ∈ xs, t * x.2 + x.1.1.length + v + 1 ≤ X) →
    (xs.foldr affStep (v, t, P)).1 = v ∧ (xs.foldr affStep (v, t, P)).2.1 = t ∧
    PInv (X + (xs.foldr affStep (v, t, P)).2.2.1.length) (xs.foldr affStep (v, t, P)).2.2 ∧
    (xs.foldr affStep (v, t, P)).2.2.1.length ≤ P.1.length + mag (.list (.prod TRow .nat)) xs ∧
    (xs.foldr affStep (v, t, P)).2.2.2.length = P.2.length + xs.length
  | [], _ => ⟨by simp, by simp, hP, by simp, by simp⟩
  | x :: xs, hx => by
    obtain ⟨i1, i2, i3, i4, i5⟩ := affFold_inv v t X P hP xs (fun y hy => hx y (by simp [hy]))
    have hxX := hx x (by simp)
    have hmx : x.1.1.length + 1 + mag (.list (.prod TRow .nat)) xs ≤
        mag (.list (.prod TRow .nat)) (x :: xs) := by
      have h1 := mag_list_len .bool x.1.1
      have e : mag (.list (.prod TRow .nat)) (x :: xs) =
          (mag (.list .bool) x.1.1 + 1 + 1) + x.2 + 1 + 1 + mag (.list (.prod TRow .nat)) xs := rfl
      omega
    simp only [List.foldr_cons, List.length_cons]
    generalize xs.foldr affStep (v, t, P) = r at i1 i2 i3 i4 i5
    obtain ⟨v', t', Q⟩ := r
    dsimp only at i1 i2 i3 i4 i5
    subst i1 i2
    obtain ⟨a1, a2, a3⟩ := abit_inv v' x.1.2 x.1.1 (t' * x.2)
    unfold affStep
    dsimp only
    generalize abit v' x.1.1 x.1.2 (t' * x.2) = A at a1 a2 a3
    have hlg : (tabGates (List.range v', v', v' + A.1.length) Q.1).length = Q.1.length := by
      simp [tabGates]
    have hlw : (tabWires (List.range v', v', v' + A.1.length) Q.2).length = Q.2.length := by
      simp [tabWires]
    simp only [List.length_append, hlg, List.length_cons, hlw]
    refine ⟨by simp, by simp, ⟨fun g hg => ?_, fun o ho => ?_⟩, by omega, by omega⟩
    · rcases List.mem_append.mp hg with hg | hg
      · have := a2 g hg; omega
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        have := gmapW_shift v' A.1.length g' (i3.1 g' hg')
        omega
    · rcases List.mem_cons.mp ho with rfl | ho
      · omega
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have := tableWire_shift v' A.1.length o'
        have := i3.2 o' ho'
        omega

theorem affFold_P {iabit : FnSig (.prod .nat (.prod (.list .bool) (.prod .bool .nat)))
    (.prod (.list TGate) .nat)} {imul irange iadd ilen iapp : ℕ}
    {itg : FnSig (.prod TTab (.list TGate)) (.list TGate)}
    {itw : FnSig (.prod TTab (.list .nat)) (.list .nat)} (habit : PolyB iabit)
    (habitd : ∀ x, iabit.den x = abit x.1 x.2.1 x.2.2.1 x.2.2.2) (htg : PolyB itg)
    (htw : PolyB itw) (htgd : ∀ x, itg.den x = tabGates x.1 x.2)
    (htwd : ∀ x, itw.den x = tabWires x.1 x.2) (is i : ℕ) :
    PolyB (foldrF (affStepF iabit imul irange iadd ilen iapp itg itw is) i) := by
  refine foldr_polyB_res _ _ (affStepF_P habit habitd htg htw htgd htwd is) (kR := 4) (cR := 300)
    (fun xs z => ?_)
  obtain ⟨(v : ℕ), (t : ℕ), P⟩ := z
  have hden : foldrDen (affStepF iabit imul irange iadd ilen iapp itg itw is) xs (v, t, P) =
      xs.foldr affStep (v, t, P) := by
    simp only [foldrDen, affStepF, exactSig_den]
  rw [hden]
  generalize hM : mag (.list (.prod TRow .nat)) xs = M
  have hxs : ∀ x ∈ xs, t * x.2 + x.1.1.length + v + 1 ≤ v + t * M + M + mag TProg P + 1 := by
    rintro ⟨⟨row, b⟩, (i : ℕ)⟩ hx
    have h1 := mag_mem (.prod TRow .nat) hx
    have h2 := mag_list_len .bool row
    have e : mag (.prod TRow .nat) ((row, b), i) = (mag (.list .bool) row + 1 + 1) + i + 1 := rfl
    have h3 : t * i ≤ t * M := Nat.mul_le_mul_left _ (by omega)
    show t * i + row.length + v + 1 ≤ _
    omega
  obtain ⟨i1, i2, i3, i4, i5⟩ := affFold_inv v t (v + t * M + M + mag TProg P + 1) P
    ((pinv_of_mag P).mono (by omega)) xs hxs
  generalize xs.foldr affStep (v, t, P) = r at i1 i2 i3 i4 i5
  obtain ⟨v', t', Q⟩ := r
  dsimp only at i1 i2 i3 i4 i5
  subst i1 i2
  rw [hM] at i4
  have hm : mag TProg Q ≤ (Q.1.length + Q.2.length + 2) *
      (2 * (v' + t' * M + M + mag TProg P + 1 + Q.1.length) + 10) := mag_prog_le _ i3
  have l1 := mag_list_len TGate P.1
  have l2 := mag_list_len .nat P.2
  have l3 := mag_list_len (.prod TRow .nat) xs
  rw [hM] at l3
  have eP : mag TProg P = mag (.list TGate) P.1 + mag (.list .nat) P.2 + 1 := rfl
  have e1 : mag TAf (v', t', Q) = v' + (t' + mag TProg Q + 1) + 1 := rfl
  have e2 : mag (.prod (.list (.prod TRow .nat)) TAf) (xs, (v', t', P)) =
      mag (.list (.prod TRow .nat)) xs + (v' + (t' + mag TProg P + 1) + 1) + 1 := rfl
  rw [e2, hM]
  generalize hm' : M + (v' + (t' + mag TProg P + 1) + 1) + 1 = m
  have hP2 := sq_ge m
  have htM : t' * M ≤ (m + 1) * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
  generalize hP2d : (m + 1) * (m + 1) = P2 at hP2 htM
  have q1 : (Q.1.length + Q.2.length + 2) *
      (2 * (v' + t' * M + M + mag TProg P + 1 + Q.1.length) + 10) ≤ (5 * P2) * (24 * P2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : (5 * P2) * (24 * P2) = 120 * (P2 * P2) := by ring
  have g1 : (m + 300 + 1) * (m + 300 + 1) + 16 ≤ G 1 300 m := G_sq 0 300 m
  have g1' : P2 ≤ G 1 300 m := by
    have : (m + 1) * (m + 1) ≤ (m + 300 + 1) * (m + 300 + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have g2 : P2 * P2 ≤ G 2 300 m := by
    have : (G 1 300 m + 1) * (G 1 300 m + 1) + 16 ≤ G 2 300 m := G_sq 1 300 m
    have : P2 * P2 ≤ (G 1 300 m + 1) * (G 1 300 m + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have g3 : 100 * G 2 300 m + 100 ≤ G 3 300 m := G_lin100 2 300 m le_rfl
  have g4 : 5 * G 3 300 m + 16 ≤ G 4 300 m := G_succ 3 300 m
  have g12 : G 1 300 m ≤ G 2 300 m := G_mono (by omega) le_rfl le_rfl
  omega

/-- **The `aff` callee of `hash_on` is polynomially bounded.** -/
theorem affF_P {iabit : FnSig (.prod .nat (.prod (.list .bool) (.prod .bool .nat)))
    (.prod (.list TGate) .nat)} {imul irange iadd ilen iapp : ℕ}
    {itg : FnSig (.prod TTab (.list TGate)) (.list TGate)}
    {itw : FnSig (.prod TTab (.list .nat)) (.list .nat)} (habit : PolyB iabit)
    (habitd : ∀ x, iabit.den x = abit x.1 x.2.1 x.2.2.1 x.2.2.2) (htg : PolyB itg)
    (htw : PolyB itw) (htgd : ∀ x, itg.den x = tabGates x.1 x.2)
    (htwd : ∀ x, itw.den x = tabWires x.1 x.2) (iip is ifo i : ℕ) :
    PolyB (affF iip (foldrF (affStepF iabit imul irange iadd ilen iapp itg itw is) ifo) i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨v, t, i0, rows⟩ := x
      have h := affP_foldr v t i0 rows
      have hFd : ∀ x, (affStepF iabit imul irange iadd ilen iapp itg itw is).den x =
          affStep x.1 x.2 := fun x => by simp only [affStepF, exactSig_den]
      simp only [affBody, tm_simp, foldrF_den, ipairsF_den, foldrDen, hFd]
      rw [show (fun x acc => affStep (x : (List Bool × Bool) × ℕ) acc) = affStep from rfl, h])
    (by simp [Tm.CallsP, affBody, polyB, affFold_P habit habitd htg htw htgd htwd is ifo])

end QecReliability.Trans.BoundsQH
