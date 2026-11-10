import Trans.BoundsRest.Mag
import Trans.BoundsQH.HFold

/-!
# Trans.BoundsRest.EndPoly: the GF(2) rank pipeline is polynomially bounded

Every function of Control's endpoint (`Trans/Control/Rank.lean`) except the final doubling fold
(`2^a` has exponential magnitude) is `PolyB` (BoundsQH: cost, depth, msize and result magnitude
`≤ G k c (mag arg)`): the circuit run `runF` (accumulator length = start + steps), `maskOfF`,
the parity fold `parF` (accumulator shape fixed), `bitF`, `denseF`, `xorLF` (explicit bounds),
`clearF`, one elimination column `rankStepF`, the elimination `rankF` (rows only shrink, the
counter grows by `≤ 1` per column) and **`ambF_P`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.BoundsRest
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH
open QecReliability.Trans.Control
open QecReliability.Trans.Control.RankP
open QecReliability.Trans.Hash (mapEnvF)

/-! ## Bit lists -/

theorem mag_bools_eq (xs : List Bool) : mag (.list .bool) xs = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show mag .bool x + 1 + mag (.list .bool) xs = _
    rw [ih, mag_bool, List.length_cons]
    omega

theorem tail_len_le (x : List Bool) : x.tail.length ≤ x.length := by simp

theorem xorL_length_le : ∀ (a b : List Bool), (xorL a b).length ≤ a.length
  | a :: as, b :: bs => by
    have := xorL_length_le as bs
    simp only [xorL, List.length_cons]
    omega
  | [], _ => by simp [xorL]
  | _ :: _, [] => by simp [xorL]

theorem clearL_length_le (p x : List Bool) : (clearL p x).length ≤ x.length := by
  unfold clearL
  split
  · have := xorL_length_le x.tail p.tail
    have := tail_len_le x
    omega
  · exact tail_len_le x

theorem mag_map_shrink (f : List Bool → List Bool) (hf : ∀ x, (f x).length ≤ x.length) :
    ∀ rows : List (List Bool), mag (.list TBits) (rows.map f) ≤ mag (.list TBits) rows
  | [] => le_rfl
  | r :: rs => by
    have ih := mag_map_shrink f hf rs
    have h1 : mag TBits (f r) = 2 * (f r).length + 1 := mag_bools_eq (f r)
    have h2 : mag TBits r = 2 * r.length + 1 := mag_bools_eq r
    have h3 := hf r
    show mag TBits (f r) + 1 + mag (.list TBits) (rs.map f) ≤ mag TBits r + 1 + mag (.list TBits) rs
    omega

/-! ## `xorLF` -/

theorem xorLF_P (i : ℕ) : PolyB (xorLF i) := ⟨2, 300, fnB_quad _ _ fun p => by
  obtain ⟨a, b⟩ := p
  have h1 := xorL_length_le a b
  have ha := mag_bools_eq a
  have hb := mag_bools_eq b
  have hr := mag_bools_eq (xorL a b)
  have hs := sz_le (.prod (.list .bool) (.list .bool)) (a, b)
  have hX := sq_ge (mag (.prod (.list .bool) (.list .bool)) (a, b))
  simp only [mag_prod] at hs hX ⊢
  simp only [xorLF_cost, xorLF_depth, xorLF_msize, xorLF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega⟩

section Rank
variable (y : IxR)

/-! ## Circuit run and mask -/

theorem gateValF_P : PolyB (gateValF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, gateValBody, polyB])

theorem runStepF_P : PolyB (runStepF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, runStepBody, polyB, gateValF_P])

theorem runStep_len (vals : List Bool) (g : TGateP.den) :
    ((runStepF y).den (vals, g)).length = vals.length + 1 := by
  simp [runStepF, bodySig_den, runStepBody, tm_simp]

theorem runF_P : PolyB (runF y) := by
  refine foldl_polyB_idx (runStepF y) y.run (runStepF_P y) (kR := 2) (cR := 2)
    (fun z xs => ⟨fun n acc => acc.length = z.length + n, by simp,
      fun x _ n _ acc h => by dsimp only at h ⊢; rw [runStep_len, h]; omega,
      fun n hn acc h => ?_⟩)
  dsimp only at h
  have e1 : mag TBits acc = 2 * acc.length + 1 := mag_bools_eq acc
  have e2 : mag TBits z = 2 * z.length + 1 := mag_bools_eq z
  have e3 := mag_list_len TGateP xs
  have := lin_le 2 (mag (.prod TBits (.list TGateP)) (z, xs))
  simp only [mag_prod] at this ⊢
  omega

theorem lookF_P : PolyB (lookF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, lookBody, polyB])

theorem maskOfF_P : PolyB (maskOfF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, maskOfBody, polyB, runF_P, mapEnvH_P, lookF_P])

/-! ## Parities and dense rows -/

theorem parStepF_P : PolyB (parStepF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, parStepBody, polyB])

theorem parStep_fst (acc : (Ty.prod TCoord .bool).den) (c : TCoord.den) :
    ((parStepF y).den (acc, c)).1 = acc.1 := by
  simp [parStepF, bodySig_den, parStepBody, tm_simp]

theorem parFold_P : PolyB (foldlF (parStepF y) y.parFold) := by
  refine foldl_polyB (parStepF y) y.parFold (parStepF_P y) (kR := 0) (cR := 2)
    (fun z xs => ⟨fun acc => acc.1 = z.1, rfl,
      fun x _ acc h => by dsimp only at h ⊢; rw [parStep_fst, h], fun acc h => ?_⟩)
  dsimp only at h
  rw [G_zero]
  show mag TCoord acc.1 + mag .bool acc.2 + 1 ≤
    mag TCoord z.1 + mag .bool z.2 + 1 + mag (.list TCoord) xs + 1 + 2
  rw [h, mag_bool, mag_bool]
  omega

theorem parF_P : PolyB (parF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, parBody, polyB, parFold_P])

theorem bitF_P : PolyB (bitF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, bitBody, polyB, parF_P])

theorem denseF_P : PolyB (denseF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, denseBody, polyB, mapEnvH_P, bitF_P])

/-! ## Elimination -/

theorem headTF_P : PolyB (headTF y) := polyB_bodySig _ _ (by simp [Tm.CallsP, headTBody])
theorem tailBF_P : PolyB (tailBF y) := polyB_bodySig _ _ (by simp [Tm.CallsP, tailBBody])
theorem idBF_P : PolyB (idBF y) := polyB_bodySig _ _ (by simp [Tm.CallsP, idBBody])
theorem notBF_P : PolyB (notBF y) := polyB_bodySig _ _ (by simp [Tm.CallsP, notBBody])

theorem clearF_P : PolyB (clearF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, clearBody, headTF_P, tailBF_P, xorLF_P])

theorem rankStepF_P : PolyB (rankStepF y) :=
  polyB_bodySig _ _ (by
    simp [Tm.CallsP, rankStepBody, polyB, filterF_P, mapF_P, mapEnvH_P, headTF_P, tailBF_P,
      clearF_P])

theorem colStep_inv (s : List (List Bool) × ℕ) :
    mag (.list TBits) (colStep s).1 ≤ mag (.list TBits) s.1 ∧ (colStep s).2 ≤ s.2 + 1 := by
  unfold colStep
  split
  · exact ⟨mag_map_shrink _ (fun x => tail_len_le x) _, by simp⟩
  · exact ⟨mag_map_shrink _ (fun x => clearL_length_le _ x) _, by simp⟩

theorem rankFold_P : PolyB (foldlF (rankStepF y) y.rankFold) := by
  refine foldl_polyB_idx (rankStepF y) y.rankFold (rankStepF_P y) (kR := 0) (cR := 0)
    (fun z xs => ⟨fun n acc => mag (.list TBits) acc.1 ≤ mag (.list TBits) z.1 ∧
      (acc.2 : ℕ) ≤ (z.2 : ℕ) + n, ⟨le_rfl, by simp⟩, fun x _ n _ acc h => ?_,
      fun n hn acc h => ?_⟩)
  · obtain ⟨r1, (c1 : ℕ)⟩ := acc
    obtain ⟨r0, (c0 : ℕ)⟩ := z
    dsimp only at h ⊢
    rw [rankStep_den]
    obtain ⟨i1, i2⟩ := colStep_inv (r1, c1)
    generalize colStep (r1, c1) = cs at i1 i2 ⊢
    obtain ⟨r2, (c2 : ℕ)⟩ := cs
    dsimp only at i1 i2 h ⊢
    have h2 : c1 ≤ c0 + n := h.2
    have i2' : c2 ≤ c1 + 1 := i2
    refine ⟨i1.trans h.1, ?_⟩
    show c2 ≤ c0 + (n + 1)
    omega
  · obtain ⟨r1, (c1 : ℕ)⟩ := acc
    obtain ⟨r0, (c0 : ℕ)⟩ := z
    dsimp only at h
    have h1 := h.1
    have h2 : c1 ≤ c0 + n := h.2
    have e3 := mag_list_len .nat xs
    rw [G_zero]
    show mag (.list TBits) r1 + c1 + 1 ≤ mag (.list TBits) r0 + c0 + 1 + mag (.list .nat) xs + 1 + 0
    omega

theorem rankF_P : PolyB (rankF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, rankBody, polyB, rankFold_P])

/-- **The ambiguity rank is polynomially bounded.** -/
theorem ambF_P : PolyB (ambF y) :=
  polyB_bodySig _ _ (by
    simp [Tm.CallsP, ambBody, polyB, filterF_P, mapF_P, mapEnvH_P, idBF_P, notBF_P, rankF_P,
      denseF_P])

end Rank

end QecReliability.Trans.BoundsRest
