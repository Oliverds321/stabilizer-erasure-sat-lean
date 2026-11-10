import Trans.BoundsRest.Mag
import Trans.BoundsQH.HFold

/-!
# Trans.BoundsRest.InitMany: the repetition reader `manyF` along well-formed inputs

`Wire.manyF F (k, bs)` folds `k` calls of the item reader `F` over `range k`. Its cost depends
on `k`, which is a header value read from the input; at the machine input the header is a real
count and the input is `xs.flatMap enc ++ rest` with `k = xs.length`. **`many_bounds`**: if
`F` reads back `enc x` (`F (enc x ++ r) = (g x, r)`) and is bounded by `K D M` at every
suffix `(xs.drop j).flatMap enc ++ rest` actually visited, then `manyF` costs
`≤ (K + 40) k + 60 (k+1)² + 100`, depth `≤ 2k + D + 20`, size budget
`≤ 3M + 20 (k+1)² + 15·mag (xs.map g) + 6·size(bs) + 100` (the fold's states are a reversed
prefix of the result and a suffix of the input; `BoundsQH.foldl_bounds_idx`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.BoundsRest
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH (foldl_bounds_idx sz_le mag_take mag_reverse)
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_cost bodySig_depth bodySig_msize)
open QecReliability.Trans.Wire (manyF manyStepF manyBody manyStepBody)

theorem suffix_flatMap {β : Type} (enc : β → List Bool) (xs : List β) (rest : List Bool) (j : ℕ) :
    ((xs.drop j).flatMap enc ++ rest) <:+ (xs.flatMap enc ++ rest) := by
  have e : xs.flatMap enc ++ rest = (xs.take j).flatMap enc ++ ((xs.drop j).flatMap enc ++ rest) := by
    rw [← List.append_assoc, ← List.flatMap_append, List.take_append_drop]
  rw [e]
  exact List.suffix_append _ _

theorem sz_suffix {l1 l2 : List Bool} (h : l1 <:+ l2) :
    (Ty.enc (.list .bool) l1).size ≤ (Ty.enc (.list .bool) l2).size :=
  Ty.sz_sublist .bool h.sublist

section Many
variable (WL : Wire.Lib) {t : Ty} (F : FnSig (.list .bool) (.prod t (.list .bool)))
  (iStep iFold i : ℕ)

theorem manyStep_den (st : (Ty.prod (.list t) (.list .bool)).den) (j : ℕ) :
    (manyStepF F iStep).den (st, j) = ((F.den st.2).1 :: st.1, (F.den st.2).2) := by
  simp [manyStepF, bodySig_den, manyStepBody, tm_simp]

theorem manyStep_bounds (st : (Ty.prod (.list t) (.list .bool)).den) (j : ℕ) :
    (manyStepF F iStep).cost (st, j) ≤ F.cost st.2 + 20 ∧
      (manyStepF F iStep).depth (st, j) ≤ F.depth st.2 + 2 ∧
      (manyStepF F iStep).msize (st, j) ≤
        F.msize st.2 + (Ty.enc (.prod (.list t) (.list .bool)) ((manyStepF F iStep).den (st, j))).size := by
  rw [manyStep_den]
  obtain ⟨acc, bs⟩ := st
  refine ⟨?_, ?_, ?_⟩
  · simp [manyStepF, bodySig_cost, manyStepBody, tm_simp]; omega
  · simp [manyStepF, bodySig_depth, manyStepBody, tm_simp]
  · simp only [manyStepF, bodySig_msize, manyStepBody, Tm.msize, Tm.den, Env.get,
      max_le_iff]
    have e : (Ty.enc (.list t) ((F.den bs).1 :: acc)).size ≤
        (Ty.enc (.prod (.list t) (.list .bool)) ((F.den bs).1 :: acc, (F.den bs).2)).size := by
      rw [Ty.sz_prod]; dsimp only; omega
    refine ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩

/-- The state of `manyF`'s fold after `j` items. -/
def manySt {β : Type} (enc : β → List Bool) (g : β → t.den) (xs : List β) (rest : List Bool)
    (j : ℕ) : (Ty.prod (.list t) (.list .bool)).den :=
  (((xs.take j).map g).reverse, (xs.drop j).flatMap enc ++ rest)

theorem manySt_step {β : Type} (enc : β → List Bool) (g : β → t.den)
    (hf : ∀ x r, F.den (enc x ++ r) = (g x, r)) (xs : List β) (rest : List Bool) (j x : ℕ)
    (hj : j < xs.length) :
    (manyStepF F iStep).den (manySt enc g xs rest j, x) = manySt enc g xs rest (j + 1) := by
  rw [manyStep_den]
  simp only [manySt]
  rw [List.drop_eq_getElem_cons hj, List.flatMap_cons, List.append_assoc, hf,
    List.take_succ_eq_append_getElem hj, List.map_append, List.reverse_append]
  rfl

theorem manySt_size {β : Type} (enc : β → List Bool) (g : β → t.den) (xs : List β)
    (rest : List Bool) (j : ℕ) :
    (Ty.enc (.prod (.list t) (.list .bool)) (manySt enc g xs rest j)).size ≤
      5 * mag (.list t) (xs.map g) + 1 + (Ty.enc (.list .bool) (xs.flatMap enc ++ rest)).size + 1 := by
  have h1 := sz_le (.list t) ((xs.take j).map g).reverse
  have h2 : mag (.list t) ((xs.take j).map g).reverse ≤ mag (.list t) (xs.map g) := by
    rw [mag_reverse, List.map_take]
    exact mag_take t _ _
  have h3 := sz_suffix (suffix_flatMap enc xs rest j)
  simp only [manySt]
  rw [Ty.sz_prod]
  dsimp only
  omega

/-- **`manyF` along a well-formed input.** -/
theorem many_bounds {β : Type} (enc : β → List Bool) (g : β → t.den)
    (hf : ∀ x r, F.den (enc x ++ r) = (g x, r)) (xs : List β) (rest : List Bool) (K D M : ℕ)
    (hF : ∀ j, j < xs.length → F.cost ((xs.drop j).flatMap enc ++ rest) ≤ K ∧
      F.depth ((xs.drop j).flatMap enc ++ rest) ≤ D ∧
      F.msize ((xs.drop j).flatMap enc ++ rest) ≤ M) :
    (manyF WL F iStep iFold i).cost (xs.length, xs.flatMap enc ++ rest) ≤
        (K + 60) * xs.length + 60 * ((xs.length + 1) * (xs.length + 1)) + 100 ∧
      (manyF WL F iStep iFold i).depth (xs.length, xs.flatMap enc ++ rest) ≤
        2 * xs.length + D + 20 ∧
      (manyF WL F iStep iFold i).msize (xs.length, xs.flatMap enc ++ rest) ≤
        3 * M + 20 * ((xs.length + 1) * (xs.length + 1)) + 3 * (5 * mag (.list t) (xs.map g) + 1) +
          6 * (Ty.enc (.list .bool) (xs.flatMap enc ++ rest)).size + 100 := by
  have hz : manySt enc g xs rest 0 = ([], xs.flatMap enc ++ rest) := by simp [manySt]
  obtain ⟨f1, f2, f3, f4, f5⟩ := foldl_bounds_idx (manyStepF F iStep)
    (fun j st => j ≤ xs.length ∧ st = manySt enc g xs rest j) (K + 20) (D + 2)
    (M + (5 * mag (.list t) (xs.map g) + 1) + (Ty.enc (.list .bool) (xs.flatMap enc ++ rest)).size
      + 20) xs.length
    (List.range xs.length) ([], xs.flatMap enc ++ rest) 0 (by simp)
    ⟨Nat.zero_le _, hz.symm⟩ (by rw [← hz]; have := manySt_size enc g xs rest 0; omega)
    (fun x _ j hj acc hacc _ => by
      obtain ⟨-, rfl⟩ := hacc
      have hs := manySt_size enc g xs rest (j + 1)
      obtain ⟨c1, c2, c3⟩ := manyStep_bounds F iStep (manySt enc g xs rest j) x
      obtain ⟨d1, d2, d3⟩ := hF j hj
      have e2 : (manySt enc g xs rest j).2 = (xs.drop j).flatMap enc ++ rest := rfl
      rw [e2] at c1 c2 c3
      rw [manySt_step F iStep enc g hf xs rest j x hj] at c3 ⊢
      exact ⟨⟨by omega, rfl⟩, by omega, by omega, by omega, by omega⟩)
  simp only [List.length_range, Nat.zero_add] at f1 f3 f4 f5
  obtain ⟨-, hfin⟩ := f1
  have hfin' : foldlDen (manyStepF F iStep) ([], xs.flatMap enc ++ rest) (List.range xs.length) =
      ((xs.map g).reverse, rest) := by
    rw [hfin]; simp [manySt]
  have hSr := Bounds.sz_range_le xs.length
  have hks := NatSize.size_le_self xs.length
  have hsq : xs.length * (4 * xs.length + 2) ≤ 6 * ((xs.length + 1) * (xs.length + 1)) := by
    nlinarith
  have hrc : 60 * (xs.length + 1) * (xs.length.size + 1) ≤ 60 * ((xs.length + 1) * (xs.length + 1)) := by
    have := Nat.mul_le_mul (le_refl (xs.length + 1)) (show xs.length.size + 1 ≤ xs.length + 1 by omega)
    nlinarith
  have hlsq : xs.length + 1 ≤ (xs.length + 1) * (xs.length + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hKk : (K + 20 + 12) * xs.length + 15 * xs.length ≤ (K + 60) * xs.length := by nlinarith
  have hfs : (Ty.enc (.prod (.list t) (.list .bool)) ((xs.map g).reverse, rest)).size ≤
      (5 * mag (.list t) (xs.map g) + 1) + (Ty.enc (.list .bool) (xs.flatMap enc ++ rest)).size + 1 := by
    have := manySt_size enc g xs rest xs.length
    simp only [manySt] at this
    rw [List.take_of_length_le (le_refl _), List.drop_of_length_le (le_refl _), List.flatMap_nil,
      List.nil_append] at this
    omega
  have hrl : ((xs.map g).reverse).length = xs.length := by simp
  have hsz0 : (Ty.enc (.prod (.prod (.list t) (.list .bool)) (.list .nat))
      (([], xs.flatMap enc ++ rest), List.range xs.length)).size ≤
        (Ty.enc (.list .bool) (xs.flatMap enc ++ rest)).size +
          (Ty.enc (.list .nat) (List.range xs.length)).size + 3 := by
    rw [Bounds.shape2, Bounds.shape2, Ty.sz_list_nil]; omega
  have e2 : (Ty.enc (.prod (.list t) (.list .bool)) ([], xs.flatMap enc ++ rest)).size =
      (Ty.enc (.list .bool) (xs.flatMap enc ++ rest)).size + 2 := by
    rw [Bounds.shape2, Ty.sz_list_nil]; omega
  have hrev : (Ty.enc (.list t) (xs.map g).reverse).size ≤ 5 * mag (.list t) (xs.map g) + 1 := by
    have := sz_le (.list t) (xs.map g).reverse; rw [mag_reverse] at this; omega
  have hrv : (Ty.enc (.prod (.list t) (.list .bool)) ((xs.map g).reverse.reverse, rest)).size ≤
      (5 * mag (.list t) (xs.map g) + 1) + (Ty.enc (.list .bool) (xs.flatMap enc ++ rest)).size + 1 := by
    have hrest : (Ty.enc (.list .bool) rest).size ≤ (Ty.enc (.list .bool) (xs.flatMap enc ++ rest)).size :=
      sz_suffix (List.suffix_append _ _)
    have := sz_le (.list t) (xs.map g)
    rw [List.reverse_reverse, Bounds.shape2]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [manyF, bodySig_cost, manyBody, Tm.cost, Tm.den, Env.get, foldlF_cost,
      foldlF_den, rangeF_cost, rangeF_den, reverseF_cost]
    rw [hfin', hrl]
    generalize foldlCost (manyStepF F iStep) ([], xs.flatMap enc ++ rest) (List.range xs.length) = fc
      at f3 ⊢
    omega
  · simp only [manyF, bodySig_depth, manyBody, Tm.depth, Tm.den, Env.get, foldlF_depth,
      foldlF_den, rangeF_depth, rangeF_den, reverseF_depth]
    rw [hfin', hrl]
    generalize foldlDepth (manyStepF F iStep) ([], xs.flatMap enc ++ rest) (List.range xs.length) = fd
      at f4 ⊢
    omega
  · simp only [manyF, bodySig_msize, manyBody, Tm.msize, Tm.den, Env.get, foldlF_msize,
      foldlF_den, rangeF_msize, rangeF_den, reverseF_msize, reverseF_den]
    rw [hfin']
    dsimp only
    generalize foldlMsize (manyStepF F iStep) ([], xs.flatMap enc ++ rest) (List.range xs.length) = fm
      at f5 ⊢
    simp only [max_le_iff]
    repeat' apply And.intro
    all_goals omega

end Many

end QecReliability.Trans.BoundsRest
