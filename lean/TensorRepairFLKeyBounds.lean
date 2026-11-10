import TensorRepairFL
import Trans.BoundsQH.HFold

/-! Polynomial resource bounds for the installed componentwise key comparator.
Here natural coordinates are bounded by their degree sum, so the existing
magnitude-based polynomial calculus is appropriate. Ratios require bit-size
bounds and are handled separately; their numerical magnitude is not substituted
for their encoding length. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib Trans.Wire
open Trans.Query.Bound Trans.BoundsQH

variable (L : Lib) (i : Indices)

theorem keyStepF_poly : PolyB (keyStepF L i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, keyStepBody, polyB])

private theorem keyStepR_mag (s : Key × Bool) (x : ℕ) :
    mag TKey (keyStepR s x).1 ≤ mag TKey s.1 := by
  rcases s with ⟨ys,b⟩
  cases ys with
  | nil => exact le_rfl
  | cons y ys =>
    change mag TKey ys ≤ y + 1 + mag TKey ys
    omega

theorem keyFold_poly : PolyB (foldlF (keyStepF L i) i.keyFold) := by
  refine foldl_polyB (keyStepF L i) i.keyFold (keyStepF_poly L i) (kR := 0) (cR := 2)
    (fun z xs => ⟨fun acc => mag TKey acc.1 ≤ mag TKey z.1, le_rfl, ?_, ?_⟩)
  · intro x hx acc hacc
    rcases acc with ⟨ys,b⟩
    rw [keyStepF_den]
    exact (keyStepR_mag (ys,b) x).trans hacc
  · intro acc hacc
    rw [G_zero]
    simp only [mag_prod, mag_bool]
    omega

theorem keyLeF_poly : PolyB (keyLeF L i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, keyLeBody, keyFold_poly])

theorem keyEqF_poly : PolyB (keyEqF L i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, keyEqBody, keyLeF_poly])

theorem indexList_mag (ds : List ℕ) (j : TensorBernstein.Grid ds) :
    mag TKey (TensorMachine.indexList ds j) ≤ ds.sum + ds.length + 1 := by
  induction ds with
  | nil => exact le_rfl
  | cons r ds ih =>
    have hj := Nat.le_of_lt_succ j.1.isLt
    have ht := ih j.2
    change j.1.val + 1 + mag TKey (TensorMachine.indexList ds j.2) ≤
      (r + ds.sum) + (ds.length + 1) + 1
    omega

/-- The actual key-comparison cost, depth and space are uniformly polynomial
in the degree-list structural parameters. -/
theorem keyLe_index_resources : ∃ k c, ∀ (ds : List ℕ) (a b : TensorBernstein.Grid ds),
    (keyLeF L i).cost (TensorMachine.indexList ds a,TensorMachine.indexList ds b) ≤
      G k c (2 * (ds.sum + ds.length + 1) + 1) ∧
    (keyLeF L i).depth (TensorMachine.indexList ds a,TensorMachine.indexList ds b) ≤
      G k c (2 * (ds.sum + ds.length + 1) + 1) ∧
    (keyLeF L i).msize (TensorMachine.indexList ds a,TensorMachine.indexList ds b) ≤
      G k c (2 * (ds.sum + ds.length + 1) + 1) := by
  obtain ⟨k,c,h⟩ := keyLeF_poly L i
  refine ⟨k,c,?_⟩
  intro ds a b
  obtain ⟨hcost,hdepth,hsize,_⟩ := h (TensorMachine.indexList ds a,TensorMachine.indexList ds b)
  have ha := indexList_mag ds a
  have hb := indexList_mag ds b
  have he := G_mono (k := k) (c := c) le_rfl le_rfl
    (show mag (.prod TKey TKey) (TensorMachine.indexList ds a,TensorMachine.indexList ds b) ≤
      2 * (ds.sum + ds.length + 1) + 1 by simp only [mag_prod]; omega)
  exact ⟨hcost.trans he,hdepth.trans he,hsize.trans he⟩

end QecReliability.TensorMachine.RepairFL
