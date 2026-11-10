import TensorMachineGridBounds
import PhysicalBridge.RationalTensorRepair
import QecReliability.TensorLayers

/-! Exact ordering bridge between typed coefficients and the runtime grid. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine
open TensorBernstein

theorem indexList_eq_latent (ds : List ℕ) (j : Grid ds) :
    indexList ds j = TensorLatent.indexList ds j := by
  induction ds with
  | nil => rfl
  | cons r ds ih => exact congrArg (j.1.val :: ·) (ih j.2)

set_option backward.isDefEq.respectTransparency false in
theorem enum_map_indexList (ds : List ℕ) :
    (RationalTensorRepair.enum ds).map (indexList ds) = grid ds := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    have hr : (List.finRange (r+1)).map Fin.val = List.range (r+1) := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Fin.val_cast]
    simp only [RationalTensorRepair.enum, List.map_flatMap, List.map_map, Function.comp_def]
    change (List.finRange (r+1)).flatMap
      (fun j => (RationalTensorRepair.enum ds).map (fun k => j.val :: indexList ds k)) = _
    have hm : ∀ j : Fin (r+1),
        (RationalTensorRepair.enum ds).map (fun k => j.val :: indexList ds k) =
          (grid ds).map (j.val :: ·) := by
      intro j
      rw [← ih, List.map_map]
      rfl
    simp_rw [hm]
    rw [grid, ← hr, List.flatMap_map]

def ordinalIndex (ds : List ℕ) (j : Fin (slots ds)) : Grid ds :=
  (RationalTensorRepair.enum ds).get
    ⟨j.val, by simpa only [RationalTensorRepair.enum_length, slots] using j.isLt⟩

theorem grid_get_ordinal (ds : List ℕ) (j : Fin (slots ds)) :
    (grid ds).get ⟨j.val, by simpa only [grid_length] using j.isLt⟩ =
      indexList ds (ordinalIndex ds j) := by
  have h := congrArg (fun xs : List (List ℕ) => xs[j.val]?) (enum_map_indexList ds)
  have hi : j.val < (RationalTensorRepair.enum ds).length := by
    simpa only [RationalTensorRepair.enum_length, slots] using j.isLt
  have hg : j.val < (grid ds).length := by simpa only [grid_length] using j.isLt
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hg, Option.map_some, Option.some.injEq,
    ordinalIndex, List.get_eq_getElem] using h.symm

theorem ordinalIndex_surjective (ds : List ℕ) : Function.Surjective (ordinalIndex ds) := by
  intro j
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (RationalTensorRepair.mem_enum ds j)
  refine ⟨⟨i.val, ?_⟩, ?_⟩
  · simpa only [RationalTensorRepair.enum_length, slots] using i.isLt
  · exact hi

theorem grid_getD_ordinal (ds : List ℕ) (j : Fin (slots ds)) :
    (grid ds).getD j.val [] = indexList ds (ordinalIndex ds j) := by
  have hi : j.val < (grid ds).length := by simpa only [grid_length] using j.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact grid_get_ordinal ds j

end QecReliability.TensorMachine
