import QecReliability.TensorBernstein
import Trans.Wire.Parse

/-! Executable, list-based coefficient tables for the tensor machine. The first
class is the outermost loop. Bounds explicitly retain the table cardinality;
the number of classes is not assumed constant. -/

namespace QecReliability.TensorMachine

open TensorBernstein

/-- The number of coefficient slots, including the unique empty tuple. -/
def slots (ds : List ℕ) : ℕ := (ds.map (fun r => r + 1)).prod

/-- A runtime grid uses only natural-number lists, with no dependent data on tape. -/
def grid : List ℕ → List (List ℕ)
  | [] => [[]]
  | r :: ds => (List.range (r + 1)).flatMap (fun j => (grid ds).map (j :: ·))

/-- Runtime coordinate validation, including the length check. -/
def ValidIndex : List ℕ → List ℕ → Prop
  | [], [] => True
  | r :: ds, j :: js => j ≤ r ∧ ValidIndex ds js
  | _, _ => False

/-- Serialization of a typed tensor index. -/
def indexList : (ds : List ℕ) → Grid ds → List ℕ
  | [], _ => []
  | _ :: ds, j => j.1.val :: indexList ds j.2

@[simp] theorem slots_nil : slots [] = 1 := rfl
@[simp] theorem slots_cons (r : ℕ) (ds : List ℕ) :
    slots (r :: ds) = (r + 1) * slots ds := rfl

private theorem length_expand (hs : List ℕ) (xs : List (List ℕ)) :
    (hs.flatMap (fun j => xs.map (j :: ·))).length = hs.length * xs.length := by
  induction hs with
  | nil => simp
  | cons h hs ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem grid_length (ds : List ℕ) : (grid ds).length = slots ds := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    rw [grid, length_expand, List.length_range, ih, slots_cons]

theorem mem_grid_iff (ds js : List ℕ) : js ∈ grid ds ↔ ValidIndex ds js := by
  induction ds generalizing js with
  | nil => cases js <;> simp [grid, ValidIndex]
  | cons r ds ih =>
    cases js with
    | nil => simp [grid, ValidIndex]
    | cons j js =>
      simp [grid, ValidIndex, List.mem_flatMap, List.mem_map, ih, Nat.lt_succ_iff]

theorem indexList_valid (ds : List ℕ) (j : Grid ds) : ValidIndex ds (indexList ds j) := by
  induction ds with
  | nil => trivial
  | cons r ds ih => exact ⟨Nat.le_of_lt_succ j.1.isLt, ih j.2⟩

theorem indexList_mem_grid (ds : List ℕ) (j : Grid ds) : indexList ds j ∈ grid ds :=
  (mem_grid_iff ds _).mpr (indexList_valid ds j)

theorem validIndex_iff_typed (ds js : List ℕ) :
    ValidIndex ds js ↔ ∃ j : Grid ds, indexList ds j = js := by
  induction ds generalizing js with
  | nil =>
    cases js with
    | nil => exact ⟨fun _ => ⟨PUnit.unit, rfl⟩, fun _ => trivial⟩
    | cons j js => simp [ValidIndex, indexList]
  | cons r ds ih =>
    cases js with
    | nil => simp [ValidIndex, indexList]
    | cons j js =>
      constructor
      · rintro ⟨hj, hjs⟩
        obtain ⟨k, hk⟩ := (ih js).mp hjs
        exact ⟨(⟨j, Nat.lt_succ_of_le hj⟩, k), by simp [indexList, hk]⟩
      · rintro ⟨k, hk⟩
        have hh := List.cons.inj hk
        exact ⟨hh.1 ▸ Nat.le_of_lt_succ k.1.isLt,
          (ih js).mpr ⟨k.2, hh.2⟩⟩

theorem indexList_injective (ds : List ℕ) : Function.Injective (indexList ds) := by
  induction ds with
  | nil => intro a b hab; cases a; cases b; rfl
  | cons r ds ih =>
    intro a b hab
    have hh := List.cons.inj hab
    exact Prod.ext (Fin.ext hh.1) (ih hh.2)

theorem validIndex_length {ds js : List ℕ} (h : ValidIndex ds js) :
    js.length = ds.length := by
  induction ds generalizing js with
  | nil => cases js <;> simp_all [ValidIndex]
  | cons r ds ih => cases js <;> simp_all [ValidIndex]

theorem grid_row_length {ds js : List ℕ} (h : js ∈ grid ds) : js.length = ds.length :=
  validIndex_length ((mem_grid_iff ds js).mp h)

theorem slots_pos (ds : List ℕ) : 0 < slots ds := by
  induction ds with
  | nil => decide
  | cons r ds ih => exact Nat.mul_pos (Nat.succ_pos r) ih

/-- A self-delimiting runtime list of class sizes. -/
def degreesBits (ds : List ℕ) : List Bool :=
  OracleCost.QueryCodec.natHeader ds.length ++ ds.flatMap OracleCost.QueryCodec.natHeader

/-- The total reader preserves the remaining problem input and random tape. -/
def degreesR (bs : List Bool) : List ℕ × List Bool :=
  Trans.Wire.many Trans.Wire.hdr (Trans.Wire.hdr bs).1 (Trans.Wire.hdr bs).2

theorem degreesR_degreesBits (ds : List ℕ) (rest : List Bool) :
    degreesR (degreesBits ds ++ rest) = (ds, rest) := by
  unfold degreesR degreesBits
  simp only [List.append_assoc, Trans.Wire.hdr_natHeader]
  simpa only [List.map_id] using
    Trans.Wire.many_flatMap Trans.Wire.hdr OracleCost.QueryCodec.natHeader id
      Trans.Wire.hdr_natHeader ds rest

end QecReliability.TensorMachine
