import TensorMachineGridBounds
import Trans.BoundsQH.Compile
import Trans.BoundsQH.HTrans

/-! Polynomial intermediate-space bounds for actual tensor grid execution.
The explicit table cardinality Q is retained in the polynomial argument. -/

namespace QecReliability.TensorMachine.GridFL

open FL FL.Lib FL.Tm Trans.Wire Trans.Query.Bound Trans.BoundsQH

private theorem row_mag_cons (j : ℕ) (xs : List ℕ) :
    mag Row (j :: xs) = j + 1 + mag Row xs := rfl

private theorem table_mag_cons (row : List ℕ) (xs : List (List ℕ)) :
    mag Table (row :: xs) = mag Row row + 1 + mag Table xs := rfl

private theorem seed_mag : mag Table [[]] = 3 := rfl

private theorem seed_size : (Table.enc [[]]).size = 3 := rfl

theorem prefixMap_mag (j : ℕ) (xs : List (List ℕ)) :
    mag Table (xs.map (j :: ·)) = mag Table xs + xs.length * (j + 1) := by
  induction xs with
  | nil => simp [Table]
  | cons row xs ih =>
    change (j + 1 + mag Row row) + 1 + mag Table (xs.map (j :: ·)) =
      (mag Row row + 1 + mag Table xs) + (xs.length + 1) * (j + 1)
    rw [ih]
    ring

@[polyB] theorem prefixStep_P (i : Indices) : PolyB (prefixStepF i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, prefixStepBody])

@[polyB] theorem prefixFold_P (i : Indices) : PolyB (foldrF (prefixStepF i) i.prefixFold) := by
  apply foldr_polyB_res _ _ (prefixStep_P i) (kR := 1) (cR := 10)
  intro xs z
  rcases z with ⟨j, acc⟩
  rw [prefixFold_den]
  have ha := mag_append_le Row (xs.map (j :: ·)) acc
  rw [prefixMap_mag] at ha
  have hl := mag_list_len Row xs
  simp only [mag_prod, mag_nat]
  rw [G, Function.iterate_one]
  unfold B0
  nlinarith

@[polyB] theorem prefix_P (i : Indices) : PolyB (prefixF i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, prefixBody, polyB])

@[polyB] theorem expandStep_P (i : Indices) : PolyB (expandStepF i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, expandStepBody, polyB])

@[polyB] theorem expandFold_P (i : Indices) : PolyB (foldrF (expandStepF i) i.expandFold) := by
  apply foldr_polyB_res _ _ (expandStep_P i) (kR := 2) (cR := 10)
  intro hs z
  rcases z with ⟨xs, acc⟩
  rw [expandFold_den]
  let m := mag (.prod (.list .nat) (.prod Table Table)) (hs,xs,acc)
  have hlen : hs.length ≤ m := by
    have h := mag_list_len .nat hs
    simp only [m, mag_prod] at *
    omega
  have hslice : ∀ j ∈ hs, mag Table (xs.map (j :: ·)) ≤ G 1 10 m := by
    intro j hj
    rw [prefixMap_mag]
    have hj' := mag_mem .nat hj
    have hx := mag_list_len Row xs
    change xs.length + 1 ≤ mag Table xs at hx
    simp only [mag_nat] at hj'
    have hxM : mag Table xs ≤ m := by simp only [m, mag_prod]; omega
    have hjM : j + 1 ≤ m := by
      change j + 1 ≤ mag (.list .nat) hs + (mag Table xs + mag Table acc + 1) + 1
      calc
        j + 1 ≤ j + 2 := Nat.le_succ _
        _ ≤ mag (.list .nat) hs := hj'
        _ ≤ mag (.list .nat) hs + (mag Table xs + mag Table acc + 1) := Nat.le_add_right _ _
        _ ≤ mag (.list .nat) hs + (mag Table xs + mag Table acc + 1) + 1 := Nat.le_succ _
    have hmul := Nat.mul_le_mul (show xs.length ≤ m by omega) hjM
    rw [G, Function.iterate_one]
    unfold B0
    nlinarith
  have hf := mag_flatMap_le (a := .nat) (b := Row) hs
    (fun j => xs.map (j :: ·)) (G 1 10 m) hslice
  have ha := mag_append_le Row (hs.flatMap (fun j => xs.map (j :: ·))) acc
  have hg := le_G 1 10 m
  have hprod := Nat.mul_le_mul_right (G 1 10 m) (hlen.trans (by omega : m ≤ G 1 10 m))
  have hsq := G_sq 1 10 m
  change mag Table xs + mag Table (hs.flatMap (fun j => xs.map (j :: ·)) ++ acc) + 1 ≤ G 2 10 m
  have hm : mag Table xs + mag Table acc ≤ m := by simp [m, mag_prod]; omega
  nlinarith

@[polyB] theorem expand_P (L : Lib) (i : Indices) : PolyB (expandF L i) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, expandBody, polyB])

theorem grid_magnitude (ds : List ℕ) :
    mag Table (grid ds) ≤ slots ds * (ds.length * (ds.sum + 1) + 2) + 1 := by
  have hrow : ∀ js ∈ grid ds, mag Row js ≤ ds.length * (ds.sum + 1) + 1 := by
    intro js hjs
    have hv := (mem_grid_iff ds js).mp hjs
    have h := mag_list_le .nat js ds.sum (fun j hj => validIndex_entry_le_sum hv j hj)
    simpa only [validIndex_length hv] using h
  have h := mag_list_le Row (grid ds) (ds.length * (ds.sum + 1) + 1) hrow
  simpa only [grid_length, Nat.add_assoc] using h

def tableMagnitudeBound (M T Q : ℕ) : ℕ := Q * (T * (M + 1) + 2) + 1

theorem grid_magnitude_bound (ds : List ℕ) (M T Q : ℕ)
    (hm : ds.sum ≤ M) (ht : ds.length ≤ T) (hq : slots ds ≤ Q) :
    mag Table (grid ds) ≤ tableMagnitudeBound M T Q := by
  apply (grid_magnitude ds).trans
  unfold tableMagnitudeBound
  exact Nat.add_le_add_right (Nat.mul_le_mul hq
    (Nat.add_le_add_right (Nat.mul_le_mul ht (Nat.add_le_add_right hm 1)) 2)) 1

theorem natList_mag (ds : List ℕ) : mag (.list .nat) ds = ds.sum + ds.length + 1 := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    change r + 1 + mag (.list .nat) ds = (r + ds.sum) + (ds.length + 1) + 1
    rw [ih]
    omega

theorem gridFold_msize_bound (L : Lib) (i : Indices) {k c : ℕ}
    (hF : Trans.Query.Bound.FnB (G k c) (expandF L i))
    (ds : List ℕ) (M T Q : ℕ) (hm : ds.sum ≤ M) (ht : ds.length ≤ T) (hq : slots ds ≤ Q) :
    foldrMsize (expandF L i) ds [[]] ≤
      G k c (M + tableMagnitudeBound M T Q + 1) +
        10 * M + 5 * T + 5 * tableMagnitudeBound M T Q + 50 := by
  induction ds with
  | nil => simp
  | cons r ds ih =>
    have hm' : ds.sum ≤ M := by simp only [List.sum_cons] at hm; omega
    have hr : r ≤ M := by simp only [List.sum_cons] at hm; omega
    have ht' : ds.length ≤ T := by simp only [List.length_cons] at ht; omega
    have hq' : slots ds ≤ Q :=
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos r)).trans hq
    have htail := ih hm' ht' hq'
    have hgrid := grid_magnitude_bound ds M T Q hm' ht' hq'
    have hf := (hF (r, grid ds)).2.2.1
    have hg := G_mono (k := k) (c := c) le_rfl le_rfl
      (show mag (.prod .nat Table) (r,grid ds) ≤ M + tableMagnitudeBound M T Q + 1 by
        simp only [mag_prod, mag_nat]; omega)
    have hs1 := size_le_mag (.prod (.list .nat) Table) (ds,[[]])
    have hs2 := size_le_mag (.prod .nat Table) (r,grid ds)
    change ((Ty.prod (.list .nat) Table).enc (ds,[[]])).size ≤
      5 * (mag (.list .nat) ds + 3 + 1) + 1 at hs1
    simp only [mag_prod, mag_nat, natList_mag] at hs1 hs2 hf hg
    rw [foldrMsize, gridFold_den]
    omega

/-- Uniform polynomial intermediate space, with Q explicitly present. -/
theorem grid_msize_bound (L : Lib) (i : Indices) : ∃ k c, ∀ ds : List ℕ,
    (gridF L i).msize ds ≤
      G k c (ds.sum + tableMagnitudeBound ds.sum ds.length (slots ds) + 1) +
        10 * ds.sum + 5 * ds.length +
        5 * tableMagnitudeBound ds.sum ds.length (slots ds) + 100 := by
  obtain ⟨k,c,hF⟩ := expand_P L i
  refine ⟨k,c,?_⟩
  intro ds
  have h := gridFold_msize_bound L i hF ds ds.sum ds.length (slots ds) le_rfl le_rfl le_rfl
  have hs := size_le_mag (.prod (.list .nat) Table) (ds,[[]])
  change ((Ty.prod (.list .nat) Table).enc (ds,[[]])).size ≤
    5 * (mag (.list .nat) ds + 3 + 1) + 1 at hs
  simp only [natList_mag] at hs
  have hseed : (Row.list.enc ([[]] : List (List ℕ))).size = 3 := rfl
  simp only [gridF, Trans.Control.bodySig, gridBody, tm_simp, foldrF_msize]
  rw [hseed]
  omega

end QecReliability.TensorMachine.GridFL
