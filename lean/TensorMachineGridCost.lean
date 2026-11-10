import TensorMachineGridBounds

/-! Closed time bounds for the compiled grid enumerator. The actual FL cost
is bounded polynomially in structural degree size and explicit table size Q. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.GridFL

open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control (bodySig)

theorem prefixStep_cost (i : Indices) (row : List ℕ) (j : ℕ) (acc : List (List ℕ)) :
    (prefixStepF i).cost (row,j,acc) = 16 := by
  rfl

theorem prefixFold_cost (i : Indices) (xs : List (List ℕ)) (j : ℕ)
    (acc : List (List ℕ)) : foldrCost (prefixStepF i) xs (j,acc) = 28 * xs.length + 10 := by
  induction xs with
  | nil => rfl
  | cons row xs ih =>
    rw [foldrCost, prefixFold_den, prefixStep_cost, ih]
    simp only [List.length_cons]
    omega

theorem prefix_cost (i : Indices) (j : ℕ) (xs : List (List ℕ)) :
    (prefixF i).cost (j,xs) = 28 * xs.length + 20 := by
  simp only [prefixF, bodySig, prefixBody, tm_simp, foldrF_cost]
  rw [prefixFold_cost]
  omega

theorem expandStep_cost (i : Indices) (j : ℕ) (xs acc : List (List ℕ)) :
    (expandStepF i).cost (j,xs,acc) = 43 * xs.length + 53 := by
  simp only [expandStepF, bodySig, expandStepBody, tm_simp, appendF_cost]
  rw [prefix_cost, prefixF_den]
  simp only [List.length_map]
  omega

theorem expandFold_cost (i : Indices) (hs : List ℕ) (xs acc : List (List ℕ)) :
    foldrCost (expandStepF i) hs (xs,acc) = hs.length * (43 * xs.length + 65) + 10 := by
  induction hs with
  | nil => simp only [foldrCost, List.length_nil, Nat.zero_mul, Nat.zero_add]
  | cons j hs ih =>
    rw [foldrCost, expandFold_den, expandStep_cost, ih]
    simp only [List.length_cons, Nat.add_mul]
    omega

theorem expand_cost (L : Lib) (i : Indices) (r : ℕ) (xs : List (List ℕ)) :
    (expandF L i).cost (r,xs) =
      25 * r.size + 60 * (r + 2) * ((r + 1).size + 1) +
        (r + 1) * (43 * xs.length + 65) + 55 := by
  simp only [expandF, bodySig, expandBody, tm_simp, foldrF_cost,
    rangeF_cost, rangeF_den, succF_cost, succF_den]
  rw [expandFold_cost]
  simp only [List.length_range]
  ring

theorem expand_cost_bound (L : Lib) (i : Indices) (r : ℕ) (xs : List (List ℕ))
    (M Q : ℕ) (hr : r ≤ M) (hxs : xs.length ≤ Q) :
    (expandF L i).cost (r,xs) ≤ 1000 * (M + Q + 2)^2 := by
  rw [expand_cost]
  have hs := NatSize.size_le_self r
  have hs' := NatSize.size_le_self (r + 1)
  have hmul : 60 * (r + 2) * ((r + 1).size + 1) ≤ 60 * (M + 2) * (M + 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 60 (by omega)) (by omega)
  have hxmul : (r + 1) * (43 * xs.length + 65) ≤ (M + 1) * (43 * Q + 65) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem gridFold_cost_bound (L : Lib) (i : Indices) (ds : List ℕ) (M Q : ℕ)
    (hd : ds.sum ≤ M) (hq : slots ds ≤ Q) :
    foldrCost (expandF L i) ds [[]] ≤ ds.length * (1000 * (M + Q + 2)^2 + 12) + 10 := by
  induction ds with
  | nil => simp
  | cons r ds ih =>
    have hsum : ds.sum ≤ M := by simp only [List.sum_cons] at hd; omega
    have hr : r ≤ M := by simp only [List.sum_cons] at hd; omega
    have hs : slots ds ≤ slots (r :: ds) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos r)
    have htail := ih hsum (hs.trans hq)
    have hx := expand_cost_bound L i r (grid ds) M Q hr (by rw [grid_length]; exact hs.trans hq)
    rw [foldrCost, gridFold_den]
    simp only [List.length_cons, Nat.add_mul]
    omega

/-- A concrete polynomial bound on the cost of the actual compiled enumerator. -/
theorem grid_cost_bound (L : Lib) (i : Indices) (ds : List ℕ) :
    (gridF L i).cost ds ≤
      ds.length * (1000 * (ds.sum + slots ds + 2)^2 + 12) + 17 := by
  have h := gridFold_cost_bound L i ds ds.sum (slots ds) le_rfl le_rfl
  simp only [gridF, bodySig, gridBody, tm_simp, foldrF_cost]
  nlinarith

theorem prefixStep_depth (i : Indices) (row : List ℕ) (j : ℕ) (acc : List (List ℕ)) :
    (prefixStepF i).depth (row,j,acc) = 1 := rfl

theorem prefixFold_depth (i : Indices) (xs : List (List ℕ)) (j : ℕ)
    (acc : List (List ℕ)) : foldrDepth (prefixStepF i) xs (j,acc) = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons row xs ih =>
    rw [foldrDepth, prefixFold_den, prefixStep_depth, ih]
    simp only [List.length_cons]
    omega

theorem prefix_depth (i : Indices) (j : ℕ) (xs : List (List ℕ)) :
    (prefixF i).depth (j,xs) = xs.length + 2 := by
  simp only [prefixF, bodySig, prefixBody, tm_simp, foldrF_depth]
  rw [prefixFold_depth]
  omega

theorem expandStep_depth (i : Indices) (j : ℕ) (xs acc : List (List ℕ)) :
    (expandStepF i).depth (j,xs,acc) = xs.length + 3 := by
  simp only [expandStepF, bodySig, expandStepBody, tm_simp, appendF_depth]
  rw [prefix_depth, prefixF_den]
  simp only [List.length_map]
  omega

theorem expandFold_depth (i : Indices) (hs : List ℕ) (xs acc : List (List ℕ)) :
    foldrDepth (expandStepF i) hs (xs,acc) ≤ hs.length + xs.length + 4 := by
  induction hs with
  | nil => simp
  | cons j hs ih =>
    rw [foldrDepth, expandFold_den, expandStep_depth]
    simp only [List.length_cons]
    omega

theorem expand_depth_bound (L : Lib) (i : Indices) (r : ℕ) (xs : List (List ℕ)) :
    (expandF L i).depth (r,xs) ≤ 2 * r + xs.length + 10 := by
  have hf := expandFold_depth i (List.range (r + 1)) xs []
  have hn := NatSize.size_le_self r
  have hn' := NatSize.size_le_self (r + 1)
  simp only [List.length_range] at hf
  simp only [expandF, bodySig, expandBody, tm_simp, foldrF_depth,
    rangeF_depth, rangeF_den, succF_depth, succF_den]
  omega

theorem gridFold_depth_bound (L : Lib) (i : Indices) (ds : List ℕ) (M Q : ℕ)
    (hd : ds.sum ≤ M) (hq : slots ds ≤ Q) :
    foldrDepth (expandF L i) ds [[]] ≤ ds.length + 2 * M + Q + 11 := by
  induction ds with
  | nil => simp
  | cons r ds ih =>
    have hsum : ds.sum ≤ M := by simp only [List.sum_cons] at hd; omega
    have hr : r ≤ M := by simp only [List.sum_cons] at hd; omega
    have hs : slots ds ≤ slots (r :: ds) := Nat.le_mul_of_pos_left _ (Nat.succ_pos r)
    have htail := ih hsum (hs.trans hq)
    have hx := expand_depth_bound L i r (grid ds)
    rw [grid_length] at hx
    rw [foldrDepth, gridFold_den]
    simp only [List.length_cons]
    omega

theorem grid_depth_bound (L : Lib) (i : Indices) (ds : List ℕ) :
    (gridF L i).depth ds ≤ ds.length + 2 * ds.sum + slots ds + 12 := by
  have h := gridFold_depth_bound L i ds ds.sum (slots ds) le_rfl le_rfl
  simp only [gridF, bodySig, gridBody, tm_simp, foldrF_depth]
  omega

end QecReliability.TensorMachine.GridFL
