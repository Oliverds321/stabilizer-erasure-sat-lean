import PhysicalBridge.BoundedRatios
import QecReliability.PosetShapeRepair

/-! Executable finite-poset repair by bounded-ratio selection. The list interface
keeps a serializable order and allows the anchored table to be cached once.
Comparison counts charge one unit per index equality/order test and ratio
comparison; they are not bit-operation or machine-runtime bounds. -/

namespace QecReliability.RationalPosetRepair
open RationalOutput

variable {ι : Type*} [PartialOrder ι] [DecidableEq ι] [DecidableLE ι]

def zero : Ratio := ⟨0, 1, by decide, by decide⟩
def one : Ratio := ⟨1, 1, by decide, by decide⟩

@[simp] theorem zero_value : zero.value = 0 := by simp [zero, Ratio.value]
@[simp] theorem one_value : one.value = 1 := by simp [one, Ratio.value]

def anchored (anchors : List ι) (anchorValues estimates : ι → Ratio) (i : ι) : Ratio :=
  if i ∈ anchors then anchorValues i else estimates i

/-- Cached tagged input, in the caller's explicit enumeration order. -/
def inputTable (points anchors : List ι) (anchorValues estimates : ι → Ratio) :
    List (ι × Ratio) := points.map (fun i => (i, anchored anchors anchorValues estimates i))

def anchorTable (anchors : List ι) (anchorValues : ι → Ratio) : List (ι × Ratio) :=
  anchors.map (fun i => (i, anchorValues i))

/-- The counter records index-order tests and ratio comparisons executed by a scan. -/
structure ScanResult where
  ratio : Ratio
  comparisons : ℕ

/-- One comparison to test each index, and one more when selecting its ratio. -/
def lowerScan : List (ι × Ratio) → ι → ScanResult
  | [], _ => ⟨one, 0⟩
  | (i, x) :: xs, j =>
    let tail := lowerScan xs j
    if i ≤ j then ⟨Ratio.lesser x tail.ratio, tail.comparisons + 2⟩
    else ⟨tail.ratio, tail.comparisons + 1⟩

def upperScan : List (ι × Ratio) → ι → ScanResult
  | [], _ => ⟨zero, 0⟩
  | (i, x) :: xs, j =>
    let tail := upperScan xs j
    if j ≤ i then ⟨Ratio.greater x tail.ratio, tail.comparisons + 2⟩
    else ⟨tail.ratio, tail.comparisons + 1⟩

def repairPoint (data anchors : List (ι × Ratio)) (j : ι) : ScanResult :=
  let lo := lowerScan data j
  let hi := upperScan anchors j
  ⟨Ratio.greater hi.ratio lo.ratio, lo.comparisons + hi.comparisons + 1⟩

/-- Cache substituted inputs and anchor data before scanning for each output.
The output has precisely the input enumeration order, including repetitions. -/
def repairTable (points anchors : List ι) (anchorValues estimates : ι → Ratio) :
    List (ι × Ratio) :=
  let data := inputTable points anchors anchorValues estimates
  let anchorData := anchorTable anchors anchorValues
  points.map (fun j => (j, (repairPoint data anchorData j).ratio))

/-- Single-entry interface; use `repairTable` to share preparation across entries. -/
def repair (points anchors : List ι) (anchorValues estimates : ι → Ratio) (j : ι) : Ratio :=
  (repairPoint (inputTable points anchors anchorValues estimates)
    (anchorTable anchors anchorValues) j).ratio

theorem repairTable_eq_map (points anchors : List ι) (anchorValues estimates : ι → Ratio) :
    repairTable points anchors anchorValues estimates =
      points.map (fun j => (j, repair points anchors anchorValues estimates j)) := rfl

@[simp] theorem repairTable_length (points anchors : List ι) (anchorValues estimates : ι → Ratio) :
    (repairTable points anchors anchorValues estimates).length = points.length := by
  simp [repairTable]

theorem repairTable_indices (points anchors : List ι) (anchorValues estimates : ι → Ratio) :
    (repairTable points anchors anchorValues estimates).map Prod.fst = points := by
  simp [repairTable, List.map_map, Function.comp_def]

private theorem lesser_property (P : Ratio → Prop) {x y : Ratio}
    (hx : P x) (hy : P y) : P (Ratio.lesser x y) := by
  unfold Ratio.lesser
  split_ifs <;> assumption

private theorem greater_property (P : Ratio → Prop) {x y : Ratio}
    (hx : P x) (hy : P y) : P (Ratio.greater x y) := by
  unfold Ratio.greater
  split_ifs <;> assumption

/-- Every output ratio is selected from an input or the fixed cap one. -/
theorem lowerScan_property (P : Ratio → Prop) (hone : P one)
    (data : List (ι × Ratio)) (hdata : ∀ ix ∈ data, P ix.2) (j : ι) :
    P (lowerScan data j).ratio := by
  induction data with
  | nil => exact hone
  | cons ix xs ih =>
    rcases ix with ⟨i, x⟩
    have hx := hdata (i, x) (by simp)
    have ht := ih (fun iy hy => hdata iy (by simp [hy]))
    by_cases hij : i ≤ j
    · simpa only [lowerScan, if_pos hij] using lesser_property P hx ht
    · simpa only [lowerScan, if_neg hij] using ht

/-- Every output ratio is selected from an anchor or the fixed floor zero. -/
theorem upperScan_property (P : Ratio → Prop) (hzero : P zero)
    (data : List (ι × Ratio)) (hdata : ∀ ix ∈ data, P ix.2) (j : ι) :
    P (upperScan data j).ratio := by
  induction data with
  | nil => exact hzero
  | cons ix xs ih =>
    rcases ix with ⟨i, x⟩
    have hx := hdata (i, x) (by simp)
    have ht := ih (fun iy hy => hdata iy (by simp [hy]))
    by_cases hji : j ≤ i
    · simpa only [upperScan, if_pos hji] using greater_property P hx ht
    · simpa only [upperScan, if_neg hji] using ht

theorem repair_property (P : Ratio → Prop) (hzero : P zero) (hone : P one)
    (points anchors : List ι) (anchorValues estimates : ι → Ratio)
    (ha : ∀ i ∈ anchors, P (anchorValues i))
    (he : ∀ i ∈ points, P (estimates i)) (j : ι) :
    P (repair points anchors anchorValues estimates j) := by
  apply greater_property P
  · apply upperScan_property P hzero
    intro ix hix
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hix
    exact ha i hi
  · apply lowerScan_property P hone
    intro ix hix
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hix
    dsimp only
    unfold anchored
    split_ifs with hai
    · exact ha i hai
    · exact he i hi

/-- Selection never increases either stored integer beyond the input bounds. -/
theorem repair_components (points anchors : List ι) (anchorValues estimates : ι → Ratio)
    (N D : ℕ) (hN : 1 ≤ N) (hD : 1 ≤ D)
    (ha : ∀ i ∈ anchors, (anchorValues i).num ≤ N ∧ (anchorValues i).den ≤ D)
    (he : ∀ i ∈ points, (estimates i).num ≤ N ∧ (estimates i).den ≤ D) (j : ι) :
    (repair points anchors anchorValues estimates j).num ≤ N ∧
      (repair points anchors anchorValues estimates j).den ≤ D :=
  repair_property (fun x => x.num ≤ N ∧ x.den ≤ D)
    ⟨Nat.zero_le _, hD⟩ ⟨hN, hD⟩ points anchors anchorValues estimates ha he j

/-- In particular there is no denominator growth in the stored coefficient table. -/
theorem repair_payload (points anchors : List ι) (anchorValues estimates : ι → Ratio)
    (B : ℕ) (hB : 2 ≤ B)
    (ha : ∀ i ∈ anchors, (anchorValues i).payload ≤ B)
    (he : ∀ i ∈ points, (estimates i).payload ≤ B) (j : ι) :
    (repair points anchors anchorValues estimates j).payload ≤ B := by
  apply repair_property (fun x => x.payload ≤ B) _ _ points anchors anchorValues estimates ha he j
  · simpa [Ratio.payload, zero] using (show 1 ≤ B by omega)
  · simpa [Ratio.payload, one] using hB

theorem lowerScan_comparisons (data : List (ι × Ratio)) (j : ι) :
    (lowerScan data j).comparisons ≤ 2 * data.length := by
  induction data with
  | nil => simp [lowerScan]
  | cons ix xs ih =>
    rcases ix with ⟨i, x⟩
    simp only [lowerScan, List.length_cons]
    split_ifs <;> dsimp only <;> omega

theorem upperScan_comparisons (data : List (ι × Ratio)) (j : ι) :
    (upperScan data j).comparisons ≤ 2 * data.length := by
  induction data with
  | nil => simp [upperScan]
  | cons ix xs ih =>
    rcases ix with ⟨i, x⟩
    simp only [upperScan, List.length_cons]
    split_ifs <;> dsimp only <;> omega

theorem repairPoint_comparisons (data anchors : List (ι × Ratio)) (j : ι) :
    (repairPoint data anchors j).comparisons ≤ 2 * data.length + 2 * anchors.length + 1 := by
  have hlo := lowerScan_comparisons data j
  have hhi := upperScan_comparisons anchors j
  dsimp only [repairPoint]
  omega

/-- Reserve one equality test per anchor during each cached substitution, then
add the exact scan counters. Ratio arithmetic and index tests are separate from
bit cost; the counter makes no claim of constant-time big-integer arithmetic. -/
def comparisonBudget (points anchors : List ι) (anchorValues estimates : ι → Ratio) : ℕ :=
  points.length * anchors.length +
    (points.map (fun j => (repairPoint (inputTable points anchors anchorValues estimates)
      (anchorTable anchors anchorValues) j).comparisons)).sum

theorem comparisonBudget_le (points anchors : List ι) (anchorValues estimates : ι → Ratio) :
    comparisonBudget points anchors anchorValues estimates ≤
      points.length * anchors.length +
        points.length * (2 * points.length + 2 * anchors.length + 1) := by
  have hsum : ∀ js : List ι,
      (js.map (fun j => (repairPoint (inputTable points anchors anchorValues estimates)
        (anchorTable anchors anchorValues) j).comparisons)).sum ≤
          js.length * (2 * points.length + 2 * anchors.length + 1) := by
    intro js
    induction js with
    | nil => simp
    | cons j js ih =>
      have hj := repairPoint_comparisons (inputTable points anchors anchorValues estimates)
        (anchorTable anchors anchorValues) j
      simp only [inputTable, anchorTable, List.length_map] at hj
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ (2 * points.length + 2 * anchors.length + 1) +
            js.length * (2 * points.length + 2 * anchors.length + 1) := Nat.add_le_add hj ih
        _ = _ := by ring
  exact Nat.add_le_add_left (hsum points) _

/-- A subset-sized anchor list gives a quadratic comparison budget. -/
theorem comparisonBudget_quadratic (points anchors : List ι) (anchorValues estimates : ι → Ratio)
    (ha : anchors.length ≤ points.length) :
    comparisonBudget points anchors anchorValues estimates ≤ 5 * points.length ^ 2 + points.length := by
  have h := comparisonBudget_le points anchors anchorValues estimates
  have hm := Nat.mul_le_mul_left points.length ha
  nlinarith

private theorem lowerScan_lower (data : List (ι × Ratio)) (j : ι) (b : ℝ)
    (hb : b ≤ 1) (hd : ∀ ix ∈ data, ix.1 ≤ j → b ≤ ix.2.value) :
    b ≤ (lowerScan data j).ratio.value := by
  induction data with
  | nil => simpa [lowerScan] using hb
  | cons ix xs ih =>
    rcases ix with ⟨i, x⟩
    have ht := ih (fun iy hy hij => hd iy (by simp [hy]) hij)
    by_cases hij : i ≤ j
    · simpa only [lowerScan, if_pos hij, Ratio.lesser_value] using
        le_min (hd (i,x) (by simp) hij) ht
    · simpa only [lowerScan, if_neg hij] using ht

private theorem lowerScan_le (data : List (ι × Ratio)) (j : ι) {i : ι} {x : Ratio}
    (hx : (i,x) ∈ data) (hij : i ≤ j) : (lowerScan data j).ratio.value ≤ x.value := by
  induction data with
  | nil => simp at hx
  | cons iy xs ih =>
    rcases iy with ⟨k,y⟩
    rcases List.mem_cons.mp hx with h | h
    · cases h
      simp only [lowerScan, if_pos hij, Ratio.lesser_value]
      exact min_le_left _ _
    · have ht := ih h
      by_cases hkj : k ≤ j
      · simpa only [lowerScan, if_pos hkj, Ratio.lesser_value] using
          (min_le_right y.value (lowerScan xs j).ratio.value).trans ht
      · simpa only [lowerScan, if_neg hkj] using ht

private theorem upperScan_upper (data : List (ι × Ratio)) (j : ι) (b : ℝ)
    (hb : 0 ≤ b) (hd : ∀ ix ∈ data, j ≤ ix.1 → ix.2.value ≤ b) :
    (upperScan data j).ratio.value ≤ b := by
  induction data with
  | nil => simpa [upperScan] using hb
  | cons ix xs ih =>
    rcases ix with ⟨i,x⟩
    have ht := ih (fun iy hy hji => hd iy (by simp [hy]) hji)
    by_cases hji : j ≤ i
    · simpa only [upperScan, if_pos hji, Ratio.greater_value] using
        max_le (hd (i,x) (by simp) hji) ht
    · simpa only [upperScan, if_neg hji] using ht

private theorem upperScan_nonneg (data : List (ι × Ratio)) (j : ι) :
    0 ≤ (upperScan data j).ratio.value := (Ratio.value_range _).1

private theorem le_upperScan (data : List (ι × Ratio)) (j : ι) {i : ι} {x : Ratio}
    (hx : (i,x) ∈ data) (hji : j ≤ i) : x.value ≤ (upperScan data j).ratio.value := by
  induction data with
  | nil => simp at hx
  | cons iy xs ih =>
    rcases iy with ⟨k,y⟩
    rcases List.mem_cons.mp hx with h | h
    · cases h
      simp only [upperScan, if_pos hji, Ratio.greater_value]
      exact le_max_left _ _
    · have ht := ih h
      by_cases hjk : j ≤ k
      · simpa only [upperScan, if_pos hjk, Ratio.greater_value] using
          ht.trans (le_max_right y.value (upperScan xs j).ratio.value)
      · simpa only [upperScan, if_neg hjk] using ht

theorem anchored_value (anchors : List ι) (anchorValues estimates : ι → Ratio) (i : ι) :
    (anchored anchors anchorValues estimates i).value =
      PosetShapeRepair.anchoredEstimate anchors.toFinset
        (fun a => (anchorValues a).value) (fun a => (estimates a).value) i := by
  classical
  have hr := (estimates i).value_range
  simp only [anchored, PosetShapeRepair.anchoredEstimate, List.mem_toFinset,
    PosetShapeRepair.clip_eq hr.1 hr.2]
  split_ifs <;> rfl

/-- The executable bounded-ratio algorithm is exactly the checked real repair.
The finite enumeration may be repeated or reordered, but must cover every point. -/
theorem repair_value [Fintype ι] (points anchors : List ι)
    (anchorValues estimates : ι → Ratio) (hpoints : ∀ i, i ∈ points) (j : ι) :
    (repair points anchors anchorValues estimates j).value =
      PosetShapeRepair.repair anchors.toFinset
        (fun a => (anchorValues a).value) (fun a => (estimates a).value) j := by
  classical
  let g := fun i => (anchored anchors anchorValues estimates i).value
  have hg : g = PosetShapeRepair.anchoredEstimate anchors.toFinset
      (fun a => (anchorValues a).value) (fun a => (estimates a).value) :=
    funext (anchored_value anchors anchorValues estimates)
  have hlo : (lowerScan (inputTable points anchors anchorValues estimates) j).ratio.value =
      PosetShapeRepair.prefixMinimum g j := by
    apply le_antisymm
    · apply (PosetShapeRepair.le_prefixMinimum_iff g j _).mpr
      intro i hij
      exact lowerScan_le _ j (List.mem_map.mpr ⟨i, hpoints i, rfl⟩) hij
    · apply lowerScan_lower
      · exact (PosetShapeRepair.prefixMinimum_le g (le_refl j)).trans
          (Ratio.value_range _).2
      · intro ix hix hij
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hix
        exact PosetShapeRepair.prefixMinimum_le g hij
  have hhi : (upperScan (anchorTable anchors anchorValues) j).ratio.value =
      PosetShapeRepair.anchorFloor anchors.toFinset (fun a => (anchorValues a).value) j := by
    apply le_antisymm
    · apply upperScan_upper
      · exact PosetShapeRepair.anchorFloor_nonneg _ _ _
      · intro ix hix hji
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hix
        exact PosetShapeRepair.le_anchorFloor anchors.toFinset
          (fun a => (anchorValues a).value) (List.mem_toFinset.mpr hi) hji
    · apply (PosetShapeRepair.anchorFloor_le_iff _ _ j _).mpr
      refine ⟨upperScan_nonneg _ j, ?_⟩
      intro i hi hji
      exact le_upperScan _ j (List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, rfl⟩) hji
  simp only [repair, repairPoint, Ratio.greater_value, hlo, hhi, hg, PosetShapeRepair.repair]

end QecReliability.RationalPosetRepair
