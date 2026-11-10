import TensorMachineGrid
import PhysicalBridge.RationalTensorRepair
import FL.Lib.LinearRepair

/-! Serializable semantics of tensor repair. Keys are natural-number lists and
ratios are numerator/denominator pairs. The following functions are transcribed
by TensorRepairFL; they do not use real comparisons or classical enumeration. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL.Lib.LinearRepairFL RationalOutput TensorBernstein

abbrev Key := List ℕ
abbrev RawRatio := ℕ × ℕ
abbrev RawEntry := Key × RawRatio
abbrev RawTable := List RawEntry

def keyLe : Key → Key → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide (x ≤ y) && keyLe xs ys
  | _, _ => false

def keyEq (xs ys : Key) : Bool := keyLe xs ys && keyLe ys xs

def keyStepR (s : Key × Bool) (x : ℕ) : Key × Bool :=
  match s.1 with
  | [] => ([],false)
  | y :: ys => (ys,s.2 && decide (x ≤ y))

def keyFinish (s : Key × Bool) : Bool :=
  match s.1 with
  | [] => s.2
  | _ :: _ => false

theorem keyFold_finish (xs ys : Key) (b : Bool) :
    keyFinish (xs.foldl keyStepR (ys,b)) = (b && keyLe xs ys) := by
  induction xs generalizing ys b with
  | nil => cases ys <;> simp [keyFinish, keyLe]
  | cons x xs ih =>
    cases ys with
    | nil => simpa [List.foldl_cons, keyStepR, keyLe] using ih [] false
    | cons y ys =>
      simpa only [List.foldl_cons, keyStepR, keyLe, Bool.and_assoc] using
        ih ys (b && decide (x ≤ y))

theorem keyLe_index (ds : List ℕ) (i j : Grid ds) :
    keyLe (indexList ds i) (indexList ds j) = decide (i ≤ j) := by
  induction ds with
  | nil => cases i; cases j; rfl
  | cons r ds ih =>
    rcases i with ⟨a,is⟩
    rcases j with ⟨b,js⟩
    change (decide (a ≤ b) && keyLe (indexList ds is) (indexList ds js)) =
      decide (a ≤ b ∧ is ≤ js)
    rw [ih]
    by_cases hab : a ≤ b <;> by_cases hij : is ≤ js <;> simp [hab, hij]

theorem keyEq_index (ds : List ℕ) (i j : Grid ds) :
    keyEq (indexList ds i) (indexList ds j) = decide (i = j) := by
  by_cases hij : i ≤ j <;> by_cases hji : j ≤ i
  · have he := le_antisymm hij hji
    simp [keyEq, keyLe_index, hij, hji, he]
  · have he : i ≠ j := by intro h; subst j; exact hji le_rfl
    simp [keyEq, keyLe_index, hij, hji, he]
  · have he : i ≠ j := by intro h; subst j; exact hij le_rfl
    simp [keyEq, keyLe_index, hij, hji, he]
  · have he : i ≠ j := by intro h; subst j; exact hij le_rfl
    simp [keyEq, keyLe_index, hij, hji, he]

def lowerR : RawTable → Key → RawRatio
  | [], _ => (1,1)
  | (i,x) :: xs, j => if keyLe i j then lesserR x (lowerR xs j) else lowerR xs j

def upperR : RawTable → Key → RawRatio
  | [], _ => (0,1)
  | (i,x) :: xs, j => if keyLe j i then greaterR x (upperR xs j) else upperR xs j

def anchorR : RawTable → Key → RawRatio → RawRatio
  | [], _, fallback => fallback
  | (i,x) :: xs, j, fallback =>
    if keyEq i j then x else anchorR xs j fallback

def substituteR (data anchors : RawTable) : RawTable :=
  data.map (fun ix => (ix.1, anchorR anchors ix.1 ix.2))

def pointR (data anchors : RawTable) (j : Key) : RawRatio :=
  greaterR (upperR anchors j) (lowerR data j)

def repairR (data anchors : RawTable) : List RawRatio :=
  let cached := substituteR data anchors
  data.map (fun ix => pointR cached anchors ix.1)

def encodeEntries (ds : List ℕ) (xs : List (Grid ds × Ratio)) : RawTable :=
  xs.map (fun ix => (indexList ds ix.1, toR ix.2))

theorem lowerR_encode (ds : List ℕ) (xs : List (Grid ds × Ratio)) (j : Grid ds) :
    lowerR (encodeEntries ds xs) (indexList ds j) =
      toR (RationalPosetRepair.lowerScan xs j).ratio := by
  induction xs with
  | nil => rfl
  | cons ix xs ih =>
    rcases ix with ⟨i,x⟩
    simp only [encodeEntries] at ih
    simp only [encodeEntries, List.map_cons, lowerR, keyLe_index,
      RationalPosetRepair.lowerScan]
    by_cases hij : i ≤ j
    · simp [hij, ih, toR_lesser]
    · simp [hij, ih]

theorem upperR_encode (ds : List ℕ) (xs : List (Grid ds × Ratio)) (j : Grid ds) :
    upperR (encodeEntries ds xs) (indexList ds j) =
      toR (RationalPosetRepair.upperScan xs j).ratio := by
  induction xs with
  | nil => rfl
  | cons ix xs ih =>
    rcases ix with ⟨i,x⟩
    simp only [encodeEntries] at ih
    simp only [encodeEntries, List.map_cons, upperR, keyLe_index,
      RationalPosetRepair.upperScan]
    by_cases hji : j ≤ i
    · simp [hji, ih, toR_greater]
    · simp [hji, ih]

theorem anchorR_encode (ds : List ℕ) (anchors : List (Grid ds))
    (values : Grid ds → Ratio) (j : Grid ds) (fallback : Ratio) :
    anchorR (encodeEntries ds (RationalPosetRepair.anchorTable anchors values))
      (indexList ds j) (toR fallback) =
        toR (if j ∈ anchors then values j else fallback) := by
  induction anchors with
  | nil => rfl
  | cons a anchors ih =>
    simp only [encodeEntries, RationalPosetRepair.anchorTable, List.map_map] at ih
    simp only [RationalPosetRepair.anchorTable, List.map_cons, encodeEntries,
      anchorR, keyEq_index]
    by_cases haj : a = j
    · subst j
      simp
    · have hja : j ≠ a := Ne.symm haj
      simp [haj, hja, ih]

theorem substituteR_encode (ds : List ℕ) (points anchors : List (Grid ds))
    (anchorValues estimates : Grid ds → Ratio) :
    substituteR (encodeEntries ds (points.map (fun j => (j, estimates j))))
      (encodeEntries ds (RationalPosetRepair.anchorTable anchors anchorValues)) =
    encodeEntries ds (RationalPosetRepair.inputTable points anchors anchorValues estimates) := by
  simp only [substituteR, encodeEntries, RationalPosetRepair.inputTable, List.map_map]
  apply List.map_congr_left
  intro j hj
  change (indexList ds j,
    anchorR (encodeEntries ds (RationalPosetRepair.anchorTable anchors anchorValues))
      (indexList ds j) (toR (estimates j))) = _
  rw [anchorR_encode]
  rfl

/-- The raw list algorithm implements the executable bounded-ratio repair table. -/
theorem repairR_encode (ds : List ℕ) (points anchors : List (Grid ds))
    (anchorValues estimates : Grid ds → Ratio) :
    repairR (encodeEntries ds (points.map (fun j => (j, estimates j))))
      (encodeEntries ds (RationalPosetRepair.anchorTable anchors anchorValues)) =
      (RationalPosetRepair.repairTable points anchors anchorValues estimates).map
        (fun ix => toR ix.2) := by
  rw [repairR, substituteR_encode, RationalPosetRepair.repairTable_eq_map]
  simp only [encodeEntries, List.map_map]
  apply List.map_congr_left
  intro j hj
  change pointR (encodeEntries ds (RationalPosetRepair.inputTable points anchors anchorValues estimates))
    (encodeEntries ds (RationalPosetRepair.anchorTable anchors anchorValues)) (indexList ds j) = _
  rw [pointR, lowerR_encode, upperR_encode]
  exact (toR_greater _ _).symm

end QecReliability.TensorMachine.RepairFL
