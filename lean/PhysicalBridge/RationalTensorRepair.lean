import PhysicalBridge.RationalPosetRepair
import PhysicalBridge.MultivariateReliability
import Mathlib.Data.List.FinRange

/-! Executable list-based tensor repair, exact dyadic corner anchors, and rational
parameter evaluation. Enumeration is lexicographic with the head coordinate
outermost. All algorithms below are computable; real-valued functions appear
only in semantic specifications. -/

namespace QecReliability.RationalTensorRepair
open RationalOutput TensorBernstein TensorLatent
open QecPhysical.Stabilizer

instance gridDecidableEq : (ds : List ℕ) → DecidableEq (Grid ds)
  | [] => inferInstanceAs (DecidableEq PUnit)
  | r :: ds =>
    letI := gridDecidableEq ds
    inferInstanceAs (DecidableEq (Fin (r+1) × Grid ds))

instance gridDecidableLE : (ds : List ℕ) → DecidableLE (Grid ds)
  | [] => inferInstanceAs (DecidableLE PUnit)
  | r :: ds =>
    letI := gridDecidableLE ds
    inferInstanceAs (DecidableLE (Fin (r+1) × Grid ds))

/-- Explicit computable enumeration, with head coordinate outermost. -/
def enum : (ds : List ℕ) → List (Grid ds)
  | [] => [PUnit.unit]
  | r :: ds => (List.finRange (r+1)).flatMap (fun i => (enum ds).map (fun j => (i,j)))

theorem mem_enum (ds : List ℕ) (j : Grid ds) : j ∈ enum ds := by
  induction ds with
  | nil => cases j; exact List.mem_cons_self
  | cons r ds ih =>
    exact List.mem_flatMap.mpr ⟨j.1, List.mem_finRange _,
      List.mem_map.mpr ⟨j.2, ih j.2, rfl⟩⟩

theorem enum_length (ds : List ℕ) : (enum ds).length = (ds.map (fun r => r+1)).prod := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    change ((List.finRange (r+1)).flatMap (fun i => (enum ds).map (fun j => (i,j)))).length =
      (r+1) * (ds.map (fun r => r+1)).prod
    rw [List.length_flatMap]
    simp_rw [List.length_map, ih]
    simp

theorem enum_length_card (ds : List ℕ) : (enum ds).length = Fintype.card (Grid ds) := by
  rw [enum_length, MultivariateShapeRepair.grid_card]

/-- Corner recognition does not enumerate all Boolean corners, so zero-degree
coordinates do not create an exponential list of duplicate anchors. -/
def cornerTest : (ds : List ℕ) → Grid ds → Bool
  | [], _ => true
  | r :: ds, j => ((j.1.val == 0) || (j.1.val == r)) && cornerTest ds j.2

theorem cornerTest_iff (ds : List ℕ) (j : Grid ds) :
    cornerTest ds j = true ↔ ∃ b : Corner ds, cornerIndex ds b = j := by
  induction ds with
  | nil =>
    cases j
    constructor
    · intro _; exact ⟨PUnit.unit, rfl⟩
    · intro _; rfl
  | cons r ds ih =>
    constructor
    · intro h
      have hh : (j.1.val = 0 ∨ j.1.val = r) ∧ cornerTest ds j.2 = true := by
        simpa [cornerTest] using h
      obtain ⟨bs, hbs⟩ := (ih j.2).mp hh.2
      rcases hh.1 with hzero | hlast
      · refine ⟨(false,bs), ?_⟩
        exact Prod.ext (Fin.ext hzero.symm) hbs
      · refine ⟨(true,bs), ?_⟩
        exact Prod.ext (Fin.ext hlast.symm) hbs
    · rintro ⟨⟨b,bs⟩, rfl⟩
      have ht := (ih (cornerIndex ds bs)).mpr ⟨bs,rfl⟩
      cases b <;> simp [cornerTest, cornerIndex, ht]

def anchors (ds : List ℕ) : List (Grid ds) := (enum ds).filter (cornerTest ds)

theorem anchors_length_le (ds : List ℕ) : (anchors ds).length ≤ (enum ds).length :=
  List.length_filter_le _ _

theorem anchors_toFinset (ds : List ℕ) :
    (anchors ds).toFinset = MultivariateShapeRepair.cornerAnchors ds := by
  classical
  ext j
  simp [anchors, mem_enum, cornerTest_iff, MultivariateShapeRepair.cornerAnchors]

/-- Computable counterpart of the semantic canonical-cause representative. -/
def canonicalCausesExec : (ds : List ℕ) → Grid ds → CausesGrid ds
  | [], _ => PUnit.unit
  | r :: ds, j =>
    (Finset.univ.filter (fun i : Fin r => i.val < j.1.val), canonicalCausesExec ds j.2)

theorem canonicalCausesExec_eq (ds : List ℕ) (j : Grid ds) :
    canonicalCausesExec ds j = canonicalCauses ds j := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    exact congrArg (fun x => (Finset.univ.filter (fun i : Fin r => i.val < j.1.val), x)) (ih j.2)

/-- Exact bounded dyadic anchor data from the input Pauli rows and observation map. -/
def dyadicAnchor {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) : Ratio :=
  Ratio.dyadic rows (C (canonicalCausesExec ds j))

theorem dyadicAnchor_value {n : ℕ} (ds : List ℕ)
    (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) :
    (dyadicAnchor ds rows C j).value = physicalCornerAnchorValues (SharedCircuit.rowSpace rows) C j := by
  rw [dyadicAnchor, Ratio.dyadic_value, canonicalCausesExec_eq]
  rfl

def coefficient {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → Ratio) (j : Grid ds) : Ratio :=
  RationalPosetRepair.repair (enum ds) (anchors ds) (dyadicAnchor ds rows C) estimates j

/-- Flat bounded-ratio output, with cached inputs shared by all coordinate scans. -/
def prepare {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → Ratio) : List Ratio :=
  (RationalPosetRepair.repairTable (enum ds) (anchors ds)
    (dyadicAnchor ds rows C) estimates).map Prod.snd

theorem prepare_eq_map {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → Ratio) :
    prepare ds rows C estimates = (enum ds).map (coefficient ds rows C estimates) := by
  simp [prepare, RationalPosetRepair.repairTable_eq_map, List.map_map, coefficient]

theorem prepare_length {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → Ratio) :
    (prepare ds rows C estimates).length = (ds.map (fun r => r+1)).prod := by
  rw [prepare_eq_map, List.length_map, enum_length]

/-- Explicit flat-list lookup, with zero for a short or absent input. -/
def lookup {ι : Type*} [DecidableEq ι] : List ι → List Ratio → ι → Ratio
  | i :: is, x :: xs, j => if i = j then x else lookup is xs j
  | _, _, _ => RationalPosetRepair.zero

theorem lookup_map {ι : Type*} [DecidableEq ι] (is : List ι) (f : ι → Ratio)
    {j : ι} (hj : j ∈ is) : lookup is (is.map f) j = f j := by
  induction is with
  | nil => simp at hj
  | cons i is ih =>
    by_cases hij : i = j
    · subst j
      simp [lookup]
    · have ht : j ∈ is := (List.mem_cons.mp hj).resolve_left (Ne.symm hij)
      simpa [lookup, hij] using ih ht

/-- A serialized estimate-table interface for machine transcription. -/
def prepareFlat {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : List Ratio) : List Ratio :=
  prepare ds rows C (lookup (enum ds) estimates)

theorem prepareFlat_map {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → Ratio) :
    prepareFlat ds rows C ((enum ds).map estimates) = prepare ds rows C estimates := by
  have h : lookup (enum ds) ((enum ds).map estimates) = estimates :=
    funext (fun j => lookup_map (enum ds) estimates (mem_enum ds j))
  simp only [prepareFlat, h]

theorem coefficient_value {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → Ratio) (j : Grid ds) :
    (coefficient ds rows C estimates j).value =
      PosetShapeRepair.repair (MultivariateShapeRepair.cornerAnchors ds)
        (physicalCornerAnchorValues (SharedCircuit.rowSpace rows) C)
        (fun i => (estimates i).value) j := by
  rw [coefficient, RationalPosetRepair.repair_value _ _ _ _ (mem_enum ds), anchors_toFinset]
  simp only [dyadicAnchor_value]

theorem prepare_payload {n : ℕ} (ds : List ℕ) (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → Ratio) (B : ℕ) (hB : 2 ≤ B)
    (ha : ∀ i ∈ anchors ds, (dyadicAnchor ds rows C i).payload ≤ B)
    (he : ∀ i, (estimates i).payload ≤ B) :
    ∀ x ∈ prepare ds rows C estimates, x.payload ≤ B := by
  rw [prepare_eq_map]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact RationalPosetRepair.repair_payload _ _ _ _ B hB ha (fun i _ => he i) j

theorem comparisonBudget_quadratic {n : ℕ} (ds : List ℕ)
    (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → Ratio) :
    RationalPosetRepair.comparisonBudget (enum ds) (anchors ds) (dyadicAnchor ds rows C) estimates ≤
      5 * ((ds.map (fun r => r+1)).prod) ^ 2 + (ds.map (fun r => r+1)).prod := by
  simpa only [enum_length] using RationalPosetRepair.comparisonBudget_quadratic
    (enum ds) (anchors ds) (dyadicAnchor ds rows C) estimates (anchors_length_le ds)

/-- Exact bounded-ratio evaluation of one rational Bernstein row. -/
def evaluateRow {r : ℕ} (f : Fin (r+1) → Ratio) (p : Ratio) : Ratio :=
  let v := evaluateRationalCurve (fun j => (f j).num) (fun j => (f j).den) p.num p.den
  ⟨v.1, v.2,
    evaluateRationalCurve_den_pos _ _ (fun j => (f j).den_pos) p.den_pos,
    evaluateRationalCurve_num_le_den _ _ (fun j => (f j).den_pos)
      (fun j => (f j).num_le_den) p.num_le_den p.den_pos⟩

theorem evaluateRow_value {r : ℕ} (f : Fin (r+1) → Ratio) (p : Ratio) :
    (evaluateRow f p).value = bernsteinCurve r (fun j => (f j).value) p.value :=
  evaluateRationalCurve_semantics _ _ (fun j => (f j).den_pos) p.num_le_den p.den_pos

def RationalParams : List ℕ → Type
  | [] => PUnit
  | _ :: ds => Ratio × RationalParams ds

noncomputable def realParams : (ds : List ℕ) → RationalParams ds → Params ds
  | [], _ => PUnit.unit
  | _ :: ds, p => (p.1.value, realParams ds p.2)

def evaluate : (ds : List ℕ) → (Grid ds → Ratio) → RationalParams ds → Ratio
  | [], f, _ => f PUnit.unit
  | r :: ds, f, p => evaluateRow (fun j => evaluate ds (fun k => f (j,k)) p.2) p.1

theorem evaluate_value (ds : List ℕ) (f : Grid ds → Ratio) (p : RationalParams ds) :
    (evaluate ds f p).value = curve ds (fun j => (f j).value) (realParams ds p) := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    change (evaluateRow (fun j => evaluate ds (fun k => f (j,k)) p.2) p.1).value =
      bernsteinCurve r (fun j => curve ds (fun k => (f (j,k)).value) (realParams ds p.2)) p.1.value
    rw [evaluateRow_value]
    congr 1
    funext j
    exact ih (fun k => f (j,k)) p.2

/-- The rationally evaluated repaired table agrees exactly with the established
real physical-corner repaired curve. -/
theorem evaluate_coefficient_value {n : ℕ} (ds : List ℕ)
    (rows : List (List (SharedCircuit.PauliCoord n)))
    (C : CausesGrid ds → Finset (Fin n)) (estimates : Grid ds → Ratio) (p : RationalParams ds) :
    (evaluate ds (coefficient ds rows C estimates) p).value =
      physicalCornerRepairedCurve (SharedCircuit.rowSpace rows) C
        (fun j => (estimates j).value) (realParams ds p) := by
  rw [evaluate_value]
  simp only [coefficient_value, physicalCornerRepairedCurve, MultivariateShapeRepair.repairedCurve]

end QecReliability.RationalTensorRepair
