import QecReliability.PosetShapeRepair
import QecReliability.TensorBernstein

/-! New multivariate anchored shape repair. The finite coefficient construction
preserves both relative tails on the entire parameter cube. This is a mathematical
postprocessing theorem, not an installed-machine or comparison-count bound. -/

noncomputable section
namespace QecReliability.MultivariateShapeRepair

open scoped Classical
open TensorBernstein

theorem grid_card (ds : List ℕ) :
    Fintype.card (Grid ds) = (ds.map (fun r => r + 1)).prod := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    change Fintype.card (Fin (r + 1) × Grid ds) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih]
    rfl

/-- A fixed number of probability classes gives a polynomial-sized table. -/
theorem grid_card_le (ds : List ℕ) :
    Fintype.card (Grid ds) ≤ (ds.sum + 1) ^ ds.length := by
  rw [grid_card]
  induction ds with
  | nil => simp
  | cons r ds ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons]
    have hp : (ds.sum + 1) ^ ds.length ≤ (r + ds.sum + 1) ^ ds.length :=
      Nat.pow_le_pow_left (by omega) ds.length
    calc
      (r + 1) * (List.map (fun r => r + 1) ds).prod ≤
          (r + ds.sum + 1) * (r + ds.sum + 1) ^ ds.length :=
        Nat.mul_le_mul (by omega) (ih.trans hp)
      _ = (r + ds.sum + 1) ^ (ds.length + 1) := by
        rw [pow_succ, Nat.mul_comm]

instance cornerFintype : (ds : List ℕ) → Fintype (Corner ds)
  | [] => inferInstanceAs (Fintype PUnit)
  | _ :: ds =>
    letI := cornerFintype ds
    inferInstanceAs (Fintype (Bool × Corner ds))

theorem corner_card (ds : List ℕ) : Fintype.card (Corner ds) = 2 ^ ds.length := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    change Fintype.card (Bool × Corner ds) = _
    rw [Fintype.card_prod, Fintype.card_bool, ih]
    simp [pow_succ, Nat.mul_comm]

/-- Duplicate corners in zero-degree coordinates are counted only once. -/
def cornerAnchors (ds : List ℕ) : Finset (Grid ds) := by
  classical
  exact Finset.univ.image (cornerIndex ds)

theorem cornerIndex_mem (ds : List ℕ) (b : Corner ds) :
    cornerIndex ds b ∈ cornerAnchors ds := by
  classical
  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩

theorem cornerAnchors_card_le (ds : List ℕ) :
    (cornerAnchors ds).card ≤ 2 ^ ds.length := by
  classical
  calc
    (cornerAnchors ds).card ≤ (Finset.univ : Finset (Corner ds)).card :=
      Finset.card_image_le
    _ = 2 ^ ds.length := by rw [Finset.card_univ, corner_card]

def repairedCurve (ds : List ℕ) (anchors : Finset (Grid ds))
    (anchorValues estimates : Grid ds → ℝ) : Params ds → ℝ :=
  curve ds (PosetShapeRepair.repair anchors anchorValues estimates)

/-- Shape holds for every estimate table, before assuming any accuracy event. -/
theorem repairedCurve_shape (ds : List ℕ) (anchors : Finset (Grid ds))
    (anchorValues estimates : Grid ds → ℝ)
    (ha : ∀ a ∈ anchors, 0 ≤ anchorValues a ∧ anchorValues a ≤ 1) :
    AntitoneOn (repairedCurve ds anchors anchorValues estimates) {p | cube ds p} ∧
      ∀ p, cube ds p →
        0 ≤ repairedCurve ds anchors anchorValues estimates p ∧
        repairedCurve ds anchors anchorValues estimates p ≤ 1 :=
  ⟨curve_antitone ds _ (PosetShapeRepair.repair_antitone anchors anchorValues estimates),
    curve_range ds _ (PosetShapeRepair.repair_range anchors anchorValues estimates ha)⟩

/-- The original coefficient event implies simultaneous two-tail accuracy at
every parameter vector, with no loss of tolerance. -/
theorem repairedCurve_relPair (ds : List ℕ) (anchors : Finset (Grid ds))
    (anchorValues estimates f : Grid ds → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hf : Antitone f)
    (hrange : ∀ j, 0 ≤ f j ∧ f j ≤ 1)
    (ha : ∀ a ∈ anchors, anchorValues a = f a)
    (hpair : ∀ j, RelPair ε (f j) (estimates j)) :
    ∀ p, cube ds p →
      RelPair ε (curve ds f p) (repairedCurve ds anchors anchorValues estimates p) :=
  curve_relPair ds
    (PosetShapeRepair.repair_relPair anchors anchorValues estimates f hε hε1 hf hrange ha hpair)

/-- Exact supplied anchors at all corners give exact corner values, even when
the estimates elsewhere are inaccurate. -/
theorem repairedCurve_corner (ds : List ℕ) (anchors : Finset (Grid ds))
    (anchorValues estimates f : Grid ds → ℝ) (hf : Antitone f)
    (hzero : ∀ j, 0 ≤ f j) (ha : ∀ a ∈ anchors, anchorValues a = f a)
    (hc : ∀ b, cornerIndex ds b ∈ anchors) (b : Corner ds) :
    repairedCurve ds anchors anchorValues estimates (cornerParams ds b) =
      f (cornerIndex ds b) := by
  rw [repairedCurve, curve_corner]
  rw [PosetShapeRepair.repair_anchor anchors anchorValues estimates
    (fun a h => by rw [ha a h]; exact hzero a)
    (fun a hA b hB hab => by rw [ha a hA, ha b hB]; exact hf hab) (hc b)]
  exact ha _ (hc b)

/-- Deterministic repair preserves any lower bound on the number of successful
seeds. In particular it consumes no additional failure-probability allowance. -/
theorem repairedCurve_confidence (ds : List ℕ) {Ω : Type*} [Fintype Ω]
    (anchors : Finset (Grid ds)) (anchorValues f : Grid ds → ℝ)
    (estimates : Ω → Grid ds → ℝ) {ε bound : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hf : Antitone f)
    (hrange : ∀ j, 0 ≤ f j ∧ f j ≤ 1)
    (ha : ∀ a ∈ anchors, anchorValues a = f a)
    (hbound : bound ≤ ((Finset.univ.filter (fun ω =>
      ∀ j, RelPair ε (f j) (estimates ω j))).card : ℝ)) :
    bound ≤ ((Finset.univ.filter (fun ω =>
      ∀ p, cube ds p → RelPair ε (curve ds f p)
        (repairedCurve ds anchors anchorValues (estimates ω) p))).card : ℝ) := by
  classical
  have hcards : (Finset.univ.filter (fun ω =>
      ∀ j, RelPair ε (f j) (estimates ω j))).card ≤
      (Finset.univ.filter (fun ω =>
        ∀ p, cube ds p → RelPair ε (curve ds f p)
          (repairedCurve ds anchors anchorValues (estimates ω) p))).card := by
    apply Finset.card_le_card
    intro ω hω
    simp only [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, repairedCurve_relPair ds anchors anchorValues (estimates ω) f
      hε hε1 hf hrange ha hω.2⟩
  exact hbound.trans (by exact_mod_cast hcards)

end QecReliability.MultivariateShapeRepair
