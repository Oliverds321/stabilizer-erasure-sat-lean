import QecReliability.Normalization
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Anchored antitone repair on a finite partial order

This is a new construction. It uses only the supplied anchor values and estimates;
the unknown target occurs solely in the correctness statements. Arbitrary estimates
are clipped before taking finite prefix minima, and anchors above a point impose a
finite lower envelope. No extra relative-error tolerance is consumed.
-/

namespace QecReliability.PosetShapeRepair

noncomputable section

variable {ι : Type*} [Fintype ι] [PartialOrder ι]

/-- Clip an arbitrary real estimate to the unit interval. -/
def clip (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clip_nonneg (x : ℝ) : 0 ≤ clip x := le_max_left _ _

theorem clip_le_one (x : ℝ) : clip x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem clip_eq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : clip x = x := by
  rw [clip, min_eq_right hx1, max_eq_right hx]

/-- Keep exact supplied anchors; clip every other estimate. -/
def anchoredEstimate (anchors : Finset ι) (anchorValues estimates : ι → ℝ) (i : ι) : ℝ := by
  classical
  exact if i ∈ anchors then anchorValues i else clip (estimates i)

private def lowerSet (j : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => i ≤ j)

private theorem mem_lowerSet (i j : ι) : i ∈ lowerSet j ↔ i ≤ j := by
  classical
  simp [lowerSet]

private theorem lowerSet_nonempty (j : ι) : (lowerSet j).Nonempty :=
  ⟨j, (mem_lowerSet j j).mpr le_rfl⟩

/-- Minimum of all estimates at points below the argument, including itself. -/
def prefixMinimum (g : ι → ℝ) (j : ι) : ℝ :=
  (lowerSet j).inf' (lowerSet_nonempty j) g

theorem le_prefixMinimum_iff (g : ι → ℝ) (j : ι) (b : ℝ) :
    b ≤ prefixMinimum g j ↔ ∀ i, i ≤ j → b ≤ g i := by
  classical
  simp only [prefixMinimum, Finset.le_inf'_iff, mem_lowerSet]

theorem prefixMinimum_le (g : ι → ℝ) {i j : ι} (hij : i ≤ j) :
    prefixMinimum g j ≤ g i :=
  Finset.inf'_le g ((mem_lowerSet i j).mpr hij)

theorem prefixMinimum_antitone (g : ι → ℝ) : Antitone (prefixMinimum g) := by
  intro i j hij
  apply (le_prefixMinimum_iff g i _).mpr
  intro k hki
  exact prefixMinimum_le g (hki.trans hij)

private def floorValues (anchors : Finset ι) (anchorValues : ι → ℝ) (j : ι) : Finset ℝ := by
  classical
  exact insert 0 ((anchors.filter (fun a => j ≤ a)).image anchorValues)

private theorem floorValues_nonempty (anchors : Finset ι) (anchorValues : ι → ℝ) (j : ι) :
    (floorValues anchors anchorValues j).Nonempty := by
  classical
  exact ⟨0, by simp [floorValues]⟩

/-- Maximum of zero and all supplied anchor values at points above the argument. -/
def anchorFloor (anchors : Finset ι) (anchorValues : ι → ℝ) (j : ι) : ℝ :=
  (floorValues anchors anchorValues j).sup'
    (floorValues_nonempty anchors anchorValues j) id

theorem anchorFloor_le_iff (anchors : Finset ι) (anchorValues : ι → ℝ) (j : ι) (b : ℝ) :
    anchorFloor anchors anchorValues j ≤ b ↔
      0 ≤ b ∧ ∀ a ∈ anchors, j ≤ a → anchorValues a ≤ b := by
  classical
  constructor
  · intro h
    have hb : ∀ v ∈ floorValues anchors anchorValues j, v ≤ b :=
      (Finset.sup'_le_iff (floorValues_nonempty anchors anchorValues j) id).mp h
    refine ⟨hb 0 (by simp [floorValues]), ?_⟩
    intro a ha hja
    apply hb (anchorValues a)
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨ha, hja⟩, rfl⟩)
  · rintro ⟨hzero, hanchors⟩
    apply Finset.sup'_le
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · subst v
      exact hzero
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      exact hanchors a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2

theorem anchorFloor_nonneg (anchors : Finset ι) (anchorValues : ι → ℝ) (j : ι) :
    0 ≤ anchorFloor anchors anchorValues j := by
  classical
  exact Finset.le_sup' id (by simp [floorValues])

theorem le_anchorFloor (anchors : Finset ι) (anchorValues : ι → ℝ)
    {a j : ι} (ha : a ∈ anchors) (hja : j ≤ a) :
    anchorValues a ≤ anchorFloor anchors anchorValues j := by
  classical
  apply Finset.le_sup' id
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨a, Finset.mem_filter.mpr ⟨ha, hja⟩, rfl⟩)

theorem anchorFloor_antitone (anchors : Finset ι) (anchorValues : ι → ℝ) :
    Antitone (anchorFloor anchors anchorValues) := by
  intro i j hij
  apply (anchorFloor_le_iff anchors anchorValues j _).mpr
  refine ⟨anchorFloor_nonneg anchors anchorValues i, ?_⟩
  intro a ha hja
  exact le_anchorFloor anchors anchorValues ha (hij.trans hja)

/-- Finite anchored shape repair. Its inputs contain no unknown target function. -/
def repair (anchors : Finset ι) (anchorValues estimates : ι → ℝ) (j : ι) : ℝ :=
  max (anchorFloor anchors anchorValues j)
    (prefixMinimum (anchoredEstimate anchors anchorValues estimates) j)

/-- Antitonicity holds even for arbitrary estimates and inconsistent anchors. -/
theorem repair_antitone (anchors : Finset ι) (anchorValues estimates : ι → ℝ) :
    Antitone (repair anchors anchorValues estimates) := by
  intro i j hij
  exact max_le_max (anchorFloor_antitone anchors anchorValues hij)
    (prefixMinimum_antitone (anchoredEstimate anchors anchorValues estimates) hij)

/-- Valid anchor values ensure the unit-interval range for arbitrary estimates. -/
theorem repair_range (anchors : Finset ι) (anchorValues estimates : ι → ℝ)
    (hanchors : ∀ a ∈ anchors, 0 ≤ anchorValues a ∧ anchorValues a ≤ 1) (j : ι) :
    0 ≤ repair anchors anchorValues estimates j ∧
      repair anchors anchorValues estimates j ≤ 1 := by
  classical
  refine ⟨(anchorFloor_nonneg anchors anchorValues j).trans (le_max_left _ _), ?_⟩
  apply max_le
  · apply (anchorFloor_le_iff anchors anchorValues j 1).mpr
    exact ⟨by norm_num, fun a ha _ => (hanchors a ha).2⟩
  · apply (prefixMinimum_le (anchoredEstimate anchors anchorValues estimates) le_rfl).trans
    by_cases hj : j ∈ anchors
    · simpa [anchoredEstimate, hj] using (hanchors j hj).2
    · simpa [anchoredEstimate, hj] using clip_le_one (estimates j)

/-- Every anchor is reproduced exactly when the supplied anchors are consistent.
No hypothesis on the estimates, nor on unobserved target values, is required. -/
theorem repair_anchor (anchors : Finset ι) (anchorValues estimates : ι → ℝ)
    (hnonneg : ∀ a ∈ anchors, 0 ≤ anchorValues a)
    (hconsistent : ∀ a ∈ anchors, ∀ b ∈ anchors, a ≤ b → anchorValues b ≤ anchorValues a)
    {a : ι} (ha : a ∈ anchors) : repair anchors anchorValues estimates a = anchorValues a := by
  classical
  apply le_antisymm
  · apply max_le
    · exact (anchorFloor_le_iff anchors anchorValues a _).mpr
        ⟨hnonneg a ha, fun b hb hab => hconsistent a ha b hb hab⟩
    · simpa [anchoredEstimate, ha] using
        (prefixMinimum_le (anchoredEstimate anchors anchorValues estimates) (le_refl a))
  · exact (le_anchorFloor anchors anchorValues ha le_rfl).trans (le_max_left _ _)

/-- Exact anchor data and the original two-sided relative estimates imply the same
`RelPair` after repair, with exactly the original tolerance. -/
theorem repair_relPair (anchors : Finset ι) (anchorValues estimates f : ι → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hanti : Antitone f)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hanchor : ∀ a ∈ anchors, anchorValues a = f a)
    (hpair : ∀ i, RelPair ε (f i) (estimates i)) (j : ι) :
    RelPair ε (f j) (repair anchors anchorValues estimates j) := by
  classical
  have hbase : ∀ i, relLower ε (f i) ≤ anchoredEstimate anchors anchorValues estimates i ∧
      anchoredEstimate anchors anchorValues estimates i ≤ relUpper ε (f i) := by
    intro i
    by_cases hi : i ∈ anchors
    · simpa [anchoredEstimate, hi, hanchor i hi] using
        And.intro (relLower_le_self hε (hf i).1 (hf i).2)
          (self_le_relUpper hε (hf i).1 (hf i).2)
    · have hrange := (hpair i).range hε1 (hf i).1 (hf i).2
      simpa [anchoredEstimate, hi, clip_eq hrange.1 hrange.2] using
        (relPair_iff_interval ε (f i) (estimates i)).mp (hpair i)
  have hlo : relLower ε (f j) ≤
      prefixMinimum (anchoredEstimate anchors anchorValues estimates) j := by
    apply (le_prefixMinimum_iff _ j _).mpr
    intro i hij
    exact (relLower_mono hε hε1 (hanti hij)).trans (hbase i).1
  have hfloor : anchorFloor anchors anchorValues j ≤ f j := by
    apply (anchorFloor_le_iff anchors anchorValues j (f j)).mpr
    refine ⟨(hf j).1, ?_⟩
    intro a ha hja
    rw [hanchor a ha]
    exact hanti hja
  apply (relPair_iff_interval _ _ _).mpr
  refine ⟨hlo.trans (le_max_right _ _), max_le ?_ ?_⟩
  · exact hfloor.trans (self_le_relUpper hε (hf j).1 (hf j).2)
  · exact (prefixMinimum_le (anchoredEstimate anchors anchorValues estimates) le_rfl).trans
      (hbase j).2

/-- Combined guarantee: shape is unconditional on estimate accuracy; accuracy
consumes no extra tolerance, and all supplied exact anchors survive. -/
theorem repair_spec (anchors : Finset ι) (anchorValues estimates f : ι → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hanti : Antitone f)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hanchor : ∀ a ∈ anchors, anchorValues a = f a)
    (hpair : ∀ i, RelPair ε (f i) (estimates i)) :
    Antitone (repair anchors anchorValues estimates) ∧
      (∀ j, 0 ≤ repair anchors anchorValues estimates j ∧
        repair anchors anchorValues estimates j ≤ 1) ∧
      (∀ a ∈ anchors, repair anchors anchorValues estimates a = anchorValues a) ∧
      (∀ j, RelPair ε (f j) (repair anchors anchorValues estimates j)) := by
  have ha : ∀ a ∈ anchors, 0 ≤ anchorValues a ∧ anchorValues a ≤ 1 := by
    intro a ha
    rw [hanchor a ha]
    exact hf a
  refine ⟨repair_antitone anchors anchorValues estimates,
    repair_range anchors anchorValues estimates ha, ?_,
    repair_relPair anchors anchorValues estimates f hε hε1 hanti hf hanchor hpair⟩
  intro a ha'
  apply repair_anchor anchors anchorValues estimates (fun b hb => (ha b hb).1) _ ha'
  intro b hb c hc hbc
  rw [hanchor b hb, hanchor c hc]
  exact hanti hbc

end

end QecReliability.PosetShapeRepair
