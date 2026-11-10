import PhysicalBridge.PostprocessShape

/-! Exact zero tails are a deterministic property, independent of confidence. -/
noncomputable section
namespace QecReliability
open scoped BigOperators

def TailExact (f g : ℝ) : Prop := (f=0 → g=0) ∧ (f=1 → g=1)

theorem endpointCoefficients_tailExact {r : ℕ} (f g : Fin (r+1) → ℝ)
    (ht : ∀ j, TailExact (f j) (g j)) :
    ∀ j, TailExact (f j) (endpointCoefficients f g j) := by
  intro j
  by_cases hz : j.val=0
  · have hj : j=0 := Fin.ext hz
    subst j
    simp [endpointCoefficients,shapeInput,TailExact]
  · by_cases hr : j.val=r
    · have hj : j=Fin.last r := Fin.ext hr
      subst j
      change TailExact (f (Fin.last r)) (shapeInput f g r)
      rw [(shapeInput_endpoints f g).2]
      exact ⟨id,id⟩
    · simpa only [endpointCoefficients,shapeInput,if_neg hz,if_neg hr,extendCoefficients_at] using ht j

theorem shapeCoefficients_tailExact {r : ℕ} (f g : Fin (r+1) → ℝ)
    (hf : ∀ j, 0≤f j ∧ f j≤1) (hg : ∀ j, 0≤g j ∧ g j≤1)
    (ha : Antitone f) (ht : ∀ j, TailExact (f j) (g j)) :
    ∀ j, TailExact (f j) (shapeCoefficients f g j) := by
  intro j
  have he := endpointCoefficients_tailExact f g ht
  have hr := endpointCoefficients_range f g hf hg
  constructor
  · intro hz
    have hl : f (Fin.last r)=0 := le_antisymm (by simpa [hz] using ha (show j≤Fin.last r from Nat.le_of_lt_succ j.isLt)) (hf _).1
    have hm : 0≤runningMin (shapeInput f g) j.val := by
      apply (le_runningMin_iff _ _ _).mpr
      intro i hi
      exact (hr ⟨i,by omega⟩).1
    have hu := runningMin_le_current (shapeInput f g) j.val
    have hj := (he j).1 hz
    change shapeInput f g j.val=0 at hj
    rw [hj] at hu
    have hm0 := le_antisymm hu hm
    change max (f (Fin.last r)) (runningMin (shapeInput f g) j.val)=0
    rw [hl,hm0,max_self]
  · intro ho
    have hall : ∀ i≤j.val, shapeInput f g i=1 := by
      intro i hi
      let k : Fin (r+1) := ⟨i,by omega⟩
      have hk : f k=1 := le_antisymm (hf k).2 (by simpa [ho] using ha (show k≤j from hi))
      exact (he k).2 hk
    have hlo := (le_runningMin_iff (shapeInput f g) j.val 1).mpr (fun i hi => (hall i hi).ge)
    have hhi := runningMin_le_current (shapeInput f g) j.val
    rw [hall j.val le_rfl] at hhi
    have hm := le_antisymm hhi hlo
    change max (f (Fin.last r)) (runningMin (shapeInput f g) j.val)=1
    rw [hm,max_eq_right (hf _).2]

theorem average_zero_transfer {ι : Type*} [Fintype ι] (w f g : ι → ℝ)
    (hw : ∀ i,0≤w i) (hf : ∀ i,0≤f i) (ht : ∀ i,f i=0 → g i=0)
    (hz : average w f=0) : average w g=0 := by
  classical
  have hterm : ∀ i,w i*f i=0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hw k) (hf k))).mp hz i (Finset.mem_univ i)
  unfold average
  apply Finset.sum_eq_zero
  intro i _
  rcases mul_eq_zero.mp (hterm i) with hi|hi
  · rw [hi,zero_mul]
  · rw [ht i hi,mul_zero]

theorem average_tailExact {ι : Type*} [Fintype ι] (w f g : ι → ℝ)
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (hf : ∀ i,0≤f i ∧ f i≤1)
    (ht : ∀ i,TailExact (f i) (g i)) : TailExact (average w f) (average w g) := by
  refine ⟨average_zero_transfer w f g hw (fun i => (hf i).1) (fun i => (ht i).1),?_⟩
  intro ho
  have h := average_zero_transfer w (fun i => 1-f i) (fun i => 1-g i) hw
    (fun i => sub_nonneg.mpr (hf i).2)
    (fun i hi => by
      change 1-f i=0 at hi
      change 1-g i=0
      rw [(ht i).2 (by linarith)]; ring)
    (by rw [average_complement w f hs,ho]; ring)
  rw [average_complement w g hs] at h
  linarith

theorem bernsteinCurve_tailExact {r : ℕ} (f g : Fin (r+1) → ℝ)
    (hf : ∀ j,0≤f j ∧ f j≤1) (ht : ∀ j,TailExact (f j) (g j))
    {p : ℝ} (hp : 0≤p) (hp1 : p≤1) :
    TailExact (bernsteinCurve r f p) (bernsteinCurve r g p) :=
  average_tailExact _ f g (bernsteinWeight_nonneg hp hp1) (bernsteinWeight_sum r p) hf ht

end QecReliability
