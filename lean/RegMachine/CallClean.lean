import RegMachine.CallSpec

/-!
# The oracle-call gadget: cleanup of all engine tapes and the full specification

`call_spec` is the end-to-end statement of the call gadget (see `CallSpec.lean` for the
informal description).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape QecReliability.OracleCost.MultiTape.InjectiveTapeLift
open Turing Function RegSyms

variable {k kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- Contents after cleaning the first `m` engine tapes of the final observation `o`. -/
def cleanC (e : Embedding kE k) (o : Observed kE ΓE ΛE) (s : Fin (k + 1) → List Bool) (m : ℕ) :
    Fin (k + 1) → ℤ → Cell ΓE :=
  assemble e (fun j => if j.val < m then (fun _ => .blank) else finC o j) (regC s)

/-- Head positions after cleaning the first `m` engine tapes. -/
def cleanP (e : Embedding kE k) (o : Observed kE ΓE ΛE) (m : ℕ) : Fin (k + 1) → ℤ :=
  assemble e (fun j => if j.val < m then 0 else o.position j) (fun _ => 0)

variable {E : Machine kE ΓE ΛE} {e : Embedding kE k} {q : Fin (k + 1)}

/-- Interval data with the size bounded by the total visited cells. -/
theorem interval_bounds {o : Observed kE ΓE ΛE} (hint : IntervalObs o) (j : Fin (kE + 1)) :
    ∃ l r : ℤ, l ≤ 0 ∧ 0 ≤ r ∧ (↑(o.visited j) : Set ℤ) = Set.Icc l r ∧
      o.position j ∈ Set.Icc l r ∧ r - l + 1 ≤ (visitedCells o : ℤ) := by
  obtain ⟨l, r, hl, hr, hV, hp⟩ := hint j
  refine ⟨l, r, hl, hr, hV, hp, ?_⟩
  have hc := card_of_coe_Icc hV
  have hle : (o.visited j).card ≤ visitedCells o :=
    Finset.single_le_sum (f := fun j => (o.visited j).card) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  omega

theorem mem_visited_iff {o : Observed kE ΓE ΛE} {j : Fin (kE + 1)} {l r : ℤ}
    (hV : (↑(o.visited j) : Set ℤ) = Set.Icc l r) (z : ℤ) : z ∈ o.visited j ↔ l ≤ z ∧ z ≤ r := by
  rw [← Finset.mem_coe, hV, Set.mem_Icc]

theorem clean_one {o : Observed kE ΓE ΛE} (hint : IntervalObs o) (s : Fin (k + 1) → List Bool)
    (b : Bool) {W : Fin (k + 1) → Set ℤ} (hW0 : ∀ t, (0 : ℤ) ∈ W t) {Cb : ℕ}
    (hcells : visitedCells o ≤ Cb)
    (hWe : ∀ j (z : ℤ), -(Cb + 1 : ℤ) ≤ z → z ≤ Cb + 1 → z ∈ W (e j))
    (m : ℕ) (hm : m < kE + 1) :
    ∃ c : ℕ, c ≤ 3 * visitedCells o + 2 ∧
      ARun (callM E e q) W ⟨.clean b ⟨m, hm⟩ .right, cleanC e o s m, cleanP e o m⟩ c
        ⟨afterClean b ⟨m, hm⟩, cleanC e o s (m + 1), cleanP e o (m + 1)⟩ := by
  obtain ⟨l, r, hl, hr, hV, hp, hcard⟩ := interval_bounds hint ⟨m, hm⟩
  have hp' := hp
  simp only [Set.mem_Icc] at hp'
  have hPe : cleanP e o m (e ⟨m, hm⟩) = o.position ⟨m, hm⟩ := by
    simp [cleanP]
  have hCe : cleanC e o s m (e ⟨m, hm⟩) = finC o ⟨m, hm⟩ := by
    simp [cleanC]
  have hinW : InW W (cleanP e o m) := by
    intro t
    by_cases ht : ∃ j, e j = t
    · obtain ⟨j, rfl⟩ := ht
      simp only [cleanP, assemble_image]
      split_ifs
      · exact hW0 _
      · obtain ⟨l', r', _, _, _, hp2, hc2⟩ := interval_bounds hint j
        simp only [Set.mem_Icc] at hp2
        exact hWe j _ (by omega) (by omega)
    · push_neg at ht
      simp only [cleanP, assemble_outside e _ _ ht]
      exact hW0 t
  obtain ⟨c, hc, hrun⟩ := run_cleanTape (M := callM E e q) (W := W) (t := e ⟨m, hm⟩)
    (qR := .clean b ⟨m, hm⟩ .right) (qE := .clean b ⟨m, hm⟩ .erase)
    (qF := .clean b ⟨m, hm⟩ .find) (qN := afterClean b ⟨m, hm⟩)
    (fun _ h => callM_right_nb E e q b _ h) (fun _ h => callM_right_b E e q b _ h)
    (fun _ h => callM_erase_nb E e q b _ h) (fun _ h => callM_erase_b E e q b _ h)
    (fun _ h => callM_find_b E e q b _ h) (fun _ h => callM_find_nb E e q b _ h)
    (cleanC e o s m) (cleanP e o m) l r hl hr (by rw [hPe]; exact hp'.1) (by rw [hPe]; exact hp'.2)
    (fun z h1 h2 => by
      rw [hCe]
      have hz : z ∈ o.visited ⟨m, hm⟩ := (mem_visited_iff hV z).mpr ⟨h1, h2⟩
      simp [finC, engC, hz])
    (fun z hz => by
      rw [hCe]
      have hz' : z ∉ o.visited ⟨m, hm⟩ := fun h => by
        have := (mem_visited_iff hV z).mp h; omega
      simp [finC, engC, hz'])
    hinW (fun z h1 h2 => hWe _ z (by omega) (by omega))
  refine ⟨c, by omega, hrun.of_eq (ACfg.ext rfl ?_ ?_)⟩
  · simp only [cleanC]
    rw [assemble_update_eng]
    congr 1
    funext j
    by_cases hj : j = ⟨m, hm⟩
    · subst hj; simp
    · rw [update_of_ne hj]
      have : j.val ≠ m := fun h => hj (Fin.ext h)
      by_cases hlt : j.val < m
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]
  · simp only [cleanP]
    rw [assemble_update_eng]
    congr 1
    funext j
    by_cases hj : j = ⟨m, hm⟩
    · subst hj; simp
    · rw [update_of_ne hj]
      have : j.val ≠ m := fun h => hj (Fin.ext h)
      by_cases hlt : j.val < m
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

theorem clean_all {o : Observed kE ΓE ΛE} (hint : IntervalObs o) (s : Fin (k + 1) → List Bool)
    (b : Bool) {W : Fin (k + 1) → Set ℤ} (hW0 : ∀ t, (0 : ℤ) ∈ W t) {Cb : ℕ}
    (hcells : visitedCells o ≤ Cb)
    (hWe : ∀ j (z : ℤ), -(Cb + 1 : ℤ) ≤ z → z ≤ Cb + 1 → z ∈ W (e j)) :
    ∀ (d m : ℕ) (hm : m + d = kE), ∃ c : ℕ, c ≤ (d + 1) * (3 * visitedCells o + 2) ∧
      ARun (callM E e q) W ⟨.clean b ⟨m, by omega⟩ .right, cleanC e o s m, cleanP e o m⟩ c
        ⟨.done b, cleanC e o s (kE + 1), cleanP e o (kE + 1)⟩ := by
  intro d
  induction d with
  | zero =>
    intro m hm
    obtain ⟨c, hc, hrun⟩ := clean_one (E := E) (q := q) hint s b hW0 hcells hWe m (by omega)
    have ha : afterClean (kE := kE) (ΛE := ΛE) b ⟨m, by omega⟩ = .done b := by
      have h : ¬ (m + 1 < kE + 1) := by omega
      simp [afterClean, nextEng, h]
    have e1 : m + 1 = kE + 1 := by omega
    rw [ha, e1] at hrun
    exact ⟨c, by omega, hrun⟩
  | succ d ih =>
    intro m hm
    obtain ⟨c, hc, hrun⟩ := clean_one (E := E) (q := q) hint s b hW0 hcells hWe m (by omega)
    have ha : afterClean (kE := kE) (ΛE := ΛE) b ⟨m, by omega⟩ =
        .clean b ⟨m + 1, by omega⟩ .right := by
      have h : m + 1 < kE + 1 := by omega
      simp [afterClean, nextEng, h]
    rw [ha] at hrun
    obtain ⟨c2, hc2, hrun2⟩ := ih (m + 1) (by omega)
    refine ⟨c + c2, ?_, hrun.trans hrun2⟩
    have : (d + 1 + 1) * (3 * visitedCells o + 2) =
        (3 * visitedCells o + 2) + (d + 1) * (3 * visitedCells o + 2) := by ring
    omega

theorem length_le_cells {w : List Bool} (run : Completed E w) : w.length ≤ run.cells := by
  have h1 : ((initialObserved E w).visited 0).card ≤ (run.final.visited 0).card :=
    Finset.card_le_card (run.trace.visited_mono 0)
  have h2 : (run.final.visited 0).card ≤ run.cells :=
    Finset.single_le_sum (f := fun j => (run.final.visited j).card) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ 0)
  have h3 : w.length ≤ ((initialObserved E w).visited 0).card := by
    simp only [initialObserved, if_true]
    calc w.length = (Finset.image (fun j : ℕ => (j : ℤ)) (Finset.range w.length)).card := by
          rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
      _ ≤ _ := Finset.card_le_card (Finset.subset_insert _ _)
  omega

/-- **Call gadget specification.** -/
theorem call_spec (hq : ∀ j, e j ≠ q) (s : Fin (k + 1) → List Bool) (hs : ∀ j, s (e j) = [])
    (run : Completed E (s q)) {W : Fin (k + 1) → Set ℤ} {Cb : ℕ} (hC : run.cells ≤ Cb)
    (hW0 : ∀ t, (0 : ℤ) ∈ W t) (hWq : ∀ z : ℤ, -1 ≤ z → z ≤ (s q).length → z ∈ W q)
    (hWe : ∀ j (z : ℤ), -(Cb + 1 : ℤ) ≤ z → z ≤ Cb + 1 → z ∈ W (e j)) :
    ∃ m, m ≤ 2 * (s q).length + 3 + run.time + (kE + 1) * (3 * run.cells + 2) ∧
      ARun (callM E e q) W (nf .init s) m (nf (.done run.output) s) ∧
      aanswer (callM E e q) (nf (.done run.output) s) = some run.output := by
  have hlen := length_le_cells run
  -- prelude
  have h1 := call_prelude (E := E) hq s hs hW0 hWq
    (fun z h1 h2 => hWe 0 z (by omega) (by omega))
  rw [prelude_eq_simA] at h1
  -- simulation
  have hint : IntervalObs run.final := (IntervalObs.initial E (s q)).trace run.trace
  have hsub : ∀ j, ↑(run.final.visited j) ⊆ W (e j) := by
    intro j z hz
    obtain ⟨l, r, hl, hr, hV, _, hc⟩ := interval_bounds hint j
    rw [hV, Set.mem_Icc] at hz
    have : (visitedCells run.final : ℤ) ≤ Cb := by
      have := hC; unfold Completed.cells at this; omega
    exact hWe j z (by omega) (by omega)
  obtain ⟨Mk, hinv, h2⟩ := sim_run (q := q) run.trace s hW0 hsub _ (simInv_initial (s q))
  -- mark
  have h3 := mark_step (e := e) (q := q) hinv run.halt s
  have h3' : astep (callM E e q) (simA e run.final Mk s) =
      some ⟨.clean run.output ⟨0, by omega⟩ .right, cleanC e run.final s 0, cleanP e run.final 0⟩ := by
    rw [h3]
    congr 1
  -- cleanup
  have hcells : visitedCells run.final ≤ Cb := hC
  obtain ⟨c, hc, h4⟩ := clean_all (E := E) (q := q) hint s run.output hW0 hcells hWe kE 0 (by omega)
  have hfinal : (⟨.done run.output, cleanC e run.final s (kE + 1), cleanP e run.final (kE + 1)⟩ :
      ACfg k (Cell ΓE) (CallL kE ΛE)) = nf (.done run.output) s := by
    refine ACfg.ext rfl ?_ ?_
    · simp only [cleanC, nf]
      have : (fun j : Fin (kE + 1) => if j.val < kE + 1 then (fun _ => Cell.blank) else finC run.final j)
          = fun j => regC s (e j) := by
        funext j
        rw [if_pos j.isLt, regC_eng hs j]
      rw [this, assemble_restrict]
    · simp only [cleanP, nf]
      have : (fun j : Fin (kE + 1) => if j.val < kE + 1 then (0 : ℤ) else run.final.position j)
          = fun _ => 0 := by
        funext j; rw [if_pos j.isLt]
      rw [this]
      exact assemble_const_zero
  rw [hfinal] at h4
  refine ⟨2 * (s q).length + 3 + (run.transitions + (c + 1)), ?_, ?_, ?_⟩
  · have ht : run.time = run.transitions + 1 := rfl
    have : (kE + 1) * (3 * visitedCells run.final + 2) =
        (kE + 1) * (3 * run.cells + 2) := rfl
    omega
  · exact h1.trans (h2.trans (ARun.step h3' h4 (inW_simA hinv s hW0 hsub)))
  · exact aanswer_of_halt (callM_done E e q run.output)

end QecReliability.RegMachine
