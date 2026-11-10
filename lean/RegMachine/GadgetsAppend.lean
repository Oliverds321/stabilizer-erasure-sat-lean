import RegMachine.Gadgets

/-!
# Gadgets: `append`, tests, constants

`appendM i j` (`i ≠ j`): `reg i := reg i ++ reg j` in `2|i| + 3|j| + 4` steps.
Tests and constants halt immediately (zero steps) with their answer.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape Turing Function RegSyms

variable {k : ℕ} {Γ : Type} [Fintype Γ] [Inhabited Γ] [RegSyms Γ]

/-- Head positions: tape `i` at `a`, tape `j` at `b`, others at `0`. -/
abbrev pos2 (i : Fin (k + 1)) (a : ℤ) (j : Fin (k + 1)) (b : ℤ) : Fin (k + 1) → ℤ :=
  update (pos1 i a) j b

section Pos2
variable {i j : Fin (k + 1)} (hij : i ≠ j)
include hij

theorem pos2_i (a b : ℤ) : pos2 i a j b i = a := by
  simp [pos2, update_of_ne hij]

theorem pos2_upd_i (a b a' : ℤ) : update (pos2 i a j b) i a' = pos2 i a' j b := by
  unfold pos2 pos1
  rw [update_comm hij.symm, update_idem]

theorem inW_pos2 {W : Fin (k + 1) → Set ℤ} (hW : ∀ t, (0 : ℤ) ∈ W t) {a b : ℤ}
    (ha : a ∈ W i) (hb : b ∈ W j) : InW W (pos2 i a j b) :=
  (inW_pos1 hW ha).update hb

end Pos2

theorem pos2_j {i j : Fin (k + 1)} (a b : ℤ) : pos2 i a j b j = b := by simp [pos2]

theorem pos2_upd_j {i j : Fin (k + 1)} (a b b' : ℤ) : update (pos2 i a j b) j b' = pos2 i a j b' := by
  simp [pos2]

theorem pos2_zero_j (i j : Fin (k + 1)) (a : ℤ) (hij : i ≠ j) : pos2 i a j 0 = pos1 i a := by
  funext t
  by_cases ht : t = j
  · subst ht; simp [pos2, update_of_ne hij.symm]
  · simp [pos2, update_of_ne ht]

/-! ## `append` -/

set_option backward.isDefEq.respectTransparency false in
inductive AppL where
  | scanD | copy | rewD | rewS | done
  deriving DecidableEq, Fintype

/-- `reg i := reg i ++ reg j` (for `i ≠ j`). -/
def appendM (i j : Fin (k + 1)) : Machine k Γ AppL :=
  mkMachine .scanD fun q heads =>
    match q with
    | .scanD => match dec (heads i) with
      | some _ => .advance .scanD heads (moves1 i .right)
      | none => .advance .copy heads (fun _ => .stay)
    | .copy => match dec (heads j) with
      | some x => .advance .copy (update heads i (sym x)) (moves2 i .right j .right)
      | none => .advance .rewD heads (moves1 i .left)
    | .rewD => match dec (heads i) with
      | some _ => .advance .rewD heads (moves1 i .left)
      | none => .advance .rewS heads (moves2 i .right j .left)
    | .rewS => match dec (heads j) with
      | some _ => .advance .rewS heads (moves1 j .left)
      | none => .advance .done heads (moves1 j .right)
    | .done => .halt true

section AppT
variable (i j : Fin (k + 1)) {heads : Fin (k + 1) → Γ}
theorem appendM_scanD_some (h : dec (heads i) ≠ none) :
    (appendM i j).transition .scanD heads = .advance .scanD heads (moves1 i .right) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some x => simp [appendM, mkMachine, hd]
theorem appendM_scanD_none (h : dec (heads i) = none) :
    (appendM i j).transition .scanD heads = .advance .copy heads (fun _ => .stay) := by
  simp [appendM, mkMachine, h]
theorem appendM_copy_some (h : dec (heads j) ≠ none) :
    (appendM i j).transition .copy heads =
      .advance .copy (update heads i ((fun x _ => optSym (dec x)) (heads j) (heads i)))
        (moves2 i .right j .right) := by
  cases hd : dec (heads j) with
  | none => exact absurd hd h
  | some x => simp [appendM, mkMachine, hd]
theorem appendM_copy_none (h : dec (heads j) = none) :
    (appendM i j).transition .copy heads = .advance .rewD heads (moves1 i .left) := by
  simp [appendM, mkMachine, h]
theorem appendM_rewD_some (h : dec (heads i) ≠ none) :
    (appendM i j).transition .rewD heads = .advance .rewD heads (moves1 i .left) := by
  cases hd : dec (heads i) with
  | none => exact absurd hd h
  | some x => simp [appendM, mkMachine, hd]
theorem appendM_rewD_none (h : dec (heads i) = none) :
    (appendM i j).transition .rewD heads = .advance .rewS heads (moves2 i .right j .left) := by
  simp [appendM, mkMachine, h]
theorem appendM_rewS_some (h : dec (heads j) ≠ none) :
    (appendM i j).transition .rewS heads = .advance .rewS heads (moves1 j .left) := by
  cases hd : dec (heads j) with
  | none => exact absurd hd h
  | some x => simp [appendM, mkMachine, hd]
theorem appendM_rewS_none (h : dec (heads j) = none) :
    (appendM i j).transition .rewS heads = .advance .done heads (moves1 j .right) := by
  simp [appendM, mkMachine, h]
theorem appendM_done : (appendM i j).transition .done heads = .halt true := by
  simp [appendM, mkMachine]
end AppT

theorem append_spec {i j : Fin (k + 1)} (hij : i ≠ j) (s : Fin (k + 1) → List Bool)
    {W : Fin (k + 1) → Set ℤ} (hW : ∀ t, (0 : ℤ) ∈ W t)
    (hWi : ∀ z : ℤ, -1 ≤ z → z ≤ (s i).length + (s j).length → z ∈ W i)
    (hWj : ∀ z : ℤ, -1 ≤ z → z ≤ (s j).length → z ∈ W j) :
    ARun (appendM (Γ := Γ) i j) W (nf .scanD s) (2 * (s i).length + 3 * (s j).length + 4)
        (nf .done (update s i (s i ++ s j))) ∧
      aanswer (appendM (Γ := Γ) i j) (nf .done (update s i (s i ++ s j))) = some true := by
  have hji : j ≠ i := fun h => hij h.symm
  have hP0 : InW W (fun _ => (0 : ℤ)) := hW
  set D := (s i).length with hD
  set E := (s j).length with hE
  -- the appended contents
  set C1 : Fin (k + 1) → ℤ → Γ := update (regC s) i (cellOf (s i ++ s j)) with hC1
  have hC1j : C1 j = cellOf (s j) := by simp [hC1, update_of_ne hji]
  -- 1. scan the destination
  have h1 : ARun (appendM (Γ := Γ) i j) W ⟨.scanD, regC s, fun _ => 0⟩ D
      ⟨.scanD, regC s, pos1 i D⟩ := by
    have := run_scanR (M := appendM (Γ := Γ) i j) (W := W) (q := .scanD) (i := i)
      (fun x => dec x ≠ none) (fun _ h => appendM_scanD_some i j h)
      D (regC s) (fun _ => 0)
      (fun t ht => by
        have := cont_cellOf (Γ := Γ) (w := s i) (z := t) (by omega) (by omega)
        simpa using this) hP0
      (fun t ht => by simpa using hWi t (by omega) (by omega))
    simpa using this
  have h2 : astep (appendM (Γ := Γ) i j) ⟨.scanD, regC s, pos1 i D⟩ =
      some ⟨.copy, regC s, pos1 i D⟩ :=
    astep_stay (appendM_scanD_none i j (by simp [bitAt_ge, hD]))
  -- 2. copy the source
  have h3 : ARun (appendM (Γ := Γ) i j) W ⟨.copy, regC s, pos1 i D⟩ E
      ⟨.copy, C1, pos2 i (D + E) j E⟩ := by
    have := run_copyR (M := appendM (Γ := Γ) i j) (W := W) (q := .copy) hij
      (fun x => dec x ≠ none) (fun x _ => optSym (dec x)) (fun _ h => appendM_copy_some i j h)
      E (regC s) (pos1 i D)
      (fun t ht => by
        have := cont_cellOf (Γ := Γ) (w := s j) (z := t) (by omega) (by omega)
        simpa [update_of_ne hji] using this)
      (inW_pos1 hW (hWi _ (by omega) (by omega)))
      (fun t ht => by simpa using hWi (D + t) (by omega) (by omega))
      (fun t ht => by simpa [update_of_ne hji] using hWj t (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl ?_ ?_)
    · rw [hC1]
      refine congrArg (update (regC s) i) ?_
      rw [← cellOf_append (Γ := Γ) (s i) (s j)]
      funext z
      simp only [update_self, update_of_ne hji, regC]
      split_ifs <;> simp [hD]
    · simp [pos2, update_of_ne hji]
  -- 3. turn around and rewind the destination
  have h4 : astep (appendM (Γ := Γ) i j) ⟨.copy, C1, pos2 i (D + E) j E⟩ =
      some ⟨.rewD, C1, pos2 i (D + E - 1) j E⟩ := by
    have := astep_move1 (M := appendM (Γ := Γ) i j) (a := ⟨.copy, C1, pos2 i (D + E) j E⟩)
      (appendM_copy_none i j (by simp [hC1j, bitAt_ge, hE]))
    dsimp only at this
    rw [this, pos2_i hij, pos2_upd_i hij]
    simp [Move.delta, sub_eq_add_neg]
  have h5 : ARun (appendM (Γ := Γ) i j) W ⟨.rewD, C1, pos2 i (D + E - 1) j E⟩ (D + E)
      ⟨.rewD, C1, pos2 i (-1) j E⟩ := by
    have := run_scanL (M := appendM (Γ := Γ) i j) (W := W) (q := .rewD) (i := i)
      (fun x => dec x ≠ none) (fun _ h => appendM_rewD_some i j h)
      (D + E) C1 (pos2 i (D + E - 1) j E)
      (fun t ht => by
        rw [pos2_i hij, hC1, update_self]
        exact cont_cellOf (by omega) (by simp; omega))
      (inW_pos2 hij hW (hWi _ (by omega) (by omega)) (hWj _ (by omega) (by omega)))
      (fun t ht => by rw [pos2_i hij]; exact hWi _ (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl rfl ?_)
    rw [pos2_i hij, pos2_upd_i hij]
    congr 1; push_cast; ring_nf
  have h6 : astep (appendM (Γ := Γ) i j) ⟨.rewD, C1, pos2 i (-1) j E⟩ =
      some ⟨.rewS, C1, pos2 i 0 j (E - 1)⟩ := by
    have := astep_move2 (M := appendM (Γ := Γ) i j) (a := ⟨.rewD, C1, pos2 i (-1) j E⟩) hij
      (appendM_rewD_none i j (by simp [pos2_i hij, hC1, bitAt_neg]))
    dsimp only at this
    rw [this, pos2_i hij, pos2_j, pos2_upd_i hij, pos2_upd_j]
    simp [Move.delta, sub_eq_add_neg]
  -- 4. rewind the source
  have h7 : ARun (appendM (Γ := Γ) i j) W ⟨.rewS, C1, pos2 i 0 j (E - 1)⟩ E
      ⟨.rewS, C1, pos2 i 0 j (-1)⟩ := by
    have := run_scanL (M := appendM (Γ := Γ) i j) (W := W) (q := .rewS) (i := j)
      (fun x => dec x ≠ none) (fun _ h => appendM_rewS_some i j h)
      E C1 (pos2 i 0 j (E - 1))
      (fun t ht => by
        rw [pos2_j, hC1j]
        exact cont_cellOf (by omega) (by omega))
      (inW_pos2 hij hW (hW i) (hWj _ (by omega) (by omega)))
      (fun t ht => by rw [pos2_j]; exact hWj _ (by omega) (by omega))
    refine this.of_eq (ACfg.ext rfl rfl ?_)
    rw [pos2_j, pos2_upd_j]
    congr 1; ring_nf
  have h8 : astep (appendM (Γ := Γ) i j) ⟨.rewS, C1, pos2 i 0 j (-1)⟩ =
      some ⟨.done, C1, pos2 i 0 j 0⟩ := by
    have := astep_move1 (M := appendM (Γ := Γ) i j) (a := ⟨.rewS, C1, pos2 i 0 j (-1)⟩)
      (appendM_rewS_none i j (by simp [hC1j, bitAt_neg]))
    dsimp only at this
    rw [this, pos2_j, pos2_upd_j]
    simp [Move.delta]
  have hend : (⟨.done, C1, pos2 i 0 j 0⟩ : ACfg k Γ AppL) = nf .done (update s i (s i ++ s j)) := by
    refine ACfg.ext rfl ?_ ?_
    · show C1 = regC (update s i (s i ++ s j))
      rw [regC_update]
    · rw [pos2_zero_j i j 0 hij, pos1_zero]; rfl
  refine ⟨?_, aanswer_of_halt (appendM_done i j)⟩
  have hw1 : InW W (pos2 i 0 j (E - 1)) := inW_pos2 hij hW (hW i) (hWj _ (by omega) (by omega))
  have hrun := h1.trans (ARun.step h2 (h3.trans (ARun.step h4 (h5.trans (ARun.step h6
    (h7.trans (ARun.single h8 h7.end_mem (inW_pos2 hij hW (hW i) (hW j)))) h5.end_mem))
      h3.end_mem)) h1.end_mem)
  have e : D + (E + (D + E + (E + 1 + 1) + 1) + 1) = 2 * D + 3 * E + 4 := by ring
  rw [e] at hrun
  exact hrun.of_eq hend

/-! ## Tests and constants (zero steps) -/

/-- Test `reg i = []`. -/
def isEmptyM (i : Fin (k + 1)) : Machine k Γ Unit :=
  mkMachine () fun _ heads => .halt (decide (dec (heads i) = none))

/-- Test `(reg i).head? = some b`. -/
def headIsM (i : Fin (k + 1)) (b : Bool) : Machine k Γ Unit :=
  mkMachine () fun _ heads => .halt (decide (dec (heads i) = some b))

/-- Halt immediately with answer `b`. -/
def constM (b : Bool) : Machine k Γ Unit :=
  mkMachine () fun _ _ => .halt b

theorem isEmpty_answer (i : Fin (k + 1)) (s : Fin (k + 1) → List Bool) :
    aanswer (isEmptyM (Γ := Γ) i) (nf () s) = some (decide (s i = [])) := by
  apply aanswer_of_halt
  simp [isEmptyM, mkMachine, nf, bitAt]

theorem headIs_answer (i : Fin (k + 1)) (b : Bool) (s : Fin (k + 1) → List Bool) :
    aanswer (headIsM (Γ := Γ) i b) (nf () s) = some (decide ((s i).head? = some b)) := by
  apply aanswer_of_halt
  simp [headIsM, mkMachine, nf, bitAt, List.head?_eq_getElem?]

theorem const_answer (b : Bool) (s : Fin (k + 1) → List Bool) :
    aanswer (constM (k := k) (Γ := Γ) b) (nf () s) = some b := by
  apply aanswer_of_halt
  simp [constM, mkMachine]

theorem nf_run_zero {L : Type} [Fintype L] (M : Machine k Γ L) (q : L)
    (s : Fin (k + 1) → List Bool) {W : Fin (k + 1) → Set ℤ} (hW : ∀ t, (0 : ℤ) ∈ W t) :
    ARun M W (nf q s) 0 (nf q s) := .nil hW

end QecReliability.RegMachine
