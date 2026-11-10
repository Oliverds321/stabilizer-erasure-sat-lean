import TensorMachineGrid
import Trans.Wire.Header

/-! Typed FL implementation of runtime tensor-grid enumeration. All loops are
existing certified list folds. The exported execution theorem is about the
compiled FL program, with its concrete compositional time/depth/size budgets. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.GridFL

open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid)

abbrev Row : Ty := .list .nat
abbrev Table : Ty := .list Row

structure Indices where
  prefixStep : ℕ
  prefixFold : ℕ
  prefixIdx : ℕ
  append : ℕ
  expandStep : ℕ
  expandFold : ℕ
  expand : ℕ
  gridFold : ℕ
  grid : ℕ

def prefixStepBody : Tm [.prod Row (.prod .nat Table)] (.prod .nat Table) :=
  .pair (.fst (.snd v0))
    (.lcons (.lcons (.fst (.snd v0)) (.fst v0)) (.snd (.snd v0)))

def prefixStepF (i : Indices) := bodySig i.prefixStep prefixStepBody

def prefixBody (i : Indices) : Tm [.prod .nat Table] Table :=
  .snd (.app (foldrF (prefixStepF i) i.prefixFold)
    (.pair (.snd v0) (.pair (.fst v0) .lnil)))

def prefixF (i : Indices) := bodySig i.prefixIdx (prefixBody i)

def expandStepBody (i : Indices) : Tm [.prod .nat (.prod Table Table)] (.prod Table Table) :=
  .letE (.app (prefixF i) (.pair (.fst v0) (.fst (.snd v0)))) <|
    .pair (.fst (.snd v1))
      (.app (appendF Row i.append) (.pair v0 (.snd (.snd v1))))

def expandStepF (i : Indices) := bodySig i.expandStep (expandStepBody i)

def expandBody (L : Lib) (i : Indices) : Tm [.prod .nat Table] Table :=
  .snd (.app (foldrF (expandStepF i) i.expandFold)
    (.pair (.app (rangeF L.range) (.app (succF L.succ) (.fst v0)))
      (.pair (.snd v0) .lnil)))

def expandF (L : Lib) (i : Indices) := bodySig i.expand (expandBody L i)

def gridBody (L : Lib) (i : Indices) : Tm [.list .nat] Table :=
  .app (foldrF (expandF L i) i.gridFold) (.pair v0 (.lcons .lnil .lnil))

def gridF (L : Lib) (i : Indices) := bodySig i.grid (gridBody L i)

theorem prefixStepF_den (i : Indices) (row : List ℕ) (j : ℕ) (acc : List (List ℕ)) :
    (prefixStepF i).den (row, j, acc) = (j, (j :: row) :: acc) := by
  simp [prefixStepF, prefixStepBody, bodySig_den, tm_simp]

theorem prefixFold_den (i : Indices) (xs : List (List ℕ)) (j : ℕ)
    (acc : List (List ℕ)) :
    foldrDen (prefixStepF i) xs (j, acc) = (j, xs.map (j :: ·) ++ acc) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (prefixStepF i).den (x, foldrDen (prefixStepF i) xs (j, acc)) = _
    rw [ih, prefixStepF_den]
    rfl

theorem prefixF_den (i : Indices) (j : ℕ) (xs : List (List ℕ)) :
    (prefixF i).den (j, xs) = xs.map (j :: ·) := by
  simp only [prefixF, bodySig_den, prefixBody, tm_simp, foldrF_den,
    List.append_nil]
  rw [prefixFold_den]
  simp only [List.append_nil]

theorem expandStepF_den (i : Indices) (j : ℕ) (xs acc : List (List ℕ)) :
    (expandStepF i).den (j, xs, acc) = (xs, xs.map (j :: ·) ++ acc) := by
  simp only [expandStepF, bodySig_den, expandStepBody, tm_simp, appendF_den]
  rw [prefixF_den]

theorem expandFold_den (i : Indices) (hs : List ℕ) (xs acc : List (List ℕ)) :
    foldrDen (expandStepF i) hs (xs, acc) =
      (xs, hs.flatMap (fun j => xs.map (j :: ·)) ++ acc) := by
  induction hs with
  | nil => rfl
  | cons j hs ih =>
    change (expandStepF i).den (j, foldrDen (expandStepF i) hs (xs, acc)) = _
    rw [ih, expandStepF_den]
    simp only [List.flatMap_cons, List.append_assoc]

theorem expandF_den (L : Lib) (i : Indices) (r : ℕ) (xs : List (List ℕ)) :
    (expandF L i).den (r, xs) =
      (List.range (r + 1)).flatMap (fun j => xs.map (j :: ·)) := by
  simp only [expandF, bodySig_den, expandBody, tm_simp, foldrF_den,
    rangeF_den, succF_den]
  rw [expandFold_den]
  simp only [List.append_nil]

theorem gridFold_den (L : Lib) (i : Indices) (ds : List ℕ) :
    foldrDen (expandF L i) ds [[]] = TensorMachine.grid ds := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    change (expandF L i).den (r, foldrDen (expandF L i) ds [[]]) = _
    rw [ih, expandF_den]
    rfl

theorem gridF_den (L : Lib) (i : Indices) (ds : List ℕ) :
    (gridF L i).den ds = TensorMachine.grid ds := by
  simp only [gridF, bodySig_den, gridBody, tm_simp, foldrF_den]
  exact gridFold_den L i ds

structure Indices.OK (L : Lib) (i : Indices) (P : FL.Program) : Prop where
  prefixStep : P[i.prefixStep]? = some prefixStepBody.compile
  prefixFold : P[i.prefixFold]? = some (foldrBody (prefixStepF i) i.prefixFold).compile
  prefixIdx : P[i.prefixIdx]? = some (prefixBody i).compile
  append : P[i.append]? = some (appendBody Row i.append).compile
  expandStep : P[i.expandStep]? = some (expandStepBody i).compile
  expandFold : P[i.expandFold]? = some (foldrBody (expandStepF i) i.expandFold).compile
  expand : P[i.expand]? = some (expandBody L i).compile
  gridFold : P[i.gridFold]? = some (foldrBody (expandF L i) i.gridFold).compile
  grid : P[i.grid]? = some (gridBody L i).compile

variable {L : Lib} {i : Indices} {P : FL.Program}

theorem prefixStep_valid (hi : Indices.OK L i P) : ∀ x, (prefixStepF i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.prefixStep
  simp [prefixStepBody, tm_simp]

theorem prefix_valid (hi : Indices.OK L i P) : ∀ x, (prefixF i).ValidAt P x := by
  have hf := Trans.Hash.foldr_validAll (prefixStep_valid hi) hi.prefixFold
  intro x
  apply bodySig_valid hi.prefixIdx
  simp [prefixBody, tm_simp, hf]

theorem expandStep_valid (hi : Indices.OK L i P) : ∀ x, (expandStepF i).ValidAt P x := by
  have ha := append_valid hi.append
  intro x
  apply bodySig_valid hi.expandStep
  simp [expandStepBody, tm_simp, prefix_valid hi, ha]

theorem expand_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ x, (expandF L i).ValidAt P x := by
  have hf := Trans.Hash.foldr_validAll (expandStep_valid hi) hi.expandFold
  intro x
  apply bodySig_valid hi.expand
  simp [expandBody, tm_simp, hf, hL.range, hL.succ]

theorem grid_valid (hL : L.OK P) (hi : Indices.OK L i P) :
    ∀ ds, (gridF L i).ValidAt P ds := by
  have hf := Trans.Hash.foldr_validAll (expand_valid hL hi) hi.gridFold
  intro ds
  apply bodySig_valid hi.grid
  simp [gridBody, tm_simp, hf]

/-- Actual compiled evaluation, not an assumed semantic iterator contract. -/
theorem grid_computes (hL : L.OK P) (hi : Indices.OK L i P) (ds : List ℕ) :
    FL.Computes P i.grid ((Ty.list Ty.nat).enc ds)
      (Table.enc (TensorMachine.grid ds))
      (max ((gridF L i).msize ds) ((Ty.list Ty.nat).enc ds).size)
      ((gridF L i).cost ds) ((gridF L i).depth ds) := by
  have h := (grid_valid hL hi ds).computes (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [gridF_den] at h
  exact h

end QecReliability.TensorMachine.GridFL
