import QecReliability.BinarySymplectic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.List.Basic

/-! Column-by-column binary elimination. The correctness target is the
dimension of the span of the supplied rows, including duplicate and zero rows. -/
namespace QecReliability.BinaryElimination
open QecReliability.Binary Module

abbrev Row (n : ℕ) := Fin n → Bit

def spanRows {n : ℕ} (rows : List (Row n)) : Submodule Bit (Row n) :=
  Submodule.span Bit {x | x∈rows}

def tailMap (n : ℕ) : Row (n+1) →ₗ[Bit] Row n where
  toFun x i := x i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def clearTail {n : ℕ} (p : Row (n+1)) : Row (n+1) →ₗ[Bit] Row n where
  toFun x i := x i.succ-x 0*p i.succ
  map_add' x y := by ext i; simp; ring
  map_smul' c x := by ext i; simp; ring

/-- Materialize coordinates once in an array before retaining a row function. -/
def cacheRow {n : ℕ} (x : Row n) : Row n :=
  let a := Array.ofFn x
  fun i => a[i.val]'(by simp [a])

@[simp] theorem cacheRow_eq {n : ℕ} (x : Row n) : cacheRow x=x := by
  funext i
  simp [cacheRow]

def rank : (n : ℕ) → List (Row n) → ℕ
  | 0,_ => 0
  | n+1,rows =>
    match rows.find? (fun x => decide (x 0≠0)) with
    | none => rank n (rows.map (fun x => cacheRow (tailMap n x)))
    | some p => rank n (rows.map (fun x => cacheRow (clearTail p x)))+1

theorem spanRows_map {n m : ℕ} (f : Row n →ₗ[Bit] Row m) (rows : List (Row n)) :
    spanRows (rows.map f)=(spanRows rows).map f := by
  rw [spanRows,spanRows,Submodule.map_span]
  congr 1
  ext x
  simp

def restrictedKernelEquiv {n m : ℕ} (S : Submodule Bit (Row n)) (f : Row n →ₗ[Bit] Row m) :
    LinearMap.ker (f.domRestrict S) ≃ₗ[Bit] (S ⊓ LinearMap.ker f : Submodule Bit (Row n)) where
  toFun x := ⟨x.val.val,x.val.property,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_map_kernel {n m : ℕ} (S : Submodule Bit (Row n)) (f : Row n →ₗ[Bit] Row m) :
    finrank Bit (S.map f)+finrank Bit (S ⊓ LinearMap.ker f : Submodule Bit (Row n))=finrank Bit S := by
  have h := (f.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict,(restrictedKernelEquiv S f).finrank_eq] at h
  exact h

theorem clearTail_kernel {n : ℕ} (p : Row (n+1)) (hp : p 0=1) :
    LinearMap.ker (clearTail p)=Bit ∙ p := by
  apply le_antisymm
  · intro x hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x 0,?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hp]
    · have hj := congrFun hx j
      change x j.succ-x 0*p j.succ=0 at hj
      exact (sub_eq_zero.mp hj).symm
  · apply Submodule.span_le.mpr
    intro x hx
    have he : x=p := Set.mem_singleton_iff.mp hx
    subst x
    change clearTail p p=0
    ext i
    simp [clearTail,hp]

theorem pivot_dimension {n : ℕ} (rows : List (Row (n+1))) (p : Row (n+1))
    (hp : p∈rows) (hp0 : p 0=1) :
    finrank Bit (spanRows (rows.map (clearTail p)))+1=finrank Bit (spanRows rows) := by
  have hk := clearTail_kernel p hp0
  have hmem : p∈spanRows rows := Submodule.subset_span hp
  have hle : (Bit ∙ p : Submodule Bit (Row (n+1)))≤spanRows rows := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hmem
  have hn : p≠0 := by intro h; rw [h] at hp0; exact zero_ne_one hp0
  have h := finrank_map_kernel (spanRows rows) (clearTail p)
  rw [hk,inf_eq_right.mpr hle,finrank_span_singleton hn,←spanRows_map] at h
  exact h

theorem zero_column_dimension {n : ℕ} (rows : List (Row (n+1)))
    (hz : ∀ x∈rows, x 0=0) :
    finrank Bit (spanRows (rows.map (tailMap n)))=finrank Bit (spanRows rows) := by
  have hall : ∀ x∈spanRows rows, x 0=0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hz x hx
    | zero => rfl
    | add x y hx hy ihx ihy => simp [ihx,ihy]
    | smul c x hx ih => simp [ih]
  have hk : spanRows rows ⊓ LinearMap.ker (tailMap n)=⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    change x=0
    ext i
    refine Fin.cases (hall x hx.1) (fun j => ?_) i
    exact congrFun hx.2 j
  have h := finrank_map_kernel (spanRows rows) (tailMap n)
  rw [hk,finrank_bot,add_zero,←spanRows_map] at h
  exact h

theorem rank_correct (n : ℕ) (rows : List (Row n)) : rank n rows=finrank Bit (spanRows rows) := by
  induction n with
  | zero =>
    have h : finrank Bit (spanRows rows)≤0 := by
      simpa [Row] using Submodule.finrank_le (spanRows rows)
    exact (Nat.eq_zero_of_le_zero h).symm
  | succ n ih =>
    unfold rank
    simp only [cacheRow_eq]
    split <;> rename_i he
    · rw [ih]
      apply zero_column_dimension
      intro x hx
      have h := List.find?_eq_none.mp he x hx
      simpa using h
    · rename_i p
      rw [ih]
      apply pivot_dimension rows p (List.mem_of_find?_eq_some he)
      have h : p 0≠0 := by simpa using List.find?_some he
      generalize hp : p 0=t at h ⊢
      fin_cases t
      · exact False.elim (h rfl)
      · rfl

theorem rank_le_columns (n : ℕ) (rows : List (Row n)) : rank n rows≤n := by
  rw [rank_correct]
  simpa [Row] using Submodule.finrank_le (spanRows rows)

theorem residual_row_count {n : ℕ} (rows : List (Row (n+1))) (p : Row (n+1)) :
    (rows.map (fun x => cacheRow (tailMap n x))).length=rows.length ∧
    (rows.map (fun x => cacheRow (clearTail p x))).length=rows.length := by simp

theorem cacheRow_array_size {n : ℕ} (x : Row n) : (Array.ofFn x).size=n := Array.size_ofFn

end QecReliability.BinaryElimination
