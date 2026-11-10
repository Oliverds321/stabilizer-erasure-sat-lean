import OracleCost.CachedBatch

/-! A concrete insertion-sort refinement of the tuple median. It preserves
multiplicity. Comparisons and newly constructed list cells are counted in the
same recursion. Cell counts are a source-level allocation measure, not native
heap bytes; an arena/pointer representation remains a separate refinement.
-/
namespace QecReliability.OracleCost.MedianSort

structure Result where
  values : List ℕ
  comparisons : ℕ
  allocations : ℕ

def insert (x : ℕ) (xs : List ℕ) : Result :=
  match xs with
  | [] => ⟨[x],0,1⟩
  | y::ys =>
    if x≤y then ⟨x::xs,1,1⟩ else
    let rest := insert x ys
    ⟨y::rest.values,1+rest.comparisons,1+rest.allocations⟩

def sort : List ℕ → Result
  | [] => ⟨[],0,0⟩
  | x::xs =>
    let rest := sort xs
    let here := insert x rest.values
    ⟨here.values,rest.comparisons+here.comparisons,rest.allocations+here.allocations⟩

theorem insert_values (x : ℕ) (xs : List ℕ) :
    (insert x xs).values=List.orderedInsert (·≤·) x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => by_cases h : x≤y <;> simp [insert,List.orderedInsert,h,ih]

theorem sort_values (xs : List ℕ) : (sort xs).values=xs.insertionSort (·≤·) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [sort,List.insertionSort_cons,insert_values] using congrArg (List.orderedInsert (·≤·) x) ih

@[simp] theorem sort_length (xs : List ℕ) : (sort xs).values.length=xs.length := by
  rw [sort_values,List.length_insertionSort]

theorem sort_perm (xs : List ℕ) : (sort xs).values.Perm xs := by
  rw [sort_values]
  exact List.perm_insertionSort _ _

theorem insert_cost (x : ℕ) (xs : List ℕ) :
    (insert x xs).comparisons≤xs.length ∧ (insert x xs).allocations≤xs.length+1 := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
    by_cases h : x≤y <;> simp only [insert,h,↓reduceIte,List.length_cons] <;> omega

theorem sort_cost (xs : List ℕ) :
    (sort xs).comparisons≤xs.length^2 ∧ (sort xs).allocations≤xs.length^2+xs.length := by
  induction xs with
  | nil => simp [sort]
  | cons x xs ih =>
    have hi := insert_cost x (sort xs).values
    rw [sort_length] at hi
    simp only [sort,List.length_cons]
    constructor <;> nlinarith [ih.1,ih.2,hi.1,hi.2]

/-- No value, including a duplicate estimate, is deleted or introduced. -/
theorem sort_count (xs : List ℕ) (value : ℕ) :
    (sort xs).values.count value=xs.count value := (sort_perm xs).count_eq value

theorem sort_bounded (xs : List ℕ) (bound : ℕ) (h : ∀ value∈xs, value≤bound) :
    ∀ value∈(sort xs).values, value≤bound := by
  intro value hv
  exact h value ((sort_perm xs).mem_iff.mp hv)

theorem sorted_tuple (n : ℕ) (X : Fin n → ℕ) :
    (sort (List.ofFn X)).values=List.ofFn (X ∘ Tuple.sort X) := by
  apply List.Perm.eq_of_sortedLE
  · rw [sort_values]
    exact List.sortedLE_insertionSort (l := List.ofFn X)
  · exact (Tuple.monotone_sort X).sortedLE_ofFn
  · exact (sort_perm _).trans ((Tuple.sort X).ofFn_comp_perm X).symm

def median {m : ℕ} (X : Fin (2*m+1) → ℕ) : ℕ :=
  let result := sort (List.ofFn X)
  result.values.get ⟨m,by simp [result]; omega⟩

theorem median_eq {m : ℕ} (X : Fin (2*m+1) → ℕ) : median X=oddNatMedian X := by
  have h := congrArg (fun xs : List ℕ => xs[m]?) (sorted_tuple (2*m+1) X)
  have hm : m<2*m+1 := by omega
  have hlen : m<(sort (List.ofFn X)).values.length := by
    rw [sort_length,List.length_ofFn]
    exact hm
  simp only [List.getElem?_eq_getElem hlen,List.getElem?_ofFn,hm,↓reduceDIte,
    Function.comp_apply] at h
  exact Option.some.inj h

/-- A sequential list lookup can replace the opaque tuple sort with exactly
the same median; no decision-oracle call is made by this postprocessing. -/
def cachedMedian {Ω A : Type*} [Fintype Ω] {q : ℕ} {e : A ≃ BitModels q}
    {H : HashStages Ω A q} {S : Finset A} (D : DecisionQueries e H S)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) : ℕ × ℕ :=
  let table := CountTable.build (fun i => D.cachedTrial B (ω i))
  (median (fun i => (table.get i).1),table.calls)

theorem cachedMedian_eq {Ω A : Type*} [Fintype Ω] {q : ℕ} {e : A ≃ BitModels q}
    {H : HashStages Ω A q} {S : Finset A} (D : DecisionQueries e H S)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    cachedMedian D B m ω=D.cachedMedian B m ω := by
  simp only [cachedMedian,DecisionQueries.cachedMedian,median_eq]

end QecReliability.OracleCost.MedianSort
