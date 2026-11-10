import ExternalSATDFSOrder
import ExternalSATOuterCandidateTraversal

/-! Order-sensitive link from the actual traversal output recurrences to the
accepted DFS enumeration. No new controller or runtime assumption is added. -/
namespace QecReliability.ExternalSATBridge.DFSOutputOrder

open OAI.Algorithms.SubexponentialSAT
open CandidateClauseEmitter (slots)

def emit (clauses : List (List ℕ)) (out : List Bool) (codes : List ℕ) : List Bool :=
  CandidateVisit.output (slots codes) clauses out

def run (clauses : List (List ℕ)) (codes : List (List ℕ)) (out : List Bool) : List Bool :=
  codes.foldl (emit clauses) out

theorem fold_map {α β σ : Type*} (f : σ → β → σ) (g : α → β)
    (xs : List α) (s : σ) :
    (xs.map g).foldl f s = xs.foldl (fun t x => f t (g x)) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simpa only [List.map_cons, List.foldl_cons] using ih (f s (g x))

theorem fold_flatMap {α β σ : Type*} (f : σ → β → σ) (g : α → List β)
    (xs : List α) (s : σ) :
    (xs.flatMap g).foldl f s = xs.foldl (fun t x => (g x).foldl f t) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, ih]

theorem fold_range_succ {σ : Type*} (f : σ → ℕ → σ) (n : ℕ) (s : σ) :
    (List.range (n + 1)).foldl f s = f ((List.range n).foldl f s) n := by
  simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem deep_fold (a b start count : ℕ) (clauses : List (List ℕ)) (out : List Bool) :
    DeepCandidateTraversal.output (Encoding.encodeNat a) (Encoding.encodeNat b)
      clauses start count out =
      run clauses ((List.range count).map (fun i => [a, b, start + i])) out := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [DeepCandidateTraversal.output, run, fold_map, fold_range_succ]
    rw [ih]
    simp only [run, fold_map, emit, slots]

theorem flatMap_singleton {α β : Type*} (xs : List α) (f : α → β) :
    xs.flatMap (fun x => [f x]) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.flatMap_cons, List.singleton_append, List.map_cons] using congrArg (List.cons (f x)) ih

theorem walk_one (a n : ℕ) :
    DFSOrder.walk 1 a n = [] :: (List.range n).map (fun i => [a + i]) := by
  simp only [DFSOrder.walk, List.map_cons, List.map_nil, flatMap_singleton]

theorem middle_visit_fold (a b r : ℕ) (clauses : List (List ℕ)) (out : List Bool) :
    MiddleCandidateTraversal.visitOutput (Encoding.encodeNat a) clauses b r out =
      run clauses ((DFSOrder.walk 1 (b + 1) r).map (fun cs => a :: b :: cs)) out := by
  simpa only [MiddleCandidateTraversal.visitOutput, walk_one, List.map_cons,
    List.map_map, Function.comp_def, run, List.foldl_cons, emit, slots] using
    deep_fold a b (b + 1) r clauses (emit clauses out [a, b])

theorem middle_fold (a start total count : ℕ) (clauses : List (List ℕ)) (out : List Bool) :
    MiddleCandidateTraversal.output (Encoding.encodeNat a) clauses start total count out =
      (List.range count).foldl
        (fun acc i => run clauses
          ((DFSOrder.walk 1 (start + i + 1) (total - 1 - i)).map
            (fun cs => a :: (start + i) :: cs)) acc) out := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [MiddleCandidateTraversal.output, fold_range_succ, ih, middle_visit_fold]

theorem middle_tree (a start total : ℕ) (clauses : List (List ℕ)) (out : List Bool) :
    MiddleCandidateTraversal.output (Encoding.encodeNat a) clauses start total total
      (emit clauses out [a]) =
      run clauses ((DFSOrder.walk 2 start total).map (List.cons a)) out := by
  rw [DFSOrder.walk_succ]
  simp only [List.map_cons, run, List.foldl_cons, List.map_flatMap]
  rw [fold_flatMap, middle_fold]
  apply congrArg (fun f => (List.range total).foldl f (emit clauses out [a]))
  funext acc i
  simp only [run, List.map_map, Function.comp_def]

theorem outer_visit_fold (a r : ℕ) (clauses : List (List ℕ)) (out : List Bool) :
    OuterCandidateTraversal.visitOutput clauses a r out =
      run clauses ((DFSOrder.walk 2 (a + 1) r).map (List.cons a)) out := by
  exact middle_tree a (a + 1) r clauses out

theorem outer_fold (start total count : ℕ) (clauses : List (List ℕ)) (out : List Bool) :
    OuterCandidateTraversal.output clauses start total count out =
      (List.range count).foldl
        (fun acc i => run clauses
          ((DFSOrder.walk 2 (start + i + 1) (total - 1 - i)).map
            (List.cons (start + i))) acc) out := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [OuterCandidateTraversal.output, fold_range_succ, ih, outer_visit_fold]

/-- The root visit is real and occurs exactly once, including when upper=0. -/
theorem root_output (upper : ℕ) (clauses : List (List ℕ)) (out : List Bool) :
    OuterCandidateTraversal.output clauses 0 upper upper
      (CandidateVisit.output (slots []) clauses out) =
      run clauses (DFSOrder.walk 3 0 upper) out := by
  rw [DFSOrder.root_unfold]
  simp only [run, List.foldl_cons, fold_flatMap]
  rw [outer_fold]
  simp only [Nat.zero_add, run, emit]

theorem canonical_output_order (upper : ℕ) (clauses : List (List ℕ)) (out : List Bool) :
    OuterCandidateTraversal.output clauses 0 upper upper
      (CandidateVisit.output (slots []) clauses out) =
      run clauses (CanonicalEnumeration.candidates 3 0 upper) out := by
  rw [← DFSOrder.root_order]
  exact root_output upper clauses out

end QecReliability.ExternalSATBridge.DFSOutputOrder
