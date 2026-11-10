import QecReliability.CachedEvaluator

/-! A single traversal of the materialized scale counts replaces finite-set
minimum selection and repeated indexed lookup. The semantic target is exactly
`selectCached`; fallback and zero-cell conventions are unchanged. -/
namespace QecReliability.OracleCost.ScaleSelection

structure Result where
  estimate : ℕ
  comparisons : ℕ

def scan (B : ℕ) : ℕ → List (ℕ × ℕ) → Result
  | _,[] => ⟨1,0⟩
  | index,x::xs =>
    if x.1≤4*B then ⟨max 1 (2^index*x.1),1⟩ else
    let rest := scan B (index+1) xs
    ⟨rest.estimate,1+rest.comparisons⟩

theorem comparisons_le (B index : ℕ) (xs : List (ℕ × ℕ)) :
    (scan B index xs).comparisons≤xs.length := by
  induction xs generalizing index with
  | nil => simp [scan]
  | cons x xs ih =>
    have ht := ih (index+1)
    by_cases h : x.1≤4*B <;> simp only [scan,h,↓reduceIte,List.length_cons] <;> omega

theorem scan_none (B index : ℕ) (xs : List (ℕ × ℕ))
    (h : ∀ x∈xs, 4*B<x.1) : (scan B index xs).estimate=1 := by
  induction xs generalizing index with
  | nil => rfl
  | cons x xs ih =>
    have hx : ¬x.1≤4*B := by have := h x (by simp); omega
    simp only [scan,hx,↓reduceIte]
    exact ih _ (fun y hy => h y (by simp [hy]))

theorem scan_first (B index k : ℕ) (xs : List (ℕ × ℕ)) (hk : k<xs.length)
    (hyes : xs[k].1≤4*B)
    (hbefore : ∀ j (hj : j<k), 4*B<xs[j].1) :
    (scan B index xs).estimate=max 1 (2^(index+k)*xs[k].1) := by
  induction k generalizing index xs with
  | zero =>
    cases xs with
    | nil => simp at hk
    | cons x xs =>
      change x.1≤4*B at hyes
      simp [scan,hyes]
  | succ k ih =>
    cases xs with
    | nil => simp at hk
    | cons x xs =>
      have hx : ¬x.1≤4*B := by have := hbefore 0 (by omega); simpa using not_le.mpr this
      have ht := ih (index+1) xs (by simpa using hk) hyes
        (fun j hj => hbefore (j+1) (Nat.succ_lt_succ hj))
      simpa only [scan,hx,↓reduceIte,Nat.add_assoc,Nat.add_comm 1 k,List.getElem_cons_succ] using ht

def select {q : ℕ} (B : ℕ) (T : CountTable (q+1)) : Result := scan B 0 T.entries

theorem select_eq {q : ℕ} (B : ℕ) (T : CountTable (q+1)) :
    (select B T).estimate=selectCached B T := by
  unfold selectCached
  dsimp only
  split_ifs with h
  · let s := (Finset.univ.filter (fun s => (T.get s).1≤4*B)).min' h
    have hs : (T.get s).1≤4*B := by
      exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2
    have hbefore : ∀ j (hj : j<s.val), 4*B<(T.entries[j]'(by rw [T.length_eq]; exact hj.trans s.isLt)).1 := by
      intro j hj
      have hjq : j<q+1 := hj.trans s.isLt
      have hm : ¬(T.get ⟨j,hjq⟩).1≤4*B := by
        intro hc
        have hmem : (⟨j,hjq⟩:Fin (q+1))∈Finset.univ.filter (fun s => (T.get s).1≤4*B) := by
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hc
        have hle := Finset.min'_le _ _ hmem
        change s≤⟨j,hjq⟩ at hle
        have : s.val≤j := hle
        omega
      exact not_le.mp hm
    have hi := scan_first B 0 s.val T.entries (by rw [T.length_eq]; exact s.isLt) hs hbefore
    simpa only [s,select,Nat.zero_add,CountTable.get,List.get_eq_getElem] using hi
  · apply scan_none
    intro x hx
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hx
    have hjq : j.val<q+1 := by simpa only [T.length_eq] using j.isLt
    have hn : ¬(T.get ⟨j.val,hjq⟩).1≤4*B := by
      intro hc
      apply h
      exact ⟨⟨j.val,hjq⟩,by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hc⟩
    change ¬(T.entries.get j).1≤4*B at hn
    rw [hj] at hn
    omega

end QecReliability.OracleCost.ScaleSelection
