import ExternalSATCanonicalEnumeration

/-! Exact visit order for the residual-counter depth-first traversal.
This is an order theorem for the controller's recursion, not a runtime claim. -/
namespace QecReliability.ExternalSATBridge.DFSOrder

/-- Visit the current prefix first, then each increasing next code. The
remaining counter after choosing offset i is n-1-i, exactly as in the loops. -/
def walk : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | k + 1, a, n => [] :: (List.range n).flatMap
      (fun i => (walk k (a + i + 1) (n - 1 - i)).map (List.cons (a + i)))

theorem walk_succ (k a n : ℕ) :
    walk (k + 1) a n = [] :: (List.range n).flatMap
      (fun i => (walk k (a + i + 1) (n - 1 - i)).map (List.cons (a + i))) := rfl

theorem mem_cons_walk (k a n b : ℕ) (bs : List ℕ) :
    b :: bs ∈ walk (k + 1) a n ↔
      ∃ i, i < n ∧ b = a + i ∧ bs ∈ walk k (a + i + 1) (n - 1 - i) := by
  simp [walk, and_assoc, and_left_comm, and_comm, eq_comm]

theorem child_upper (a n i : ℕ) (hi : i < n) :
    a + i + 1 + (n - 1 - i) = a + n := by omega

theorem mem_walk (k a n : ℕ) (c : List ℕ) :
    c ∈ walk k a n ↔ c.length ≤ k ∧ c.Pairwise (· < ·) ∧
      ∀ b ∈ c, a ≤ b ∧ b < a + n := by
  induction k generalizing a n c with
  | zero => cases c <;> simp [walk]
  | succ k ih =>
    cases c with
    | nil => simp [walk]
    | cons b bs =>
      rw [mem_cons_walk]
      constructor
      · rintro ⟨i, hi, rfl, ht⟩
        obtain ⟨hlen, hp, hb⟩ := (ih (a + i + 1) (n - 1 - i) bs).mp ht
        have hu := child_upper a n i hi
        refine ⟨by simpa using Nat.succ_le_succ hlen,
          List.pairwise_cons.mpr ⟨?_, hp⟩, ?_⟩
        · intro x hx
          have := (hb x hx).1
          omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨by omega, by omega⟩
          · have := hb x hx
            exact ⟨by omega, by omega⟩
      · rintro ⟨hlen, hp, hb⟩
        have hhead := hb b (by simp)
        obtain ⟨hgreater, htail⟩ := List.pairwise_cons.mp hp
        have hi : b - a < n := by omega
        have hcode : b = a + (b - a) := by omega
        refine ⟨b - a, hi, hcode, (ih _ _ _).mpr ?_⟩
        refine ⟨by simpa using hlen, htail, ?_⟩
        intro x hx
        have hxbound := hb x (by simp [hx])
        have hxgreater := hgreater x hx
        have hu := child_upper a n (b - a) hi
        exact ⟨by omega, by omega⟩

theorem walk_sorted (k a n : ℕ) : (walk k a n).Pairwise (· < ·) := by
  induction k generalizing a n with
  | zero => simp [walk]
  | succ k ih =>
    rw [walk, List.pairwise_cons]
    constructor
    · intro c hc
      obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hc
      exact List.Lex.nil
    · apply List.pairwise_flatMap.mpr
      constructor
      · intro i hi
        exact (ih (a + i + 1) (n - 1 - i)).map (List.cons (a + i))
          (fun _ _ h => List.Lex.cons h)
      · apply List.pairwise_lt_range.imp
        intro i j hij x hx y hy
        obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hx
        obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hy
        exact List.Lex.rel (by omega)

/-- Equality is order-sensitive, not merely equality of visited sets. Prefixes
precede descendants; neither tautologies nor the empty candidate are pruned. -/
theorem walk_eq_candidates (k a n : ℕ) :
    walk k a n = CanonicalEnumeration.candidates k a (a + n) := by
  apply List.SortedLT.eq_of_mem_iff (walk_sorted k a n).sortedLT
    (CanonicalEnumeration.candidates_sorted k a (a + n)).sortedLT
  intro c
  rw [mem_walk, CanonicalEnumeration.mem_candidates]

theorem walk_zero_remaining (k a : ℕ) : walk k a 0 = [[]] := by
  cases k <;> simp [walk]

/-- Root, singleton, pair, and triple visits have exactly the accepted canonical
width-three enumeration order. -/
theorem root_order (upper : ℕ) :
    walk 3 0 upper = CanonicalEnumeration.candidates 3 0 upper := by
  simpa only [Nat.zero_add] using walk_eq_candidates 3 0 upper

/-- Useful directly when unfolding the nested finite controllers. -/
theorem root_unfold (upper : ℕ) :
    walk 3 0 upper = [] :: (List.range upper).flatMap (fun a =>
      (walk 2 (a + 1) (upper - 1 - a)).map (List.cons a)) := by
  simp only [walk, Nat.zero_add]

end QecReliability.ExternalSATBridge.DFSOrder
