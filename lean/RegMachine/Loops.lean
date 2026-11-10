import Mathlib.Tactic.Ring
import RegMachine.Abstract

/-!
# Generic actions and loop lemmas

Gadget transitions only touch one or two tapes: every other tape is rewritten with
its own head symbol and stays (`moves1`, `moves2`, writes `Function.update heads i x`).
The `astep_*` lemmas compute such steps on abstract configurations, and the `run_*`
lemmas are the generic loops all gadgets are built from (each by induction on the
number of iterations, with explicit window obligations):

* `run_scanR` / `run_scanL`: move over cells satisfying `cont`, contents unchanged;
* `run_mapL`: rewrite each cell `x` to `f x` while moving left;
* `run_shiftL`: shift contents one cell to the right-to-left with a carry label;
* `run_copyR`: read tape `j`, write tape `i`, move both right.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape Turing Function

section Moves
variable {k : ℕ}

/-- Move only tape `i` by `m`. -/
def moves1 (i : Fin (k + 1)) (m : Move) : Fin (k + 1) → Move := update (fun _ => Move.stay) i m

/-- Move tape `i` by `m` and tape `j` by `m'`. -/
def moves2 (i : Fin (k + 1)) (m : Move) (j : Fin (k + 1)) (m' : Move) : Fin (k + 1) → Move :=
  update (moves1 i m) j m'

theorem pos_moves1 (P : Fin (k + 1) → ℤ) (i : Fin (k + 1)) (m : Move) :
    (fun j => P j + (moves1 i m j).delta) = update P i (P i + m.delta) := by
  funext j
  by_cases h : j = i
  · subst h; simp [moves1]
  · simp [moves1, h, Move.delta]

theorem pos_moves2 (P : Fin (k + 1) → ℤ) {i j : Fin (k + 1)} (hij : i ≠ j) (m m' : Move) :
    (fun t => P t + (moves2 i m j m' t).delta) =
      update (update P i (P i + m.delta)) j (P j + m'.delta) := by
  funext t
  by_cases ht : t = j
  · subst ht; simp [moves2]
  · by_cases hti : t = i
    · subst hti; simp [moves2, moves1, ht]
    · simp [moves2, moves1, ht, hti, Move.delta]

end Moves

section Steps
variable {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]

theorem cont_self (a : ACfg k Γ Λ) :
    (fun i => update (a.C i) (a.P i) (a.heads i)) = a.C := by
  funext i; simp

theorem cont_write1 (a : ACfg k Γ Λ) (i : Fin (k + 1)) (x : Γ) :
    (fun j => update (a.C j) (a.P j) (update a.heads i x j)) =
      update a.C i (update (a.C i) (a.P i) x) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

variable {M : Machine k Γ Λ} {a : ACfg k Γ Λ} {q : Λ}

theorem astep_move1 {i : Fin (k + 1)} {m : Move}
    (h : M.transition a.label a.heads = .advance q a.heads (moves1 i m)) :
    astep M a = some ⟨q, a.C, update a.P i (a.P i + m.delta)⟩ := by
  rw [astep_of_advance h, cont_self, pos_moves1]

theorem astep_write1 {i : Fin (k + 1)} {x : Γ} {m : Move}
    (h : M.transition a.label a.heads = .advance q (update a.heads i x) (moves1 i m)) :
    astep M a = some ⟨q, update a.C i (update (a.C i) (a.P i) x), update a.P i (a.P i + m.delta)⟩ := by
  rw [astep_of_advance h, cont_write1, pos_moves1]

theorem astep_move2 {i j : Fin (k + 1)} (hij : i ≠ j) {m m' : Move}
    (h : M.transition a.label a.heads = .advance q a.heads (moves2 i m j m')) :
    astep M a = some ⟨q, a.C, update (update a.P i (a.P i + m.delta)) j (a.P j + m'.delta)⟩ := by
  rw [astep_of_advance h, cont_self, pos_moves2 _ hij]

theorem astep_write1_move2 {i j : Fin (k + 1)} (hij : i ≠ j) {x : Γ} {m m' : Move}
    (h : M.transition a.label a.heads = .advance q (update a.heads i x) (moves2 i m j m')) :
    astep M a = some ⟨q, update a.C i (update (a.C i) (a.P i) x),
      update (update a.P i (a.P i + m.delta)) j (a.P j + m'.delta)⟩ := by
  rw [astep_of_advance h, cont_write1, pos_moves2 _ hij]

/-- A single non-moving relabel step (rewrite every head with itself, stay). -/
theorem astep_stay {M : Machine k Γ Λ} {a : ACfg k Γ Λ} {q : Λ}
    (h : M.transition a.label a.heads = .advance q a.heads (fun _ => .stay)) :
    astep M a = some ⟨q, a.C, a.P⟩ := by
  rw [astep_of_advance h, cont_self]
  congr
  funext i
  simp [Move.delta]

end Steps

/-! ## Loops -/

section Loops
variable {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
variable {M : Machine k Γ Λ} {W : Fin (k + 1) → Set ℤ}

theorem update_update_self (P : Fin (k + 1) → ℤ) (i : Fin (k + 1)) (u v : ℤ) :
    update (update P i u) i v = update P i v := update_idem _ _ _

/-- Scan right over cells satisfying `cont`. -/
theorem run_scanR {q : Λ} {i : Fin (k + 1)} (cont : Γ → Prop)
    (htr : ∀ heads : Fin (k + 1) → Γ, cont (heads i) →
      M.transition q heads = .advance q heads (moves1 i .right)) :
    ∀ (n : ℕ) (C : Fin (k + 1) → ℤ → Γ) (P : Fin (k + 1) → ℤ),
      (∀ t : ℕ, t < n → cont (C i (P i + t))) → InW W P → (∀ t : ℕ, t ≤ n → P i + t ∈ W i) →
      ARun M W ⟨q, C, P⟩ n ⟨q, C, update P i (P i + n)⟩ := by
  intro n
  induction n with
  | zero =>
    intro C P _ hP _
    have e : update P i (P i + ((0 : ℕ) : ℤ)) = P := by simp
    rw [e]; exact .nil hP
  | succ n ih =>
    intro C P hc hP hr
    have hc0 : cont ((⟨q, C, P⟩ : ACfg k Γ Λ).heads i) := by
      simpa using hc 0 (by omega)
    have hs : astep M ⟨q, C, P⟩ = some ⟨q, C, update P i (P i + 1)⟩ := by
      simpa [Move.delta] using astep_move1 (M := M) (a := ⟨q, C, P⟩) (htr _ hc0)
    have hrun := ih C (update P i (P i + 1))
      (fun t ht => by
        have e : update P i (P i + 1) i + (t : ℤ) = P i + ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e]; exact hc (t + 1) (by omega))
      (hP.update (by simpa using hr 1 (by omega)))
      (fun t ht => by
        have e : update P i (P i + 1) i + (t : ℤ) = P i + ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e]; exact hr (t + 1) (by omega))
    refine ARun.cons hs hP (hrun.of_eq (ACfg.ext rfl rfl ?_))
    simp only [update_self, update_idem]
    refine congrArg (update P i) ?_
    push_cast; ring

/-- Scan left over cells satisfying `cont`. -/
theorem run_scanL {q : Λ} {i : Fin (k + 1)} (cont : Γ → Prop)
    (htr : ∀ heads : Fin (k + 1) → Γ, cont (heads i) →
      M.transition q heads = .advance q heads (moves1 i .left)) :
    ∀ (n : ℕ) (C : Fin (k + 1) → ℤ → Γ) (P : Fin (k + 1) → ℤ),
      (∀ t : ℕ, t < n → cont (C i (P i - t))) → InW W P → (∀ t : ℕ, t ≤ n → P i - t ∈ W i) →
      ARun M W ⟨q, C, P⟩ n ⟨q, C, update P i (P i - n)⟩ := by
  intro n
  induction n with
  | zero =>
    intro C P _ hP _
    have e : update P i (P i - ((0 : ℕ) : ℤ)) = P := by simp
    rw [e]; exact .nil hP
  | succ n ih =>
    intro C P hc hP hr
    have hc0 : cont ((⟨q, C, P⟩ : ACfg k Γ Λ).heads i) := by
      simpa using hc 0 (by omega)
    have hs : astep M ⟨q, C, P⟩ = some ⟨q, C, update P i (P i - 1)⟩ := by
      simpa [Move.delta, sub_eq_add_neg] using astep_move1 (M := M) (a := ⟨q, C, P⟩) (htr _ hc0)
    have hrun := ih C (update P i (P i - 1))
      (fun t ht => by
        have e : update P i (P i - 1) i - (t : ℤ) = P i - ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e]; exact hc (t + 1) (by omega))
      (hP.update (by simpa using hr 1 (by omega)))
      (fun t ht => by
        have e : update P i (P i - 1) i - (t : ℤ) = P i - ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e]; exact hr (t + 1) (by omega))
    refine ARun.cons hs hP (hrun.of_eq (ACfg.ext rfl rfl ?_))
    simp only [update_self, update_idem]
    refine congrArg (update P i) ?_
    push_cast; ring

/-- Rewrite cells `x ↦ f x` while moving left over cells satisfying `cont`. -/
theorem run_mapL {q : Λ} {i : Fin (k + 1)} (cont : Γ → Prop) (f : Γ → Γ)
    (htr : ∀ heads : Fin (k + 1) → Γ, cont (heads i) →
      M.transition q heads = .advance q (update heads i (f (heads i))) (moves1 i .left)) :
    ∀ (n : ℕ) (C : Fin (k + 1) → ℤ → Γ) (P : Fin (k + 1) → ℤ),
      (∀ t : ℕ, t < n → cont (C i (P i - t))) → InW W P → (∀ t : ℕ, t ≤ n → P i - t ∈ W i) →
      ARun M W ⟨q, C, P⟩ n
        ⟨q, update C i (fun z => if P i - n < z ∧ z ≤ P i then f (C i z) else C i z),
          update P i (P i - n)⟩ := by
  intro n
  induction n with
  | zero =>
    intro C P _ hP _
    have e1 : update P i (P i - ((0 : ℕ) : ℤ)) = P := by simp
    have e2 : update C i (fun z => if P i - ((0 : ℕ) : ℤ) < z ∧ z ≤ P i then f (C i z) else C i z)
        = C := by
      have : (fun z => if P i - ((0 : ℕ) : ℤ) < z ∧ z ≤ P i then f (C i z) else C i z) = C i := by
        funext z; rw [if_neg (by omega)]
      rw [this]; simp
    rw [e1, e2]; exact .nil hP
  | succ n ih =>
    intro C P hc hP hr
    have hc0 : cont ((⟨q, C, P⟩ : ACfg k Γ Λ).heads i) := by
      simpa using hc 0 (by omega)
    have hs : astep M ⟨q, C, P⟩ =
        some ⟨q, update C i (update (C i) (P i) (f (C i (P i)))), update P i (P i - 1)⟩ := by
      simpa [Move.delta, sub_eq_add_neg] using astep_write1 (M := M) (a := ⟨q, C, P⟩) (htr _ hc0)
    have hrun := ih (update C i (update (C i) (P i) (f (C i (P i))))) (update P i (P i - 1))
      (fun t ht => by
        have e : update P i (P i - 1) i - (t : ℤ) = P i - ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e, update_self, update_of_ne (by omega)]; exact hc (t + 1) (by omega))
      (hP.update (by simpa using hr 1 (by omega)))
      (fun t ht => by
        have e : update P i (P i - 1) i - (t : ℤ) = P i - ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e]; exact hr (t + 1) (by omega))
    refine ARun.cons hs hP (hrun.of_eq (ACfg.ext rfl ?_ ?_))
    · simp only [update_self, update_idem]
      refine congrArg (update C i) (funext fun z => ?_)
      by_cases hz : z = P i
      · subst hz
        rw [if_neg (by omega), if_pos (by push_cast; omega), update_self]
      · rw [update_of_ne hz]
        by_cases hin : P i - 1 - n < z ∧ z ≤ P i - 1
        · rw [if_pos hin, if_pos (by push_cast; omega)]
        · rw [if_neg hin, if_neg (by push_cast; omega)]
    · simp only [update_self, update_idem]
      refine congrArg (update P i) ?_
      push_cast; ring

/-- Right-to-left shift with a carry: the cell at the head receives the carried bit
and the old head bit becomes the new carry. -/
theorem run_shiftL [RegSyms Γ] {q : Option Bool → Λ} {i : Fin (k + 1)} (cont : Γ → Prop)
    (htr : ∀ (c : Option Bool) (heads : Fin (k + 1) → Γ), cont (heads i) →
      M.transition (q c) heads =
        .advance (q (RegSyms.dec (heads i))) (update heads i (optSym c)) (moves1 i .left)) :
    ∀ (n : ℕ) (c : Option Bool) (C : Fin (k + 1) → ℤ → Γ) (P : Fin (k + 1) → ℤ),
      (∀ t : ℕ, t < n → cont (C i (P i - t))) → InW W P → (∀ t : ℕ, t ≤ n → P i - t ∈ W i) →
      ∃ c', ARun M W ⟨q c, C, P⟩ n
        ⟨q c', update C i (fun z => if P i - n < z ∧ z ≤ P i then
            (if z = P i then optSym c else optSym (RegSyms.dec (C i (z + 1)))) else C i z),
          update P i (P i - n)⟩ := by
  intro n
  induction n with
  | zero =>
    intro c C P _ hP _
    refine ⟨c, ?_⟩
    have e1 : update P i (P i - ((0 : ℕ) : ℤ)) = P := by simp
    have e2 : update C i (fun z => if P i - ((0 : ℕ) : ℤ) < z ∧ z ≤ P i then
        (if z = P i then optSym c else optSym (RegSyms.dec (C i (z + 1)))) else C i z) = C := by
      have : (fun z => if P i - ((0 : ℕ) : ℤ) < z ∧ z ≤ P i then
          (if z = P i then optSym c else optSym (RegSyms.dec (C i (z + 1)))) else C i z) = C i := by
        funext z; rw [if_neg (by omega)]
      rw [this]; simp
    rw [e1, e2]; exact .nil hP
  | succ n ih =>
    intro c C P hc hP hr
    have hc0 : cont ((⟨q c, C, P⟩ : ACfg k Γ Λ).heads i) := by
      simpa using hc 0 (by omega)
    have hs : astep M ⟨q c, C, P⟩ =
        some ⟨q (RegSyms.dec (C i (P i))), update C i (update (C i) (P i) (optSym c)),
          update P i (P i - 1)⟩ := by
      simpa [Move.delta, sub_eq_add_neg] using astep_write1 (M := M) (a := ⟨q c, C, P⟩) (htr _ _ hc0)
    obtain ⟨c', hrun⟩ := ih (RegSyms.dec (C i (P i))) (update C i (update (C i) (P i) (optSym c)))
      (update P i (P i - 1))
      (fun t ht => by
        have e : update P i (P i - 1) i - (t : ℤ) = P i - ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e, update_self, update_of_ne (by omega)]; exact hc (t + 1) (by omega))
      (hP.update (by simpa using hr 1 (by omega)))
      (fun t ht => by
        have e : update P i (P i - 1) i - (t : ℤ) = P i - ((t + 1 : ℕ) : ℤ) := by
          simp only [update_self]; push_cast; ring
        rw [e]; exact hr (t + 1) (by omega))
    refine ⟨c', ARun.cons hs hP (hrun.of_eq (ACfg.ext rfl ?_ ?_))⟩
    · simp only [update_self, update_idem]
      refine congrArg (update C i) (funext fun z => ?_)
      by_cases hz : z = P i
      · subst hz
        rw [if_neg (by omega), if_pos (by push_cast; omega), if_pos rfl, update_self]
      · rw [update_of_ne hz]
        by_cases hin : P i - 1 - n < z ∧ z ≤ P i - 1
        · rw [if_pos hin, if_pos (show P i - ((n + 1 : ℕ) : ℤ) < z ∧ z ≤ P i by push_cast; omega),
            if_neg hz]
          by_cases hz1 : z = P i - 1
          · rw [if_pos hz1]
            subst hz1
            rw [sub_add_cancel]
          · rw [if_neg hz1, update_of_ne (show z + 1 ≠ P i by omega)]
        · rw [if_neg hin,
            if_neg (show ¬ (P i - ((n + 1 : ℕ) : ℤ) < z ∧ z ≤ P i) by push_cast; omega)]
    · simp only [update_self, update_idem]
      refine congrArg (update P i) ?_
      push_cast; ring

/-- Copy loop: read tape `j`, write `g (src) (old dst)` on tape `i`, move both right. -/
theorem run_copyR {q : Λ} {i j : Fin (k + 1)} (hij : i ≠ j) (cont : Γ → Prop) (g : Γ → Γ → Γ)
    (htr : ∀ heads : Fin (k + 1) → Γ, cont (heads j) →
      M.transition q heads =
        .advance q (update heads i (g (heads j) (heads i))) (moves2 i .right j .right)) :
    ∀ (n : ℕ) (C : Fin (k + 1) → ℤ → Γ) (P : Fin (k + 1) → ℤ),
      (∀ t : ℕ, t < n → cont (C j (P j + t))) → InW W P →
      (∀ t : ℕ, t ≤ n → P i + t ∈ W i) → (∀ t : ℕ, t ≤ n → P j + t ∈ W j) →
      ARun M W ⟨q, C, P⟩ n
        ⟨q, update C i (fun z => if P i ≤ z ∧ z < P i + n then g (C j (z - P i + P j)) (C i z)
            else C i z),
          update (update P i (P i + n)) j (P j + n)⟩ := by
  have hji : j ≠ i := fun h => hij h.symm
  intro n
  induction n with
  | zero =>
    intro C P _ hP _ _
    have e1 : update (update P i (P i + ((0 : ℕ) : ℤ))) j (P j + ((0 : ℕ) : ℤ)) = P := by simp
    have e2 : update C i (fun z => if P i ≤ z ∧ z < P i + ((0 : ℕ) : ℤ) then
        g (C j (z - P i + P j)) (C i z) else C i z) = C := by
      have : (fun z => if P i ≤ z ∧ z < P i + ((0 : ℕ) : ℤ) then
          g (C j (z - P i + P j)) (C i z) else C i z) = C i := by
        funext z; rw [if_neg (by omega)]
      rw [this]; simp
    rw [e1, e2]; exact .nil hP
  | succ n ih =>
    intro C P hc hP hri hrj
    have hc0 : cont ((⟨q, C, P⟩ : ACfg k Γ Λ).heads j) := by
      simpa using hc 0 (by omega)
    have hs : astep M ⟨q, C, P⟩ =
        some ⟨q, update C i (update (C i) (P i) (g (C j (P j)) (C i (P i)))),
          update (update P i (P i + 1)) j (P j + 1)⟩ := by
      simpa [Move.delta] using
        astep_write1_move2 (M := M) (a := ⟨q, C, P⟩) hij (htr _ hc0)
    have hPi : update (update P i (P i + 1)) j (P j + 1) i = P i + 1 := by
      rw [update_of_ne hij, update_self]
    have hPj : update (update P i (P i + 1)) j (P j + 1) j = P j + 1 := by
      rw [update_self]
    have hCj : update C i (update (C i) (P i) (g (C j (P j)) (C i (P i)))) j = C j := by
      rw [update_of_ne hji]
    have hrun := ih (update C i (update (C i) (P i) (g (C j (P j)) (C i (P i)))))
      (update (update P i (P i + 1)) j (P j + 1))
      (fun t ht => by
        rw [hCj, hPj]
        have e : P j + 1 + (t : ℤ) = P j + ((t + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e]; exact hc (t + 1) (by omega))
      ((hP.update (by simpa using hri 1 (by omega))).update
        (by simpa using hrj 1 (by omega)))
      (fun t ht => by
        rw [hPi]
        have e : P i + 1 + (t : ℤ) = P i + ((t + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e]; exact hri (t + 1) (by omega))
      (fun t ht => by
        rw [hPj]
        have e : P j + 1 + (t : ℤ) = P j + ((t + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e]; exact hrj (t + 1) (by omega))
    refine ARun.cons hs hP (hrun.of_eq (ACfg.ext rfl ?_ ?_))
    · dsimp only
      simp only [hPi, hPj, hCj, update_self, update_idem]
      refine congrArg (update C i) (funext fun z => ?_)
      by_cases hz : z = P i
      · subst hz
        rw [if_neg (by omega), if_pos (by push_cast; omega)]
        simp only [update_self]
        rw [show P i - P i + P j = P j by ring]
      · rw [update_of_ne hz]
        by_cases hin : P i + 1 ≤ z ∧ z < P i + 1 + n
        · rw [if_pos hin, if_pos (by push_cast; omega)]
          rw [show z - (P i + 1) + (P j + 1) = z - P i + P j by ring]
        · rw [if_neg hin, if_neg (by push_cast; omega)]
    · dsimp only
      funext t
      by_cases htj : t = j
      · subst htj
        simp only [update_self]
        push_cast; ring
      · by_cases hti : t = i
        · subst hti
          simp only [update_self, update_of_ne htj]
          push_cast; ring
        · simp only [update_of_ne htj, update_of_ne hti]

end Loops

end QecReliability.RegMachine
