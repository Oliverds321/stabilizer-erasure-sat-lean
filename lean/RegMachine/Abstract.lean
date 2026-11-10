import OracleCost.MachineObservations
import OracleCost.TraceDisplacementCandidate
import RegMachine.Encoding
import Mathlib.Data.Int.Interval

/-!
# Abstract configurations and windowed runs

An `ACfg` describes a configuration of a `MultiTape.Machine` by *absolute* tape
contents `C i : ℤ → Γ` and *absolute* head positions `P i : ℤ`. `astep` is the
machine's transition read through this description; `Rep s a` says that the
concrete configuration `s` has exactly these contents relative to its heads.

`ARun M W a n b`: `n` abstract steps from `a` to `b`, every visited configuration
having all head positions inside the window `W i` on each tape `i`.
`ARun.observe` turns such a run into an actual observed `Trace` whose visited sets
stay inside `W`; this is the single place where space is accounted.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape Turing

/-- Abstract configuration: control label, absolute contents, absolute heads. -/
@[ext] structure ACfg (k : ℕ) (Γ Λ : Type) where
  label : Λ
  C : Fin (k + 1) → ℤ → Γ
  P : Fin (k + 1) → ℤ

section Defs
variable {k : ℕ} {Γ Λ : Type}

/-- The symbols under the heads. -/
def ACfg.heads (a : ACfg k Γ Λ) : Fin (k + 1) → Γ := fun i => a.C i (a.P i)

@[simp] theorem ACfg.heads_apply (a : ACfg k Γ Λ) (i : Fin (k + 1)) : a.heads i = a.C i (a.P i) :=
  rfl

/-- All heads lie in the window. -/
def InW (W : Fin (k + 1) → Set ℤ) (P : Fin (k + 1) → ℤ) : Prop := ∀ i, P i ∈ W i

theorem InW.update {W : Fin (k + 1) → Set ℤ} {P : Fin (k + 1) → ℤ} (h : InW W P)
    {i : Fin (k + 1)} {v : ℤ} (hv : v ∈ W i) : InW W (Function.update P i v) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hv
  · simpa [Function.update_of_ne hj] using h j

end Defs

section Machine
variable {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]

/-- One transition, read through the abstract description. -/
def astep (M : Machine k Γ Λ) (a : ACfg k Γ Λ) : Option (ACfg k Γ Λ) :=
  match M.transition a.label a.heads with
  | .halt _ => none
  | .advance q w mv =>
      some ⟨q, fun i => Function.update (a.C i) (a.P i) (w i), fun i => a.P i + (mv i).delta⟩

/-- Halting answer, read through the abstract description. -/
def aanswer (M : Machine k Γ Λ) (a : ACfg k Γ Λ) : Option Bool :=
  match M.transition a.label a.heads with
  | .halt b => some b
  | .advance _ _ _ => none

theorem astep_of_advance {M : Machine k Γ Λ} {a : ACfg k Γ Λ} {q : Λ}
    {w : Fin (k + 1) → Γ} {mv : Fin (k + 1) → Move}
    (h : M.transition a.label a.heads = .advance q w mv) :
    astep M a = some ⟨q, fun i => Function.update (a.C i) (a.P i) (w i),
      fun i => a.P i + (mv i).delta⟩ := by
  unfold astep; rw [h]

theorem aanswer_of_halt {M : Machine k Γ Λ} {a : ACfg k Γ Λ} {b : Bool}
    (h : M.transition a.label a.heads = .halt b) : aanswer M a = some b := by
  unfold aanswer; rw [h]

theorem astep_eq_some {M : Machine k Γ Λ} {a a' : ACfg k Γ Λ} (h : astep M a = some a') :
    ∃ q w mv, M.transition a.label a.heads = .advance q w mv ∧
      a' = ⟨q, fun i => Function.update (a.C i) (a.P i) (w i), fun i => a.P i + (mv i).delta⟩ := by
  unfold astep at h
  cases htr : M.transition a.label a.heads with
  | halt b => rw [htr] at h; cases h
  | advance q w mv =>
    rw [htr] at h
    exact ⟨q, w, mv, rfl, (Option.some.inj h).symm⟩

/-! ### Concrete representation -/

/-- `s` is the concrete configuration described by `a`. -/
def Rep (s : Config k Γ Λ) (a : ACfg k Γ Λ) : Prop :=
  s.label = a.label ∧ ∀ i (z : ℤ), (s.tapes i).nth z = a.C i (a.P i + z)

theorem Rep.heads {s : Config k Γ Λ} {a : ACfg k Γ Λ} (h : Rep s a) :
    (fun i => (s.tapes i).head) = a.heads := by
  funext i
  have h0 := h.2 i 0
  simpa using h0

theorem Rep.action {M : Machine k Γ Λ} {s : Config k Γ Λ} {a : ACfg k Γ Λ} (h : Rep s a) :
    M.action s = M.transition a.label a.heads := by
  unfold Machine.action; rw [h.1, h.heads]

theorem Rep.answer {M : Machine k Γ Λ} {s : Config k Γ Λ} {a : ACfg k Γ Λ} (h : Rep s a) :
    M.answer s = aanswer M a := by
  cases htr : M.transition a.label a.heads <;> simp [Machine.answer, aanswer, h.action, htr]

omit [Fintype Γ] in
theorem nth_apply_write (m : Move) (T : Tape Γ) (x : Γ) (z : ℤ) :
    (m.apply (T.write x)).nth z = if z + m.delta = 0 then x else T.nth (z + m.delta) := by
  cases m
  · simp only [Move.apply, Tape.move_left_nth, Tape.write_nth, Move.delta]
    rfl
  · simp [Move.apply, Move.delta, Tape.write_nth]
  · simp only [Move.apply, Tape.move_right_nth, Tape.write_nth, Move.delta] <;> rfl

omit [Fintype Γ] in
theorem rep_advance {s : Config k Γ Λ} {a : ACfg k Γ Λ} (h : Rep s a) (q : Λ)
    (w : Fin (k + 1) → Γ) (mv : Fin (k + 1) → Move) :
    Rep (⟨q, fun i => (mv i).apply ((s.tapes i).write (w i))⟩ : Config k Γ Λ)
      ⟨q, fun i => Function.update (a.C i) (a.P i) (w i), fun i => a.P i + (mv i).delta⟩ := by
  refine ⟨rfl, ?_⟩
  intro i z
  simp only [nth_apply_write, h.2, Function.update_apply]
  by_cases hz : z + (mv i).delta = 0
  · rw [if_pos hz, if_pos (by omega)]
  · rw [if_neg hz, if_neg (by omega)]
    congr 1
    omega

theorem Rep.step {M : Machine k Γ Λ} {s : Config k Γ Λ} {a a' : ACfg k Γ Λ} (h : Rep s a)
    (ha : astep M a = some a') : ∃ s', M.step s = some s' ∧ Rep s' a' := by
  obtain ⟨q, w, mv, htr, rfl⟩ := astep_eq_some ha
  refine ⟨_, ?_, rep_advance h q w mv⟩
  unfold Machine.step
  rw [h.action, htr]

/-- Observed configuration described by `a`, with ghost positions equal to `a.P`. -/
def ORep (o : Observed k Γ Λ) (a : ACfg k Γ Λ) : Prop :=
  Rep o.core a ∧ o.position = a.P

theorem ORep.step {M : Machine k Γ Λ} {o : Observed k Γ Λ} {a a' : ACfg k Γ Λ}
    (h : ORep o a) (ha : astep M a = some a') :
    ∃ o', observedStep M o = some o' ∧ ORep o' a' ∧
      ∀ i, o'.visited i = insert (a'.P i) (o.visited i) := by
  obtain ⟨q, w, mv, htr, rfl⟩ := astep_eq_some ha
  have hact : M.action o.core = .advance q w mv := by rw [h.1.action, htr]
  refine ⟨⟨⟨q, fun i => (mv i).apply ((o.core.tapes i).write (w i))⟩,
    fun i => o.position i + (mv i).delta,
    fun i => insert (o.position i + (mv i).delta) (o.visited i)⟩, ?_,
    ⟨rep_advance h.1 q w mv, ?_⟩, ?_⟩
  · unfold observedStep
    rw [hact]
  · funext i
    simp [h.2]
  · intro i
    simp [h.2]

/-! ### Windowed abstract runs -/

/-- `n` abstract steps from `a` to `b` with every head inside `W` throughout. -/
inductive ARun (M : Machine k Γ Λ) (W : Fin (k + 1) → Set ℤ) :
    ACfg k Γ Λ → ℕ → ACfg k Γ Λ → Prop
  | nil {a : ACfg k Γ Λ} : InW W a.P → ARun M W a 0 a
  | cons {a b c : ACfg k Γ Λ} {n : ℕ} : astep M a = some b → InW W a.P → ARun M W b n c →
      ARun M W a (n + 1) c

namespace ARun
variable {M : Machine k Γ Λ} {W : Fin (k + 1) → Set ℤ}

theorem start_mem {a b : ACfg k Γ Λ} {n : ℕ} (h : ARun M W a n b) : InW W a.P := by
  cases h with
  | nil h => exact h
  | cons _ h _ => exact h

theorem end_mem {a b : ACfg k Γ Λ} {n : ℕ} (h : ARun M W a n b) : InW W b.P := by
  induction h with
  | nil h => exact h
  | cons _ _ _ ih => exact ih

theorem trans {a b c : ACfg k Γ Λ} {n m : ℕ} (h : ARun M W a n b) (g : ARun M W b m c) :
    ARun M W a (n + m) c := by
  induction h with
  | nil _ => simpa using g
  | cons hs hw _ ih =>
    rw [Nat.add_right_comm]
    exact .cons hs hw (ih g)

/-- One step followed by a run. -/
theorem step {a b c : ACfg k Γ Λ} {n : ℕ} (hs : astep M a = some b) (h : ARun M W b n c)
    (hw : InW W a.P) : ARun M W a (n + 1) c := .cons hs hw h

theorem single {a b : ACfg k Γ Λ} (hs : astep M a = some b) (ha : InW W a.P) (hb : InW W b.P) :
    ARun M W a 1 b := .cons hs ha (.nil hb)

theorem mono {W' : Fin (k + 1) → Set ℤ} (hW : ∀ i, W i ⊆ W' i) {a b : ACfg k Γ Λ} {n : ℕ}
    (h : ARun M W a n b) : ARun M W' a n b := by
  induction h with
  | nil h => exact .nil fun i => hW i (h i)
  | cons hs hw _ ih => exact .cons hs (fun i => hW i (hw i)) ih

theorem of_eq {a b b' : ACfg k Γ Λ} {n : ℕ} (h : ARun M W a n b) (e : b = b') :
    ARun M W a n b' := e ▸ h

/-- Turn a windowed abstract run into an actual observed trace, keeping the
visited sets inside the window. -/
theorem observe {a b : ACfg k Γ Λ} {n : ℕ} (h : ARun M W a n b) {o : Observed k Γ Λ}
    (ho : ORep o a) (hv : ∀ i, ↑(o.visited i) ⊆ W i) :
    ∃ o', Trace M o n o' ∧ ORep o' b ∧ ∀ i, ↑(o'.visited i) ⊆ W i := by
  induction h generalizing o with
  | nil _ => exact ⟨o, .nil _, ho, hv⟩
  | @cons a b c n hs _ tail ih =>
    obtain ⟨o1, hstep, hrep, hvis⟩ := ho.step hs
    have hbW := tail.start_mem
    have hv1 : ∀ i, ↑(o1.visited i) ⊆ W i := by
      intro i
      rw [hvis i, Finset.coe_insert]
      exact Set.insert_subset (hbW i) (hv i)
    obtain ⟨o2, htr, hrep2, hv2⟩ := ih hrep hv1
    exact ⟨o2, .cons hstep htr, hrep2, hv2⟩

end ARun

/-! ### Window card bounds -/

theorem card_le_of_subset_Icc {s : Finset ℤ} {lo hi : ℤ} (h : ↑s ⊆ Set.Icc lo hi) :
    s.card ≤ (hi + 1 - lo).toNat := by
  have hs : s ⊆ Finset.Icc lo hi := by
    intro x hx
    have := h hx
    simpa using this
  have := Finset.card_le_card hs
  simpa [Int.card_Icc] using this

/-- If every tape's visited set lies in an interval of `L` cells, at most
`(k+1)·L` cells are visited in total. -/
theorem visitedCells_le_of_window {o : Observed k Γ Λ} {lo hi : Fin (k + 1) → ℤ} {L : ℕ}
    (h : ∀ i, ↑(o.visited i) ⊆ Set.Icc (lo i) (hi i)) (hL : ∀ i, (hi i + 1 - lo i).toNat ≤ L) :
    visitedCells o ≤ (k + 1) * L := by
  unfold visitedCells
  calc ∑ i, (o.visited i).card ≤ ∑ _i : Fin (k + 1), L :=
        Finset.sum_le_sum fun i _ => (card_le_of_subset_Icc (h i)).trans (hL i)
    _ = (k + 1) * L := by simp

end Machine

end QecReliability.RegMachine
