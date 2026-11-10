import ExternalSATIntervalHull

/-! Passive coordinates for the frontend phase of the accepted finite-table
link. The final frontend halt becomes a zero-displacement write-back, preserving
the already visited interval because that interval encloses the current head. -/
namespace QecReliability.ExternalSATBridge.PrimitiveLink

open OAI.Algorithms.SubexponentialSAT
open Computation SqrtLogSpace
open scoped BigOperators

variable (F M : PrimitiveMachine) (out : Fin F.tapeCount)

def frontInts (v : Fin F.tapeCount → ℤ) : Fin (F.tapeCount + M.tapeCount) → ℤ :=
  Fin.addCases v (fun _ => 0)

@[simp] theorem frontInts_front (v : Fin F.tapeCount → ℤ) (i : Fin F.tapeCount) :
    frontInts F M v (frontSlot F M i) = v i := by simp [frontInts, frontSlot]

@[simp] theorem frontInts_fresh (v : Fin F.tapeCount → ℤ) (i : Fin M.tapeCount) :
    frontInts F M v (freshSlot F M i) = 0 := by simp [frontInts, freshSlot]

theorem frontInts_update (v : Fin F.tapeCount → ℤ) (i : Fin F.tapeCount) (z : ℤ) :
    frontInts F M (Function.update v i z) =
      Function.update (frontInts F M v) (frontSlot F M i) z := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change frontInts F M (Function.update v i z) (frontSlot F M k) =
      Function.update (frontInts F M v) (frontSlot F M i) z (frontSlot F M k)
    simp only [frontInts_front, Function.update_apply, front_inj]
  · change frontInts F M (Function.update v i z) (freshSlot F M k) =
      Function.update (frontInts F M v) (frontSlot F M i) z (freshSlot F M k)
    simp [Function.update_apply, Ne.symm (front_ne_fresh F M i k)]

@[simp] theorem frontInts_update_self (v : Fin F.tapeCount → ℤ) (i : Fin F.tapeCount) :
    Function.update (frontInts F M v) (frontSlot F M i) (v i) = frontInts F M v := by
  funext j
  by_cases hj : j = frontSlot F M i
  · subst j
    simp [Function.update_apply]
  · simp [Function.update_apply, hj]

@[simp] theorem frontInts_zero : frontInts F M (fun _ => 0) = fun _ => 0 := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp [frontInts]

def frontLocated (c : LocatedCfg F) : LocatedCfg (machine F M out) where
  config := frontCfg F M out c.config
  position := frontInts F M c.position
  lower := frontInts F M c.lower
  upper := frontInts F M c.upper

theorem front_located_step {c d : LocatedCfg F}
    (hs : locatedStep F c = some d)
    (he : ∀ i, c.lower i ≤ c.position i ∧ c.position i ≤ c.upper i) :
    locatedStep (machine F M out) (frontLocated F M out c) =
      some (frontLocated F M out d) := by
  obtain ⟨next, hnext, rfl⟩ := Option.map_eq_some_iff.mp hs
  change ((machine F M out).step (frontCfg F M out c.config)).map
    (frontLocated F M out c).monitor = some (frontLocated F M out (c.monitor next))
  rw [front_step F M out hnext, Option.map_some]
  apply congrArg some
  cases hstate : c.config.state with
  | inl answer => simp [PrimitiveMachine.step, hstate] at hnext
  | inr q =>
    cases ht : F.transition q (c.config.tapes (F.scan q)).head with
    | inl answer =>
      have hp := he (F.scan q)
      simp [LocatedCfg.monitor, frontLocated, frontCfg, frontState, machine,
        frontTransition, hstate, ht, headDisplacement, min_eq_left hp.1,
        max_eq_left hp.2]
      exact ⟨frontInts_update_self F M c.position (F.scan q),
        frontInts_update_self F M c.lower (F.scan q),
        frontInts_update_self F M c.upper (F.scan q)⟩
    | inr result =>
      obtain ⟨q', action⟩ := result
      cases action <;>
        simp [LocatedCfg.monitor, frontLocated, frontCfg, frontState, machine,
          frontTransition, hstate, ht, frontInts_update] <;> exact ⟨rfl, rfl, rfl⟩

theorem front_located_trace {a b : LocatedCfg F} {n : ℕ}
    (h : Trace (locatedStep F) n a b)
    (he : ∀ i, a.lower i ≤ a.position i ∧ a.position i ≤ a.upper i) :
    Trace (locatedStep (machine F M out)) n (frontLocated F M out a)
      (frontLocated F M out b) := by
  induction h with
  | refl => exact .refl _
  | cons hs _ ih =>
    exact .cons (front_located_step F M out hs he) (ih (locatedStep_encloses hs he))

theorem frontInts_initial_upper (bits : List Bool) :
    frontInts F M (fun i => if i = F.inputTape then Int.ofNat (bits.length - 1) else 0) =
      (fun i => if i = frontSlot F M F.inputTape then Int.ofNat (bits.length - 1) else 0) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change frontInts F M _ (frontSlot F M k) =
      (if frontSlot F M k = frontSlot F M F.inputTape then _ else _)
    simp [front_inj]
  · change frontInts F M _ (freshSlot F M k) =
      (if freshSlot F M k = frontSlot F M F.inputTape then _ else _)
    simp [Ne.symm (front_ne_fresh F M F.inputTape k)]

theorem front_located_initial (bits : List Bool) :
    frontLocated F M out (locatedInit F bits) = locatedInit (machine F M out) bits := by
  simp only [frontLocated, locatedInit, front_initial, frontInts_zero, frontInts_initial_upper] <;> rfl

/-- Every allocated fresh tape has its initial cell charged, including the
unused engine-input slot. This is physical interval accounting. -/
theorem front_located_space (c : LocatedCfg F) :
    visitedSpace (frontLocated F M out c) = visitedSpace c + M.tapeCount := by
  change (∑ i : Fin (F.tapeCount + M.tapeCount),
    (frontInts F M c.upper i - frontInts F M c.lower i + 1).toNat) =
      visitedSpace c + M.tapeCount
  rw [Fin.sum_univ_add]
  simp [frontInts, visitedSpace]

end QecReliability.ExternalSATBridge.PrimitiveLink
