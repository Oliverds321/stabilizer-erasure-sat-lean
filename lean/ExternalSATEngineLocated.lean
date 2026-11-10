import ExternalSATFrontLocated

/-! The engine phase follows the accepted engine finite table on the same
physical tapes. Its coordinates are translated by the actual handoff heads.
Intervals are contained in the hull of the frontend history and the translated
engine history; tapes outside the engine image retain their frontend history. -/
namespace QecReliability.ExternalSATBridge.PrimitiveLink

open OAI.Algorithms.SubexponentialSAT
open Computation SqrtLogSpace

theorem located_interval_step {N : PrimitiveMachine} {c d : LocatedCfg N}
    (hs : locatedStep N c = some d)
    (he : ∀ i, c.lower i ≤ c.position i ∧ c.position i ≤ c.upper i)
    (i : Fin N.tapeCount) :
    d.lower i = min (c.lower i) (d.position i) ∧
      d.upper i = max (c.upper i) (d.position i) := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases hstate : c.config.state with
  | inl answer =>
    simp [LocatedCfg.monitor, hstate, min_eq_left (he i).1, max_eq_left (he i).2]
  | inr q =>
    cases ht : N.transition q (c.config.tapes (N.scan q)).head with
    | inl answer =>
      simp [LocatedCfg.monitor, hstate, ht, min_eq_left (he i).1, max_eq_left (he i).2]
    | inr result =>
      obtain ⟨q', action⟩ := result
      by_cases hi : i = N.scan q
      · subst i
        simp [LocatedCfg.monitor, hstate, ht]
      · simp [LocatedCfg.monitor, hstate, ht, hi,
          min_eq_left (he i).1, max_eq_left (he i).2]

variable (F M : PrimitiveMachine) (out : Fin F.tapeCount)

theorem engine_displacement {c : (machine F M out).Cfg} {e : M.Cfg}
    (h : EngineRelated F M out c e) (i : Fin M.tapeCount) :
    PrimitiveTransport.displacement (machine F M out) c (engineSlot F M out i) =
      PrimitiveTransport.displacement M e i := by
  rcases h with ⟨hstate, htapes⟩
  cases hs : e.state with
  | inl answer =>
    simp [PrimitiveTransport.displacement, hstate, engineState, hs]
  | inr q =>
    cases ht : M.transition q (e.tapes (M.scan q)).head with
    | inl answer =>
      simp [PrimitiveTransport.displacement, hstate, engineState, hs, machine,
        engineTransition, htapes, ht]
    | inr result =>
      obtain ⟨q', action⟩ := result
      simp [PrimitiveTransport.displacement, hstate, engineState, hs, machine,
        engineTransition, htapes, ht, (engine_injective F M out).eq_iff]

theorem engine_outside_displacement {c : (machine F M out).Cfg} {e : M.Cfg}
    (h : EngineRelated F M out c e) (j : Fin (F.tapeCount + M.tapeCount))
    (hj : ∀ i, j ≠ engineSlot F M out i) :
    PrimitiveTransport.displacement (machine F M out) c j = 0 := by
  rcases h with ⟨hstate, htapes⟩
  cases hs : e.state with
  | inl answer =>
    simp [PrimitiveTransport.displacement, hstate, engineState, hs]
  | inr q =>
    cases ht : M.transition q (e.tapes (M.scan q)).head with
    | inl answer =>
      simp [PrimitiveTransport.displacement, hstate, engineState, hs, machine,
        engineTransition, htapes, ht]
    | inr result =>
      obtain ⟨q', action⟩ := result
      simp [PrimitiveTransport.displacement, hstate, engineState, hs, machine,
        engineTransition, htapes, ht, hj]

structure EngineLocatedRelated (base c : LocatedCfg (machine F M out))
    (e : LocatedCfg M) : Prop where
  core : EngineRelated F M out c.config e.config
  enclosed : ∀ j, c.lower j ≤ c.position j ∧ c.position j ≤ c.upper j
  source_enclosed : ∀ i, e.lower i ≤ e.position i ∧ e.position i ≤ e.upper i
  position : ∀ i, c.position (engineSlot F M out i) =
    base.position (engineSlot F M out i) + e.position i
  lower : ∀ i, min (base.lower (engineSlot F M out i))
    (base.position (engineSlot F M out i) + e.lower i) ≤ c.lower (engineSlot F M out i)
  upper : ∀ i, c.upper (engineSlot F M out i) ≤
    max (base.upper (engineSlot F M out i)) (base.position (engineSlot F M out i) + e.upper i)
  outside : ∀ j, (∀ i, j ≠ engineSlot F M out i) →
    c.lower j = base.lower j ∧ c.upper j = base.upper j

theorem engine_located_step {base c : LocatedCfg (machine F M out)} {e e' : LocatedCfg M}
    (he : locatedStep M e = some e') (h : EngineLocatedRelated F M out base c e) :
    ∃ c', locatedStep (machine F M out) c = some c' ∧
      EngineLocatedRelated F M out base c' e' := by
  obtain ⟨next, hnext, hcore⟩ := engine_step F M out (locatedStep_config he) h.core
  let c' := c.monitor next
  have hcs : locatedStep (machine F M out) c = some c' := by
    simp [locatedStep, hnext, c']
  have hp : ∀ i, c'.position (engineSlot F M out i) =
      base.position (engineSlot F M out i) + e'.position i := by
    intro i
    have htarget : c'.position (engineSlot F M out i) =
        c.position (engineSlot F M out i) + PrimitiveTransport.displacement M e.config i :=
      (PrimitiveTransport.located_position_step hcs (engineSlot F M out i)).trans
        (congrArg (fun z : ℤ => c.position (engineSlot F M out i) + z)
          (engine_displacement F M out h.core i))
    have hsource := PrimitiveTransport.located_position_step he i
    have hposition := h.position i
    omega
  have henc := locatedStep_encloses he h.source_enclosed
  refine ⟨c', hcs, ⟨?_, locatedStep_encloses hcs h.enclosed, henc, hp, ?_, ?_, ?_⟩⟩
  · simpa only [c', LocatedCfg.monitor_config] using hcore
  · intro i
    have hex := locatedStep_expands he i
    have hi := located_interval_step hcs h.enclosed (engineSlot F M out i)
    rw [hi.1]
    apply le_min
    · apply le_trans _ (h.lower i)
      apply le_min (min_le_left _ _)
      exact (min_le_right _ _).trans (by omega)
    · rw [hp]
      exact (shifted_hull_encloses (a := base.lower (engineSlot F M out i))
        (b := base.upper (engineSlot F M out i))
        (p := base.position (engineSlot F M out i)) (henc i)).1
  · intro i
    have hex := locatedStep_expands he i
    have hi := located_interval_step hcs h.enclosed (engineSlot F M out i)
    rw [hi.2]
    apply max_le
    · apply le_trans (h.upper i)
      apply max_le (le_max_left _ _)
      exact (show base.position (engineSlot F M out i) + e.upper i ≤
        base.position (engineSlot F M out i) + e'.upper i by omega).trans (le_max_right _ _)
    · rw [hp]
      exact (shifted_hull_encloses (a := base.lower (engineSlot F M out i))
        (b := base.upper (engineSlot F M out i))
        (p := base.position (engineSlot F M out i)) (henc i)).2
  · intro j hj
    have hjp : c'.position j = c.position j := by
      calc
        c'.position j = c.position j +
            PrimitiveTransport.displacement (machine F M out) c.config j :=
          PrimitiveTransport.located_position_step hcs j
        _ = c.position j + 0 := congrArg (fun z : ℤ => c.position j + z)
          (engine_outside_displacement F M out h.core j hj)
        _ = c.position j := add_zero _
    have hi := located_interval_step hcs h.enclosed j
    rw [hjp, min_eq_left (h.enclosed j).1, max_eq_left (h.enclosed j).2] at hi
    exact ⟨hi.1.trans (h.outside j hj).1, hi.2.trans (h.outside j hj).2⟩

theorem engine_located_trace {base : LocatedCfg (machine F M out)}
    {a b : LocatedCfg M} {n : ℕ} (h : Trace (locatedStep M) n a b)
    (c : LocatedCfg (machine F M out)) (hc : EngineLocatedRelated F M out base c a) :
    ∃ d, Trace (locatedStep (machine F M out)) n c d ∧
      EngineLocatedRelated F M out base d b := by
  induction h generalizing c with
  | refl => exact ⟨c, .refl _, hc⟩
  | cons hs _ ih =>
    obtain ⟨c', hs', hc'⟩ := engine_located_step F M out hs hc
    obtain ⟨d, hd, hrel⟩ := ih c' hc'
    exact ⟨d, .cons hs' hd, hrel⟩

theorem handoff_located {f : LocatedCfg F} {marker : Bool} {word : List Bool}
    (hh : f.config.state = .inl marker)
    (hw : f.config.tapes out = Turing.Tape.mk₁ (word.map some))
    (he : ∀ i, f.lower i ≤ f.position i ∧ f.position i ≤ f.upper i) :
    EngineLocatedRelated F M out (frontLocated F M out f) (frontLocated F M out f)
      (locatedInit M word) := by
  refine ⟨handoff F M out hh hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · change frontInts F M f.lower (frontSlot F M k) ≤ frontInts F M f.position (frontSlot F M k) ∧
        frontInts F M f.position (frontSlot F M k) ≤ frontInts F M f.upper (frontSlot F M k)
      simpa only [frontInts_front] using he k
    · change frontInts F M f.lower (freshSlot F M k) ≤ frontInts F M f.position (freshSlot F M k) ∧
        frontInts F M f.position (freshSlot F M k) ≤ frontInts F M f.upper (freshSlot F M k)
      simp only [frontInts_fresh, le_refl, and_self]
  · intro i
    simp only [locatedInit, Int.ofNat_eq_natCast]
    split_ifs <;> omega
  · intro i
    simp only [locatedInit, add_zero]
  · intro i
    exact min_le_left _ _
  · intro i
    exact le_max_left _ _
  · intro j hj
    exact ⟨rfl, rfl⟩

end QecReliability.ExternalSATBridge.PrimitiveLink
