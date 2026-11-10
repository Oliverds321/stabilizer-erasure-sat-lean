import OracleCost.MachineObservations

/-!

A proof-only displacement trace for the EXISTING physical MultiTape machine.
No new operational model, compiler, clock oracle, or arithmetic instruction is
introduced. Displacements are sums of actual unit head moves, not machine data.
-/
set_option autoImplicit false
namespace QecReliability.OracleCost.MultiTape.Displacement
variable {k : Nat} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]

/-- Ghost displacement of one physical transition; halt has no successor. -/
def delta (M : Machine k Γ Λ) (s : Config k Γ Λ) : Fin (k + 1) → Int :=
  match M.action s with
  | .halt _ => fun _ => 0
  | .advance _ _ moves => fun i => (moves i).delta

inductive Run (M : Machine k Γ Λ) :
    Config k Γ Λ → Nat → (Fin (k + 1) → Int) → Config k Γ Λ → Prop
  | nil (s) : Run M s 0 (fun _ => 0) s
  | cons {s t u n d} (step : M.step s = some t) (tail : Run M t n d u) :
      Run M s (n + 1) (fun i => delta M s i + d i) u

theorem Run.core {M : Machine k Γ Λ} {s t : Config k Γ Λ} {n d}
    (h : Run M s n d t) : CoreTrace M s n t := by
  induction h with
  | nil => exact .nil _
  | cons he _ ih => exact .cons he ih

theorem single {M : Machine k Γ Λ} {s t : Config k Γ Λ}
    (h : M.step s = some t) : Run M s 1 (delta M s) t := by
  simpa only [Int.add_zero] using Run.cons h (Run.nil t)

theorem Run.trans {M : Machine k Γ Λ} {s t u : Config k Γ Λ} {n m d e}
    (h : Run M s n d t) (g : Run M t m e u) :
    Run M s (n + m) (fun i => d i + e i) u := by
  induction h with
  | nil => simpa only [Nat.zero_add, Int.zero_add] using g
  | cons he _ ih =>
    simpa only [Nat.add_right_comm, Int.add_assoc] using Run.cons he (ih g)

theorem observedStep_delta {M : Machine k Γ Λ} {s t : Observed k Γ Λ}
    (h : observedStep M s = some t) (i : Fin (k + 1)) :
    t.position i = s.position i + delta M s.core i := by
  cases ha : M.action s.core with
  | halt b => simp [observedStep, ha] at h
  | advance label write move =>
    simp only [observedStep, ha, Option.some.injEq] at h
    subst t
    simp only [delta, ha]

/-- Both relative tape contents AND absolute head locations are retained. -/
theorem Run.observe {M : Machine k Γ Λ} {s t : Config k Γ Λ} {n d}
    (h : Run M s n d t) (initial : Observed k Γ Λ) (hi : initial.core = s) :
    ∃ final, Trace M initial n final ∧ final.core = t ∧
      ∀ i, final.position i = initial.position i + d i := by
  induction h generalizing initial with
  | nil s => exact ⟨initial, .nil _, hi, fun _ => by simp⟩
  | @cons s t u n d he tail ih =>
    obtain ⟨next, hs, hn⟩ := observedStep_exists (hi ▸ he)
    obtain ⟨final, ht, hf, hp⟩ := ih next hn
    refine ⟨final, .cons hs ht, hf, ?_⟩
    intro i
    rw [hp i, observedStep_delta hs, hi]
    simp only [Int.add_assoc]

/-- Sequential actual observed traces compose by adding physical transitions. -/
theorem observed_trans {M : Machine k Γ Λ} {s t u : Observed k Γ Λ} {n m}
    (h : Trace M s n t) (g : Trace M t m u) : Trace M s (n + m) u := by
  induction h with
  | nil => simpa using g
  | cons he _ ih => simpa only [Nat.add_right_comm] using Trace.cons he (ih g)

end QecReliability.OracleCost.MultiTape.Displacement
