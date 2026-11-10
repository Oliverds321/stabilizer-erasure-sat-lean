import Final.Statement

/-!
# The output word determines the coefficient vector

`outputWord` (Final/Statement.lean) is a concatenation of self-delimiting `natHeader` words,
so it is injective. Hence `Outputs M run o v` pins down `v` uniquely.
-/

set_option autoImplicit false

namespace QecReliability.Final
open OracleCost RationalOutput

/-- A concatenation of codewords that a reader can peel off one at a time is injective. -/
theorem flatMap_injective_of_reader {α β : Type} (f : α → List Bool) (key : α → β)
    (hkey : Function.Injective key) (read : List Bool → Option (β × List Bool))
    (hread : ∀ x rest, read (f x ++ rest) = some (key x, rest)) (hne : ∀ x, f x ≠ []) :
    Function.Injective (fun xs : List α => xs.flatMap f) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.mp h.symm).1 (hne y)
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [List.flatMap_nil, List.flatMap_cons] at h
      exact absurd (List.append_eq_nil_iff.mp h).1 (hne x)
    | cons y ys =>
      simp only [List.flatMap_cons] at h
      have hx := hread x (xs.flatMap f)
      have hy := hread y (ys.flatMap f)
      rw [h, hy] at hx
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hx)
      rw [hkey h1.symm, ih h2.symm]

/-- Read two `natHeader` words. -/
def readPair (bits : List Bool) : Option ((ℕ × ℕ) × List Bool) :=
  match QueryCodec.readHeader 0 bits with
  | none => none
  | some (a, r₁) =>
    match QueryCodec.readHeader 0 r₁ with
    | none => none
    | some (b, r₂) => some ((a, b), r₂)

theorem readPair_spec (x : Ratio) (rest : List Bool) :
    readPair (QueryCodec.natHeader x.num ++ QueryCodec.natHeader x.den ++ rest) =
      some ((x.num, x.den), rest) := by
  simp only [readPair, List.append_assoc, QueryCodec.readHeader_natHeader]

theorem ratio_key_injective : Function.Injective (fun x : Ratio => (x.num, x.den)) := by
  rintro ⟨a, b, _, _⟩ ⟨c, d, _, _⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem outputWord_injective {r : ℕ} : Function.Injective (outputWord (r := r)) := by
  rintro ⟨xs, hx⟩ ⟨ys, hy⟩ h
  have hflat := flatMap_injective_of_reader
    (fun x : Ratio => QueryCodec.natHeader x.num ++ QueryCodec.natHeader x.den)
    (fun x : Ratio => (x.num, x.den)) ratio_key_injective readPair readPair_spec
    (fun x => by simp [QueryCodec.natHeader]) h
  have : xs = ys := by
    simpa using congrArg List.toArray hflat
  subst this
  rfl

/-- Lists without blank symbols are determined by their `getI` values. -/
theorem list_eq_of_getI {Γ : Type} [Inhabited Γ] {l₁ l₂ : List Γ}
    (h₁ : ∀ x ∈ l₁, x ≠ default) (h₂ : ∀ x ∈ l₂, x ≠ default)
    (h : ∀ n, l₁.getI n = l₂.getI n) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons y ys => exact absurd (by simpa using (h 0).symm) (h₂ y (by simp))
  | cons x xs ih =>
    cases l₂ with
    | nil => exact absurd (by simpa using h 0) (h₁ x (by simp))
    | cons y ys =>
      have h0 : x = y := by simpa using h 0
      subst h0
      rw [ih (l₂ := ys) (fun z hz => h₁ z (List.mem_cons_of_mem _ hz))
        (fun z hz => h₂ z (List.mem_cons_of_mem _ hz)) (fun n => by simpa using h (n + 1))]

/-- `Outputs` determines the vector. -/
theorem Outputs.unique {k : ℕ} {Γ Λ : Type} [Fintype Γ] [Inhabited Γ] [Fintype Λ]
    {M : MultiTape.Machine k Γ Λ} {bits : List Bool} {run : MultiTape.Completed M bits}
    {o : Fin (k+1)} {r : ℕ} {v w : RationalOutput.Vector r}
    (hv : Outputs M run o v) (hw : Outputs M run o w) : v = w := by
  unfold Outputs at hv hw
  rw [hv] at hw
  have hn : ∀ n : ℕ, ((outputWord v).map M.inputSymbol).getI n =
      ((outputWord w).map M.inputSymbol).getI n := by
    intro n
    have := congrArg (fun T => Turing.Tape.nth T (n : ℤ)) hw
    simpa [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat,
      Turing.ListBlank.nth_mk] using this
  have hl := list_eq_of_getI
    (by simp only [List.mem_map]; rintro _ ⟨b, -, rfl⟩; exact M.input_not_blank b)
    (by simp only [List.mem_map]; rintro _ ⟨b, -, rfl⟩; exact M.input_not_blank b) hn
  exact outputWord_injective ((List.map_injective_iff.mpr M.input_injective) hl)

end QecReliability.Final
