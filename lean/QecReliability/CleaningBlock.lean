import QecReliability.SparseReconstruction

/-! Conditional coordinate agreement with the actual sparse reconstruction circuit. -/
namespace QecReliability.SharedCircuit
open PrefixCNF

def conditionalEquality {v : ℕ} (e x y : Fin v) : Formula v :=
  [[(e, false), (x, false), (y, true)], [(e, false), (x, true), (y, false)]]

theorem conditionalEquality_correct {v : ℕ} (e x y : Fin v) (a : BitModels v) :
    PrefixCNF.eval (conditionalEquality e x y) a = true ↔ (a e = true → a x = a y) := by
  cases he : a e <;> cases hx : a x <;> cases hy : a y <;>
    simp [conditionalEquality, PrefixCNF.eval, evalClause, he, hx, hy]

def allCoords (n : ℕ) : List (PauliCoord n) :=
  List.ofFn Sum.inl ++ List.ofFn Sum.inr

theorem mem_allCoords {n : ℕ} (c : PauliCoord n) : c ∈ allCoords n := by
  cases c with
  | inl i => exact List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩))
  | inr i => exact List.mem_append.mpr (Or.inr (List.mem_ofFn.mpr ⟨i, rfl⟩))

def coordinateAgreement {n v : ℕ} (e z s : PauliCoord n → Fin v) : Formula v :=
  ((allCoords n).map (fun c => conditionalEquality (e c) (s c) (z c))).flatten

theorem coordinateAgreement_correct {n v : ℕ} (e z s : PauliCoord n → Fin v) (a : BitModels v) :
    PrefixCNF.eval (coordinateAgreement e z s) a = true ↔
      ∀ c, a (e c) = true → a (s c) = a (z c) := by
  simp only [coordinateAgreement, PrefixCNF.eval, List.all_flatten, List.all_map,
    Function.comp_def]
  rw [List.all_eq_true]
  change (∀ c ∈ allCoords n, PrefixCNF.eval (conditionalEquality (e c) (s c) (z c)) a = true) ↔ _
  simp only [conditionalEquality_correct]
  constructor
  · intro h c; exact h c (mem_allCoords c)
  · intro h c _; exact h c

theorem coordinateAgreement_width {n v : ℕ} (e z s : PauliCoord n → Fin v) :
    Width 3 (coordinateAgreement e z s) := by
  intro c hc
  obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hcs
  simp only [conditionalEquality, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp

theorem coordinateAgreement_length {n v : ℕ} (e z s : PauliCoord n → Fin v) :
    (coordinateAgreement e z s).length = 4 * n := by
  simp [coordinateAgreement, allCoords, conditionalEquality, List.length_flatten,
    Function.comp_def]
  omega

theorem boolBit_injective : Function.Injective boolBit := by
  intro x y h
  cases x <;> cases y <;> simp_all [boolBit]

namespace Reconstruction

def cleaningBlock {n v : ℕ} (R : Reconstruction n v) (e zx zz : Fin n → Fin v) : Block v where
  aux := R.gates
  formula := R.circuit.compile ++ coordinateAgreement
    (fun c => Fin.castAdd R.gates (Sum.elim e e c))
    (fun c => Fin.castAdd R.gates (Sum.elim zx zz c)) R.output

theorem cleaningBlock_correct {n v : ℕ} (R : Reconstruction n v) (e zx zz : Fin n → Fin v)
    (a : BitModels v) : (R.cleaningBlock e zx zz).Accepts a ↔
      ∀ i, a (e i) = true → (R.value a).1 i = boolBit (a (zx i)) ∧
        (R.value a).2 i = boolBit (a (zz i)) := by
  have he : ∀ u : BitModels R.gates, PrefixCNF.eval (R.cleaningBlock e zx zz).formula (Fin.append a u) = true ↔
      PrefixCNF.eval R.circuit.compile (Fin.append a u) = true ∧
      ∀ c, a (Sum.elim e e c) = true →
        Fin.append a u (R.output c) = a (Sum.elim zx zz c) := by
    intro u
    change PrefixCNF.eval (_ ++ _) _ = true ↔ _
    simp only [PrefixCNF.eval, List.all_append, Bool.and_eq_true]
    change _ ∧ PrefixCNF.eval (coordinateAgreement _ _ _) _ = true ↔ _
    rw [coordinateAgreement_correct]
    dsimp only [cleaningBlock]
    simp only [Fin.append_left]
  have hc : (R.cleaningBlock e zx zz).Accepts a ↔
      ∀ c, a (Sum.elim e e c) = true → R.circuit.run a (R.output c) = a (Sum.elim zx zz c) := by
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨hcompile, hout⟩ := (he u).mp hu
      have hv := Circuit.satisfying_unique R.circuit a (Fin.append a u) hcompile
        (by funext i; exact Fin.append_left _ _ _)
      simpa only [hv] using hout
    · intro h
      refine ⟨R.circuit.auxiliaries a, (he _).mpr ?_⟩
      rw [Circuit.append_auxiliaries]
      exact ⟨Circuit.run_satisfies _ _, h⟩
  rw [hc]
  constructor
  · intro h i hi
    exact ⟨congrArg boolBit (h (.inl i) hi), congrArg boolBit (h (.inr i) hi)⟩
  · intro h c hc'
    cases c with
    | inl i => exact boolBit_injective ((h i hc').1)
    | inr i => exact boolBit_injective ((h i hc').2)

theorem cleaningBlock_deterministic {n v : ℕ} (R : Reconstruction n v) (e zx zz : Fin n → Fin v) :
    (R.cleaningBlock e zx zz).Deterministic := by
  intro a u v hu hv
  have hc : ∀ t, PrefixCNF.eval (R.cleaningBlock e zx zz).formula (Fin.append a t) = true →
      PrefixCNF.eval R.circuit.compile (Fin.append a t) = true := by
    intro t ht
    change PrefixCNF.eval (_ ++ _) _ = true at ht
    simp only [PrefixCNF.eval, List.all_append, Bool.and_eq_true] at ht
    exact ht.1
  exact (Circuit.unique_auxiliaries _ _).unique (hc u hu) (hc v hv)

theorem cleaningBlock_width {n v : ℕ} (R : Reconstruction n v) (e zx zz : Fin n → Fin v) :
    Width 3 (R.cleaningBlock e zx zz).formula := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact Circuit.compile_width _ c hc
  · exact coordinateAgreement_width _ _ _ c hc

theorem cleaningBlock_length {n v : ℕ} (R : Reconstruction n v) (e zx zz : Fin n → Fin v) :
    (R.cleaningBlock e zx zz).formula.length ≤ 4 * R.gates + 4 * n := by
  have h := Circuit.compile_length R.circuit
  simpa [cleaningBlock, coordinateAgreement_length] using Nat.add_le_add_right h (4 * n)

end Reconstruction
end QecReliability.SharedCircuit
