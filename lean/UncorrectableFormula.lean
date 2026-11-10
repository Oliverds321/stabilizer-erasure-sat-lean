import QecReliability.BadWeightEncoder
import QecReliability.DecisionTrial
import UncorrectableProbability

set_option autoImplicit false

/-!
# The uncorrectable-erasure count as a projected model count of one 3-CNF

Formula-level step of Corollary `cor:uncorrectable`: the fixed-weight Bad certificate
`BadEncoding.layerFormula rows j` (`QecReliability/BadWeightEncoder.lean`; Bad block plus a
population counter fixing `|E| = j`) has its variables ordered `E` (n bits), `z` (2n bits),
`x` (2n bits), auxiliaries. `uncFormula rows j` is the same clause list, with the variable
indices regrouped as `n + (everything else)`, so that `PrefixCNF.Projected` projects onto the
`n` erasure bits only: `z`, `x` and the auxiliaries are existential.

* `uncFormula_projected`: an assignment `E` of the `n` designated variables extends to a
  model iff `|E| = j` and `E` is uncorrectable (`0 < ambiguity`, the predicate behind
  `Uncorrectable.uncorrectable`).
* `uncFormula_count`: the projected model count is `uncCount (rowSpace rows) j`
  `= #{E : |E| = j, 0 < ambiguity}`.
* `uncorrectableProb_eq_counts`: `U_H(p) = Σ_j uncCount j · p^j (1-p)^(n-j)` for the
  development's `uncorrectableProb`.
* `uncFormula_contract`: width 3, at most `18 I + 99 n + 52` clauses and at most
  `29 n + 4 I + 12` variables (`I = rowIncidences rows`), plus the two facts above.

This is a statement about the formula; no machine that calls a counting engine on it is
formalized here.
-/

namespace QecPhysical.Stabilizer.UncorrectableFormula

open QecReliability QecReliability.SharedCircuit QecReliability.PrefixCNF QecReliability.Binary
open QecPhysical.Stabilizer.Uncorrectable
open scoped BigOperators

/-- Number of uncorrectable erased sets of size `j`. -/
noncomputable def uncCount {n : ℕ} (S : Submodule Bit (Pauli n)) (j : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun E : Finset (Fin n) =>
    E.card = j ∧ 0 < ambiguity (symplectic n) S (supported E)).card

/-- `U_H(p) = Σ_j C_j p^j (1-p)^(n-j)` with `C_j = uncCount S j`. -/
theorem uncorrectableProb_eq_counts {n : ℕ} (S : Submodule Bit (Pauli n)) (p : ℝ) :
    uncorrectableProb S p =
      ∑ j ∈ Finset.range (n + 1), (uncCount S j : ℝ) * (p ^ j * (1 - p) ^ (n - j)) := by
  classical
  unfold uncorrectableProb
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (n + 1))
    (g := Finset.card) (fun E _ => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (by simpa using E.card_le_univ)))]
  apply Finset.sum_congr rfl
  intro j _
  unfold uncCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro E _
  unfold causeMass uncorrectable
  by_cases hE : E.card = j <;>
    by_cases ha : 0 < ambiguity (symplectic n) S (supported E) <;> simp [hE, ha]

section Formula
variable {n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ)

/-- The existential (non-designated) variables: `z`, `x`, and the gate auxiliaries. -/
abbrev hiddenVars : ℕ :=
  (n + n) + (BadEncoding.witnessSize n + (BadEncoding.layerBlock rows j).aux)

/-- **The formula.** Variables `0, …, n-1` are the erasure bits `e_i`; the other
`hiddenVars rows j` variables are existential. -/
def uncFormula : Formula (n + hiddenVars rows j) :=
  rename (Fin.cast (Nat.add_assoc n (n + n)
    (BadEncoding.witnessSize n + (BadEncoding.layerBlock rows j).aux)))
    (BadEncoding.layerFormula rows j)

theorem uncFormula_projected_iff (e : BitModels n) :
    Projected (uncFormula rows j) e ↔
      ∃ zb : BitModels (n + n), Projected (BadEncoding.layerFormula rows j) (Fin.append e zb) := by
  constructor
  · rintro ⟨bu, hbu⟩
    let zb : BitModels (n + n) := fun i => bu (Fin.castAdd _ i)
    let u : BitModels (BadEncoding.witnessSize n + (BadEncoding.layerBlock rows j).aux) :=
      fun i => bu (Fin.natAdd (n + n) i)
    have he : Fin.append zb u = bu := Fin.append_castAdd_natAdd
    refine ⟨zb, u, ?_⟩
    rw [uncFormula, eval_rename] at hbu
    rw [← he] at hbu
    have hassoc := Fin.append_assoc e zb u
    change PrefixCNF.eval (BadEncoding.layerFormula rows j)
      (Fin.append e (Fin.append zb u) ∘ Fin.cast _) = true at hbu
    rwa [← hassoc] at hbu
  · rintro ⟨zb, u, hu⟩
    refine ⟨Fin.append zb u, ?_⟩
    rw [uncFormula, eval_rename]
    change PrefixCNF.eval (BadEncoding.layerFormula rows j)
      (Fin.append e (Fin.append zb u) ∘ Fin.cast _) = true
    rwa [← Fin.append_assoc]

theorem erasures_append (E : Finset (Fin n)) (zb : BitModels (n + n)) :
    BadEncoding.erasures (Fin.append (causeBits n E) zb) = E := by
  ext i
  simp [BadEncoding.erasures, wiredErasures, causeBits]

theorem pauli_append (e : BitModels n) (zb : BitModels (n + n)) :
    BadEncoding.pauli (Fin.append e zb) = BadEncoding.witness zb := by
  apply Prod.ext <;> funext i <;>
    simp [BadEncoding.pauli, BadEncoding.witness, wiredPauli]

/-- **Projection onto the erasure bits.** For isotropic rows and `j ≤ n`, the assignment
`E` of the `n` designated variables extends to a model of `uncFormula rows j` iff
`|E| = j` and `E` is uncorrectable. -/
theorem uncFormula_projected
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (hj : j ≤ n)
    (E : Finset (Fin n)) :
    Projected (uncFormula rows j) (causeBits n E) ↔
      E.card = j ∧ 0 < ambiguity (symplectic n) (rowSpace rows) (supported E) := by
  rw [uncFormula_projected_iff, uncorrectable_iff_certificate (rowSpace rows) hS E]
  simp_rw [BadEncoding.layer_projected_correct rows j hj, erasures_append, pauli_append]
  constructor
  · rintro ⟨zb, hc, hz, x, hx, hxz⟩
    exact ⟨hc, x, hx, _, hz, hxz⟩
  · rintro ⟨hc, x, hx, z, hz, hxz⟩
    refine ⟨BadEncoding.encodeWitness z, ?_⟩
    rw [BadEncoding.witness_encode]
    exact ⟨hc, hz, x, hx, hxz⟩

/-- **Projected model count.** The number of assignments of the `n` erasure variables that
extend to a model is `C_j = #{E : |E| = j, E uncorrectable}`. -/
theorem uncFormula_count
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (hj : j ≤ n) :
    PrefixEnumeration.modelCount (Projected (uncFormula rows j)) =
      uncCount (rowSpace rows) j := by
  classical
  have he : Projected (uncFormula rows j) = fun a => (causeBits n).symm a ∈
      (Finset.univ.filter fun E : Finset (Fin n) =>
        E.card = j ∧ 0 < ambiguity (symplectic n) (rowSpace rows) (supported E)) := by
    funext a
    apply propext
    conv_lhs => rw [← Equiv.apply_symm_apply (causeBits n) a]
    rw [uncFormula_projected rows j hS hj, Finset.mem_filter]
    simp
  rw [he, encoded_modelCount]
  unfold uncCount
  congr 1

/-- **Headline.** For isotropic rows and `j ≤ n`: `uncFormula rows j` is a 3-CNF with at most
`18 I + 99 n + 52` clauses on `n + hiddenVars rows j ≤ 29 n + 4 I + 12` variables
(`I = rowIncidences rows`); an assignment `E` of its first `n` variables extends to a model iff
`|E| = j` and `E` is uncorrectable; hence its projected model count onto those `n` variables
is `C_j = uncCount (rowSpace rows) j`, and `U_H(p) = Σ_j C_j p^j (1-p)^(n-j)`. -/
theorem uncFormula_contract
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (hj : j ≤ n) :
    Width 3 (uncFormula rows j) ∧
    (uncFormula rows j).length ≤ 18 * rowIncidences rows + 99 * n + 52 ∧
    n + hiddenVars rows j ≤ 29 * n + 4 * rowIncidences rows + 12 ∧
    (∀ E : Finset (Fin n), Projected (uncFormula rows j) (causeBits n E) ↔
      E.card = j ∧ 0 < ambiguity (symplectic n) (rowSpace rows) (supported E)) ∧
    PrefixEnumeration.modelCount (Projected (uncFormula rows j)) =
      uncCount (rowSpace rows) j ∧
    ∀ p : ℝ, uncorrectableProb (rowSpace rows) p =
      ∑ i ∈ Finset.range (n + 1), (uncCount (rowSpace rows) i : ℝ) * (p ^ i * (1 - p) ^ (n - i)) := by
  have hc := BadEncoding.layer_compiler_contract rows j hj
  refine ⟨width_rename _ _ hc.1, ?_, ?_, uncFormula_projected rows j hS hj,
    uncFormula_count rows j hS hj, uncorrectableProb_eq_counts (rowSpace rows)⟩
  · rw [uncFormula, length_rename]
    exact hc.2.1
  · have h := hc.2.2.1
    simp only [hiddenVars]
    simp only [BadEncoding.projectionSize] at h
    omega

end Formula

end QecPhysical.Stabilizer.UncorrectableFormula

#print axioms QecPhysical.Stabilizer.UncorrectableFormula.uncFormula_contract
#print axioms QecPhysical.Stabilizer.UncorrectableFormula.uncFormula_projected
#print axioms QecPhysical.Stabilizer.UncorrectableFormula.uncFormula_count
#print axioms QecPhysical.Stabilizer.UncorrectableFormula.uncorrectableProb_eq_counts
