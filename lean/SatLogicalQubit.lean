import SatToDistance

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The code of `reduce φ` has exactly one logical qubit

`reduce_finrank`: `finrank (rowSpace (reduce φ).rows) + 1 = (reduce φ).n`, so `k = n − dim S = 1`.

Route. Let `X̄ = logicalOf e x₀` (from any solution `x₀` of `H x = s`) and `Z̄` = `Z` on every
copy of the extra coordinate. Then:
* X side (as in `sol_of_logical`): an `X`-type element of `N` with folded value `0` on the extra
  coordinate lies in `S`; with folded value `1` it differs from `X̄` by such an element.
* Z side, by double orthogonality `S = N^⊥`: a `Z`-type element `B ∈ N` with
  `ω(B, X̄) = 0` pairs to zero with every element of `N` (only the `X` part of the other
  element matters, and that part lies in `S + ⟨X̄⟩`), hence lies in `S`.
So `N ≤ S ⊔ ⟨X̄, Z̄⟩`, `dim N ≤ dim S + 2`; with `dim N = 2n − dim S` and `S < N` this gives
`dim S = n − 1`.
-/

namespace QecReliability.SatReduction

open scoped BigOperators
open Finset
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecPhysical.Stabilizer.EnumeratorExample (pauliWeight)
open QecPhysical.Stabilizer.Uncorrectable

attribute [local instance 2000] instBEqOfDecidableEq

theorem symp_comm {n : ℕ} (x y : Pauli n) : symplectic n x y = symplectic n y x := by
  rw [symplectic_apply, symplectic_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem symp_fst_of_snd_zero {n : ℕ} (Q W : Pauli n) (hW : W.1 = 0) :
    symplectic n Q W = symplectic n (Q.1, 0) W := by
  simp [symplectic_apply, hW]

section Generic

variable {G R : Type} [Fintype G] [DecidableEq G]
variable {m n : ℕ} (e : Option G × Fin (m + 1) ≃ Fin n)
variable (eqs : R → List G) (rhs : R → Bit) (gens : List (List G)) (allR : List R)
  (allG : List G)

/-- `Z` on every copy of the extra coordinate. -/
def zbar : Pauli n := (0, fun i => if (e.symm i).1 = none then 1 else 0)

theorem fold_add (a b : Fin n → Bit) (g : Option G) :
    fold e (a + b) g = fold e a g + fold e b g := by
  unfold fold
  simp [Finset.sum_add_distrib]

theorem fold_logicalOf_none (x : G → Bit) : fold e (logicalOf e x).1 none = 1 := by
  unfold fold logicalOf
  simp only [Equiv.symm_apply_apply, Option.elim]
  rw [Finset.sum_ite_eq']
  simp

theorem symp_zbar_logicalOf (x : G → Bit) : symplectic n (zbar e) (logicalOf e x) = 1 := by
  rw [symplectic_apply, ← Equiv.sum_comp e]
  simp only [zbar, logicalOf, Equiv.symm_apply_apply, Pi.zero_apply, zero_mul, zero_add]
  rw [Fintype.sum_prod_type, Fintype.sum_option]
  simp

theorem zbar_mem_N (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR) :
    zbar e ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)) := by
  rw [mem_N e eqs rhs gens allR allG hG hR]
  refine ⟨fun gen _ => ?_, fun g k => ?_, fun r => ?_⟩
  · simp only [zbar, Equiv.symm_apply_apply, reduceCtorEq, ite_false]
    exact sum_map_zero gen
  · simp only [zbar, Equiv.symm_apply_apply]
    exact bit_add_self _
  · simp only [zbar]
    rw [fold_zero]
    exact sum_map_zero _

/-- The `X` part of a normalizer element is in the normalizer. -/
theorem xpart_mem_N (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR) {P : Pauli n}
    (hP : P ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG))) :
    ((P.1, 0) : Pauli n) ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)) := by
  obtain ⟨-, -, h3⟩ := (mem_N e eqs rhs gens allR allG hG hR P).1 hP
  rw [mem_N e eqs rhs gens allR allG hG hR]
  refine ⟨fun gen _ => ?_, fun g k => ?_, fun r => h3 r⟩
  · simp only [Pi.zero_apply]
    exact sum_map_zero gen
  · simp

/-- The `Z` part of a normalizer element is in the normalizer. -/
theorem zpart_mem_N (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR) {P : Pauli n}
    (hP : P ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG))) :
    ((0, P.2) : Pauli n) ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)) := by
  obtain ⟨h1, h2, -⟩ := (mem_N e eqs rhs gens allR allG hG hR P).1 hP
  rw [mem_N e eqs rhs gens allR allG hG hR]
  refine ⟨h1, h2, fun r => ?_⟩
  rw [fold_zero]
  exact sum_map_zero _

/-- **X side.** An `X`-type normalizer element with folded value `0` on the extra coordinate
lies in the stabilizer. -/
theorem xpart_mem_S (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR)
    (hspan : ∀ x : G → Bit, (∀ r, ((eqs r).map x).sum = 0) →
      x ∈ Submodule.span Bit {v | v ∈ gens.map listVec})
    {a : Fin n → Bit}
    (hN : ((a, 0) : Pauli n) ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)))
    (hy0 : fold e a none = 0) :
    ((a, 0) : Pauli n) ∈ rowSpace (codeRows e eqs rhs gens allR allG) := by
  set S := rowSpace (codeRows e eqs rhs gens allR allG)
  obtain ⟨-, -, h3⟩ := (mem_N e eqs rhs gens allR allG hG hR _).1 hN
  set y := fold e a
  have h3' : ∀ r, ((zList eqs rhs r).map y).sum = 0 := fun r => h3 r
  set x : G → Bit := fun g => y (some g)
  have hxk : ∀ r, ((eqs r).map x).sum = 0 := by
    intro r; have := h3' r; rw [zList_sum, hy0] at this; simpa using this
  have hxS : liftK e x ∈ S := by
    have hmem := Submodule.apply_mem_span_image_of_mem_span (liftK e) (hspan x hxk)
    refine Submodule.span_le.2 ?_ hmem
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨gen, hgen, rfl⟩ := List.mem_map.1 hv
    rw [liftK_listVec]
    exact Submodule.subset_span (List.mem_map.2 ⟨genRow e gen,
      (mem_codeRows e eqs rhs gens allR allG).2 (Or.inl ⟨gen, hgen, rfl⟩), rfl⟩)
  have hstar : ∀ g k, decodeRow (starRow (n := n) e g k) ∈ S := by
    intro g k
    have hg' : g ∈ allOpt allG := by
      rcases g with _ | g
      · simp [allOpt]
      · simp [allOpt, hG g]
    exact Submodule.subset_span (List.mem_map.2 ⟨starRow e g k,
      (mem_codeRows e eqs rhs gens allR allG).2 (Or.inr (Or.inl ⟨g, hg', k, rfl⟩)), rfl⟩)
  have hdecomp : ((a, 0) : Pauli n) = liftK e x +
      ∑ q : Option G × Fin (m + 1), a (e q) • decodeRow (starRow (n := n) e q.1 q.2) := by
    apply Prod.ext
    · funext i
      obtain ⟨q, rfl⟩ := e.surjective i
      rcases q with ⟨g, k⟩
      rw [Prod.fst_add, Prod.fst_sum, Pi.add_apply, Finset.sum_apply]
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, starRow, decodeRow_xRowQ,
        Equiv.symm_apply_apply]
      rw [star_sum]
      simp only [liftK, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]
      by_cases hk : k = 0
      · subst hk
        simp only [ite_true]
        rcases g with _ | g
        · simp only [Option.elim]
          change a (e (none, 0)) = 0 + (y none + a (e (none, 0)))
          rw [hy0]; simp
        · simp only [Option.elim]
          change a (e (some g, 0)) = y (some g) + (y (some g) + a (e (some g, 0)))
          rw [← add_assoc, bit_add_self, zero_add]
      · simp [hk]
    · rw [Prod.snd_add, Prod.snd_sum]
      simp [liftK, starRow, decodeRow_xRowQ]
  rw [hdecomp]
  exact S.add_mem hxS (S.sum_mem (fun q _ => S.smul_mem _ (hstar q.1 q.2)))

/-- The `X` part of a normalizer element is in `S` or in `X̄ + S`. -/
theorem xpart_cases (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR)
    (hspan : ∀ x : G → Bit, (∀ r, ((eqs r).map x).sum = 0) →
      x ∈ Submodule.span Bit {v | v ∈ gens.map listVec})
    {x0 : G → Bit} (hx0 : ∀ r, ((eqs r).map x0).sum = rhs r) {P : Pauli n}
    (hP : P ∈ normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG))) :
    ((P.1, 0) : Pauli n) ∈ rowSpace (codeRows e eqs rhs gens allR allG) ∨
      ((P.1, 0) : Pauli n) + logicalOf e x0 ∈ rowSpace (codeRows e eqs rhs gens allR allG) := by
  have hA := xpart_mem_N e eqs rhs gens allR allG hG hR hP
  rcases bit_cases (fold e P.1 none) with h0 | h1
  · exact Or.inl (xpart_mem_S e eqs rhs gens allR allG hG hR hspan hA h0)
  · right
    have hX := logicalOf_mem_N e eqs rhs gens allR allG hG hR hx0
    have hsum : ((P.1, 0) : Pauli n) + logicalOf e x0 = ((P.1 + (logicalOf e x0).1, 0) : Pauli n) := by
      apply Prod.ext
      · rfl
      · simp [logicalOf]
    rw [hsum]
    apply xpart_mem_S e eqs rhs gens allR allG hG hR hspan
    · rw [← hsum]; exact Submodule.add_mem _ hA hX
    · rw [fold_add, h1, fold_logicalOf_none]; decide

/-- **`N ≤ S ⊔ ⟨X̄, Z̄⟩`.** -/
theorem normalizer_le (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR)
    (hspan : ∀ x : G → Bit, (∀ r, ((eqs r).map x).sum = 0) →
      x ∈ Submodule.span Bit {v | v ∈ gens.map listVec})
    {x0 : G → Bit} (hx0 : ∀ r, ((eqs r).map x0).sum = rhs r) :
    normalizer (symplectic n) (rowSpace (codeRows e eqs rhs gens allR allG)) ≤
      rowSpace (codeRows e eqs rhs gens allR allG) ⊔
        Submodule.span Bit (({logicalOf e x0, zbar e} : Finset (Pauli n)) : Set (Pauli n)) := by
  set S := rowSpace (codeRows e eqs rhs gens allR allG)
  set T := Submodule.span Bit (({logicalOf e x0, zbar e} : Finset (Pauli n)) : Set (Pauli n))
  have hXT : logicalOf e x0 ∈ S ⊔ T :=
    Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hZT : zbar e ∈ S ⊔ T :=
    Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hX := logicalOf_mem_N e eqs rhs gens allR allG hG hR hx0
  have hZ := zbar_mem_N e eqs rhs gens allR allG hG hR
  have hSS : (symplectic n).orthogonal (normalizer (symplectic n) S) = S :=
    (symplectic n).orthogonal_orthogonal (symplectic_nondegenerate n) (symplectic_refl n) S
  intro P hP
  have hsplit : P = ((P.1, 0) : Pauli n) + ((0, P.2) : Pauli n) := by simp
  -- X part
  have hA : ((P.1, 0) : Pauli n) ∈ S ⊔ T := by
    rcases xpart_cases e eqs rhs gens allR allG hG hR hspan hx0 hP with h | h
    · exact Submodule.mem_sup_left h
    · have : ((P.1, 0) : Pauli n) = (((P.1, 0) : Pauli n) + logicalOf e x0) + logicalOf e x0 := by
        rw [add_assoc]
        have : logicalOf e x0 + logicalOf e x0 = 0 := by
          apply Prod.ext <;> funext i <;> simp [bit_add_self]
        rw [this, add_zero]
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left h) hXT
  -- Z part
  set B : Pauli n := (0, P.2)
  have hB := zpart_mem_N e eqs rhs gens allR allG hG hR hP
  set c := symplectic n B (logicalOf e x0)
  set B' := B + c • zbar e
  have hB'N : B' ∈ normalizer (symplectic n) S :=
    Submodule.add_mem _ hB (Submodule.smul_mem _ c hZ)
  have hB'1 : B'.1 = 0 := by simp [B', B, zbar]
  have hB'S : B' ∈ S := by
    rw [← hSS]
    intro Q hQ
    show symplectic n Q B' = 0
    rw [symp_fst_of_snd_zero Q B' hB'1]
    have hpair : ∀ s ∈ S, symplectic n s B' = 0 := fun s hs => hB'N s hs
    rcases xpart_cases e eqs rhs gens allR allG hG hR hspan hx0 hQ with h | h
    · exact hpair _ h
    · have h0 := hpair _ h
      have hlin : symplectic n (((Q.1, 0) : Pauli n) + logicalOf e x0) B' =
          symplectic n ((Q.1, 0) : Pauli n) B' + symplectic n (logicalOf e x0) B' :=
        LinearMap.map_add₂ _ _ _ _
      have hXB' : symplectic n (logicalOf e x0) B' = c + c := by
        simp only [B', map_add, map_smul, smul_eq_mul]
        rw [symp_comm (logicalOf e x0) B, symp_comm (logicalOf e x0) (zbar e),
          symp_zbar_logicalOf, mul_one]
      rw [hlin, hXB', bit_add_self, add_zero] at h0
      exact h0
  have hBT : B ∈ S ⊔ T := by
    have : B = B' + c • zbar e := by
      simp only [B', add_assoc, ← add_smul, bit_add_self, zero_smul, add_zero]
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hB'S) (Submodule.smul_mem _ c hZT)
  rw [hsplit]
  exact Submodule.add_mem _ hA hBT

/-- **Exactly one logical qubit**, for a system with a solution. -/
theorem finrank_add_one (hG : ∀ g, g ∈ allG) (hR : ∀ r, r ∈ allR)
    (hgen : ∀ gen ∈ gens, ∀ r, ((eqs r).map (listVec gen)).sum = 0)
    (hspan : ∀ x : G → Bit, (∀ r, ((eqs r).map x).sum = 0) →
      x ∈ Submodule.span Bit {v | v ∈ gens.map listVec})
    {x0 : G → Bit} (hx0 : ∀ r, ((eqs r).map x0).sum = rhs r) :
    Module.finrank Bit (rowSpace (codeRows e eqs rhs gens allR allG)) + 1 = n := by
  set S := rowSpace (codeRows e eqs rhs gens allR allG)
  set T := Submodule.span Bit (({logicalOf e x0, zbar e} : Finset (Pauli n)) : Set (Pauli n))
  have hS : S ≤ normalizer (symplectic n) S :=
    codeRows_isotropic e eqs rhs gens allR allG hG hR hgen
  have hle := normalizer_le e eqs rhs gens allR allG hG hR hspan hx0
  have fN : Module.finrank Bit (normalizer (symplectic n) S) = 2 * n - Module.finrank Bit S :=
    finrank_normalizer S
  have fS : Module.finrank Bit S ≤ n := isotropic_finrank_le S hS
  have hT : Module.finrank Bit T ≤ 2 :=
    le_trans (finrank_span_finset_le_card _) (Finset.card_le_two)
  have h1 : Module.finrank Bit (normalizer (symplectic n) S) ≤ Module.finrank Bit S + 2 :=
    le_trans (Submodule.finrank_mono hle)
      (le_trans (Submodule.finrank_add_le_finrank_add_finrank S T) (by omega))
  have hlt : S < normalizer (symplectic n) S := by
    refine lt_of_le_of_ne hS (fun h => ?_)
    have hX := logicalOf_mem_N e eqs rhs gens allR allG hG hR hx0
    rw [← h] at hX
    exact logicalOf_not_mem e eqs rhs gens allR allG x0 hX
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  omega

end Generic

namespace Formula

variable (F : Formula)

theorem rows_finrank (hpos : ∀ c, 0 < F.len c) :
    Module.finrank Bit (rowSpace F.rows) + 1 = F.nq := by
  obtain ⟨x0, hx0⟩ := F.exists_sol hpos
  exact finrank_add_one F.qEquiv F.eqList F.eqRhs F.kerGens F.allRow F.allCoord F.mem_allCoord
    F.mem_allRow (fun gen hg => F.kerGens_ker gen hg) (fun _ hx => F.ker_mem_span hx) hx0

end Formula

/-- **The code of `reduce φ` has exactly one logical qubit:** `dim S + 1 = n`. -/
theorem reduce_finrank (φ : Std.Sat.CNF Nat) :
    Module.finrank Bit (rowSpace (reduce φ).rows) + 1 = (reduce φ).n :=
  (formulaOf φ).rows_finrank (formulaOf_len_pos φ)

/-- The number of logical qubits `n − dim S` is `1`. -/
theorem reduce_logical_qubits (φ : Std.Sat.CNF Nat) :
    (reduce φ).n - Module.finrank Bit (rowSpace (reduce φ).rows) = 1 := by
  have := reduce_finrank φ
  omega

end QecReliability.SatReduction

#print axioms QecReliability.SatReduction.reduce_finrank
#print axioms QecReliability.SatReduction.reduce_logical_qubits
#print axioms QecReliability.SatReduction.finrank_add_one
#print axioms QecReliability.SatReduction.normalizer_le
