import CompletenessFormula
import PointHardness

set_option autoImplicit false

/-!
# The converse of `certFormula_unsat`, and the distance from a SAT oracle

`certFormula_sat_iff`: for isotropic rows, `certFormula rows L mins units` is satisfiable iff
there is an uncorrectable erased set `E` with `|E| ≤ L`, satisfying the unit constraints, that
contains no listed set. The direction "model ⇒ set" reads `E`, `x`, `z` off the assignment
(`E = {i | a i}`, `x.1 i = a (n + i)`, …); the two-sided Tseitin clauses force every gate value,
and the counter clauses with `¬c(n, L+1)` force `|E| ≤ L`.

With no listed sets and no units this gives the distance as the least `L` for which the formula
is satisfiable (`distance_le_iff_sat`, `sat_mono`, `distance_isLeast`): a binary search over
`L ∈ [0, n]` with a SAT decision oracle computes `d`.
-/

namespace QecPhysical.Stabilizer.Completeness

open Std.Sat
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecPhysical.Stabilizer.Uncorrectable

/-- The clauses of a gate force its value. -/
theorem Gate.ok_of_clauses (σ : Nat → Bool) (g : Gate)
    (h : ∀ c ∈ g.clauses, c.eval σ = true) : g.OK σ := by
  obtain ⟨t, op, a, b⟩ := g
  unfold Gate.OK
  rw [← List.all_eq_true] at h
  revert h
  cases op <;> simp only [Gate.clauses, GateOp.eval, List.all_cons, List.all_nil,
    CNF.Clause.eval_cons, CNF.Clause.eval_nil] <;>
    cases σ t <;> cases σ a <;> cases σ b <;> decide

def ofBool (b : Bool) : Bit := if b then 1 else 0

@[simp] theorem bb_ofBool (b : Bool) : bb (ofBool b) = b := by cases b <;> decide

theorem bb_eq_false_iff (b : Bit) : bb b = false ↔ b = 0 := by revert b; decide
theorem bb_eq_true_iff (b : Bit) : bb b = true ↔ b = 1 := by revert b; decide

theorem rowOuts_complete {n : ℕ} (sel : PauliCoord n → Nat) (F : Nat)
    (rows : List (List (PauliCoord n))) (s : Nat) :
    ∀ r ∈ rows, ∃ s', chainOut F (r.map sel) s' ∈ rowOuts sel F rows s ∧
      ∀ g ∈ chainGates F (r.map sel) s', g ∈ rowGates sel F rows s := by
  induction rows generalizing s with
  | nil => simp
  | cons r rs ih =>
    intro r' hr'
    simp only [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · exact ⟨s, by simp [rowOuts], fun g hg => by simp [rowGates, hg]⟩
    · obtain ⟨s', h1, h2⟩ := ih (s + r.length) r' hr'
      exact ⟨s', by simp [rowOuts, h1], fun g hg => by simp [rowGates, h2 g hg]⟩

theorem cnt_eq_card {n : ℕ} (σ : Nat → Bool) :
    cnt σ n = (Finset.univ.filter fun i : Fin n => σ (eVar i) = true).card := by
  unfold cnt
  rw [← Fin.sum_univ_eq_sum_range (fun k => if σ k = true then 1 else 0), Finset.card_filter]
  rfl

section ReadOff
variable {n : ℕ}

/-- The erased set read off an assignment. -/
def setOf (σ : Nat → Bool) : Finset (Fin n) := Finset.univ.filter fun i => σ (eVar i) = true
def xOf (σ : Nat → Bool) : Pauli n := (fun i => ofBool (σ (x1Var i)), fun i => ofBool (σ (x2Var i)))
def zOf (σ : Nat → Bool) : Pauli n := (fun i => ofBool (σ (z1Var i)), fun i => ofBool (σ (z2Var i)))

theorem mem_setOf (σ : Nat → Bool) (i : Fin n) : i ∈ setOf σ ↔ σ (eVar i) = true := by
  simp [setOf]

end ReadOff

/-- **A model yields a counterexample.** Every satisfying assignment of the formula gives an
uncorrectable erased set of size `≤ L` that satisfies the unit constraints and contains no
listed set. -/
theorem certFormula_model {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L : ℕ)
    (mins : List (List (Fin n))) (units : List (Fin n × Bool)) (σ : Nat → Bool)
    (hsat : (certFormula rows L mins units).Sat σ) :
    (setOf (n := n) σ).card ≤ L ∧ (∀ u ∈ units, (u.1 ∈ setOf (n := n) σ ↔ u.2 = true)) ∧
      (∀ M ∈ mins, ¬ M.toFinset ⊆ setOf (n := n) σ) ∧
      0 < ambiguity (symplectic n) (rowSpace rows) (supported (setOf (n := n) σ)) := by
  rw [CNF.sat_def, certFormula, cnf_eval_toArray, List.all_eq_true] at hsat
  set E : Finset (Fin n) := setOf (n := n) σ with hEdef
  set x : Pauli n := xOf σ
  set z : Pauli n := zOf σ
  -- membership of each clause group in `certClauses`
  have cK : ∀ c ∈ [[(fVar n, false)], [(tVar n, true)]], CNF.Clause.eval σ c = true := fun c hc =>
    hsat c (List.mem_append_left _ hc)
  have cG : ∀ c ∈ (allGates rows L).flatMap Gate.clauses, CNF.Clause.eval σ c = true := fun c hc =>
    hsat c (List.mem_append_right _ (List.mem_append_left _ hc))
  have cX : ∀ c ∈ (rowOuts selX (fVar n) rows (baseEnd n)).map (fun o => [(o, false)]),
      CNF.Clause.eval σ c = true := fun c hc =>
    hsat c (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hc)))
  have cZ : ∀ c ∈ (rowOuts selZ (fVar n) rows (zStart rows)).map (fun o => [(o, false)]),
      CNF.Clause.eval σ c = true := fun c hc =>
    hsat c (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ hc))))
  have cS : ∀ c ∈ supportClauses (n := n), CNF.Clause.eval σ c = true := fun c hc =>
    hsat c (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hc)))))
  have cY : ∀ c ∈ [[(chainOut (fVar n) (prodVars n (prodStart rows)) (sympStart rows), true)]],
      CNF.Clause.eval σ c = true := fun c hc =>
    hsat c (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hc))))))
  have cC : ∀ c ∈ [[(col n L (counterStart rows) n (L + 1), false)]], CNF.Clause.eval σ c = true :=
    fun c hc => hsat c (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hc)))))))
  have cM : ∀ c ∈ mins.map (fun M => M.map fun i => (eVar i, false)), CNF.Clause.eval σ c = true :=
    fun c hc => hsat c (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hc))))))))
  have cU : ∀ c ∈ units.map (fun u => [(eVar u.1, u.2)]), CNF.Clause.eval σ c = true :=
    fun c hc => hsat c (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hc))))))))
  -- gates and constants
  have hok : ∀ g ∈ allGates rows L, g.OK σ := fun g hg =>
    Gate.ok_of_clauses σ g (fun c hc => cG c (List.mem_flatMap.mpr ⟨g, hg, hc⟩))
  have sF : σ (fVar n) = false := by simpa [CNF.Clause.eval] using cK [(fVar n, false)] (by simp)
  have sT : σ (tVar n) = true := by simpa [CNF.Clause.eval] using cK [(tVar n, true)] (by simp)
  have mX : ∀ g ∈ rowGates selX (fVar n) rows (baseEnd n), g ∈ allGates rows L := fun g hg => by
    simp [allGates, hg]
  have mZ : ∀ g ∈ rowGates selZ (fVar n) rows (zStart rows), g ∈ allGates rows L :=
    fun g hg => by simp [allGates, hg]
  have mP : ∀ g ∈ prodGates n (prodStart rows), g ∈ allGates rows L := fun g hg => by
    simp [allGates, hg]
  have mS : ∀ g ∈ chainGates (fVar n) (prodVars n (prodStart rows)) (sympStart rows),
      g ∈ allGates rows L := fun g hg => by simp [allGates, hg]
  have mK : ∀ g ∈ counterGates n L (counterStart rows), g ∈ allGates rows L := fun g hg => by
    simp [allGates, hg]
  -- rows: both vectors are in the normalizer
  have hrow : ∀ (sel : PauliCoord n → Nat) (w : Pauli n) (s : Nat),
      (∀ c, σ (sel c) = bb (Sum.elim (fun i => w.2 i) (fun i => w.1 i) c)) →
      (∀ g ∈ rowGates sel (fVar n) rows s, g ∈ allGates rows L) →
      (∀ o ∈ rowOuts sel (fVar n) rows s, σ o = false) →
      w ∈ normalizer (symplectic n) (rowSpace rows) := by
    intro sel w s hsel hmem hout
    rw [mem_normalizer_rows]
    intro r hr
    obtain ⟨s', ho, hsub⟩ := rowOuts_complete sel (fVar n) rows s r hr
    have h1 := hout _ ho
    rw [chain_value σ _ _ _ (fun g hg => hok g (hmem g (hsub g hg))), sF, List.map_map] at h1
    have hfun : (σ ∘ sel) = (bb ∘ Sum.elim (fun i => w.2 i) (fun i => w.1 i)) := by
      funext c; exact hsel c
    rw [hfun, ← List.map_map, ← bb_sum, ← symplectic_decodeRow] at h1
    simpa [bb_eq_false_iff] using h1
  have hxN : x ∈ normalizer (symplectic n) (rowSpace rows) := by
    refine hrow selX x (baseEnd n) (fun c => ?_) mX (fun o ho => ?_)
    · cases c <;> simp [selX, x, xOf]
    · simpa [CNF.Clause.eval] using cX [(o, false)] (List.mem_map.mpr ⟨o, ho, rfl⟩)
  have hzN : z ∈ normalizer (symplectic n) (rowSpace rows) := by
    refine hrow selZ z (zStart rows) (fun c => ?_) mZ (fun o ho => ?_)
    · cases c <;> simp [selZ, z, zOf]
    · simpa [CNF.Clause.eval] using cZ [(o, false)] (List.mem_map.mpr ⟨o, ho, rfl⟩)
  -- support
  have hxE : x ∈ supported E := by
    intro i hi
    have he : σ (eVar i) = false := by
      have := (mem_setOf σ i).not.mp hi
      simpa using this
    have h1 := cS [(x1Var i, false), (eVar i, true)] (by
      simp only [supportClauses, List.mem_flatMap, List.mem_finRange, true_and]
      exact ⟨i, by simp⟩)
    have h2 := cS [(x2Var i, false), (eVar i, true)] (by
      simp only [supportClauses, List.mem_flatMap, List.mem_finRange, true_and]
      exact ⟨i, by simp⟩)
    simp [CNF.Clause.eval, he] at h1 h2
    exact ⟨by simp [x, xOf, h1, ofBool], by simp [x, xOf, h2, ofBool]⟩
  -- pairing
  have hxz : symplectic n x z = 1 := by
    have h := cY [(chainOut (fVar n) (prodVars n (prodStart rows)) (sympStart rows), true)] (by simp)
    simp only [CNF.Clause.eval_cons, CNF.Clause.eval_nil, Bool.or_false, beq_true] at h
    rw [chain_value σ _ _ _ (fun g hg => hok g (mS g hg)), sF] at h
    have hp1 : ∀ i : Fin n, σ (prodStart rows + i.val) = bb (x.1 i * z.2 i) := fun i => by
      have := hok _ (mP _ (by simp [prodGates]; exact Or.inl ⟨i, rfl⟩))
      simp only [Gate.OK, GateOp.eval] at this
      rw [this, bb_mul]; simp [x, z, xOf, zOf]
    have hp2 : ∀ i : Fin n, σ (prodStart rows + n + i.val) = bb (x.2 i * z.1 i) := fun i => by
      have := hok _ (mP _ (by simp [prodGates]; exact Or.inr ⟨i, rfl⟩))
      simp only [Gate.OK, GateOp.eval] at this
      rw [this, bb_mul]; simp [x, z, xOf, zOf]
    simp only [prodVars, List.map_append, List.map_ofFn] at h
    have e1 : (σ ∘ fun i : Fin n => prodStart rows + i.val) = fun i => bb (x.1 i * z.2 i) := by
      funext i; exact hp1 i
    have e2 : (σ ∘ fun i : Fin n => prodStart rows + n + i.val) =
        fun i => bb (x.2 i * z.1 i) := by
      funext i; exact hp2 i
    rw [e1, e2, xorList_append] at h
    have l1 : (List.ofFn fun i : Fin n => bb (x.1 i * z.2 i)) =
        (List.ofFn fun i : Fin n => x.1 i * z.2 i).map bb := by simp [List.map_ofFn]; rfl
    have l2 : (List.ofFn fun i : Fin n => bb (x.2 i * z.1 i)) =
        (List.ofFn fun i : Fin n => x.2 i * z.1 i).map bb := by simp [List.map_ofFn]; rfl
    rw [l1, l2, ← bb_sum, ← bb_sum, ← bb_add, List.sum_ofFn, List.sum_ofFn,
      ← Finset.sum_add_distrib, ← symplectic_apply] at h
    simpa [bb_eq_true_iff] using h
  -- the counter
  have hcard : E.card ≤ L := by
    have h := cC [(col n L (counterStart rows) n (L + 1), false)] (by simp)
    simp only [CNF.Clause.eval_cons, CNF.Clause.eval_nil, Bool.or_false] at h
    rw [col_value σ L _ (fun g hg => hok g (mK g hg)) sT sF n le_rfl (L + 1) le_rfl,
      cnt_eq_card] at h
    simp at h
    have : E.card = (Finset.univ.filter fun i : Fin n => σ (eVar i) = true).card := rfl
    omega
  refine ⟨hcard, ?_, ?_, ?_⟩
  · intro u hu
    have h := cU _ (List.mem_map.mpr ⟨u, hu, rfl⟩)
    simp only [CNF.Clause.eval_cons, CNF.Clause.eval_nil, Bool.or_false, beq_iff_eq] at h
    rw [hEdef, mem_setOf, h]
  · intro M hM hsub
    have h := cM _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
    simp only [CNF.Clause.eval, List.any_map, List.any_eq_true] at h
    obtain ⟨i, hiM, hi⟩ := h
    have hiE := hsub (List.mem_toFinset.mpr hiM)
    rw [hEdef, mem_setOf] at hiE
    simp [hiE] at hi
  · exact (uncorrectable_iff_certificate (rowSpace rows) hS E).mpr ⟨x, ⟨hxN, hxE⟩, z, hzN, hxz⟩

/-- **Satisfiability characterized.** -/
theorem certFormula_sat_iff {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L : ℕ)
    (mins : List (List (Fin n))) (units : List (Fin n × Bool)) :
    (∃ a, (certFormula rows L mins units).Sat a) ↔
      ∃ E : Finset (Fin n), E.card ≤ L ∧ (∀ u ∈ units, (u.1 ∈ E ↔ u.2 = true)) ∧
        (∀ M ∈ mins, ¬ M.toFinset ⊆ E) ∧
        0 < ambiguity (symplectic n) (rowSpace rows) (supported E) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨setOf (n := n) σ, certFormula_model rows hS L mins units σ hσ⟩
  · rintro ⟨E, hE, hu, hm, hamb⟩
    obtain ⟨x, hx, z, hzN, hxz⟩ :=
      (uncorrectable_iff_certificate (rowSpace rows) hS E).mp hamb
    exact ⟨_, certFormula_sat rows L mins units E hE hu hm x z hx.1 hx.2 hzN hxz⟩

/-- With no listed sets and no unit constraints: satisfiable iff some erased set of size `≤ L`
is uncorrectable. -/
theorem sat_iff_exists_uncorrectable {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L : ℕ) :
    (∃ a, (certFormula rows L [] []).Sat a) ↔
      ∃ E : Finset (Fin n), E.card ≤ L ∧
        0 < ambiguity (symplectic n) (rowSpace rows) (supported E) := by
  rw [certFormula_sat_iff rows hS]
  simp

/-- **Monotonicity in `L`.** -/
theorem sat_mono {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) {L L' : ℕ} (hL : L ≤ L')
    (h : ∃ a, (certFormula rows L [] []).Sat a) : ∃ a, (certFormula rows L' [] []).Sat a := by
  rw [sat_iff_exists_uncorrectable rows hS] at h ⊢
  obtain ⟨E, hE, hamb⟩ := h
  exact ⟨E, hE.trans hL, hamb⟩

/-- **Distance from a SAT oracle.** For isotropic rows with distance `d`:
`d ≤ L` iff `certFormula rows L [] []` is satisfiable. -/
theorem distance_le_iff_sat {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) (L : ℕ) :
    d ≤ L ↔ ∃ a, (certFormula rows L [] []).Sat a := by
  rw [sat_iff_exists_uncorrectable rows hS]
  exact (exists_uncorrectable_le_iff (rowSpace rows) hd L).symm

/-- The distance is the least `L` for which the formula is satisfiable. -/
theorem distance_isLeast {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) :
    IsLeast {L : ℕ | ∃ a, (certFormula rows L [] []).Sat a} d :=
  ⟨(distance_le_iff_sat rows hS hd d).mp le_rfl,
    fun L hL => (distance_le_iff_sat rows hS hd L).mpr hL⟩

/-- **Existence for the search.** The formula at `L = n` is satisfiable iff a distance exists,
and then `d ≤ n`; so a binary search over `[0, n]` with the monotone predicate of `sat_mono`
returns the distance, or reports (unsatisfiable at `n`) that every erased set is correctable. -/
theorem sat_at_n_iff_exists_distance {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) :
    (∃ a, (certFormula rows n [] []).Sat a) ↔ ∃ d, IsDistance (rowSpace rows) d ∧ d ≤ n := by
  constructor
  · intro h
    rw [sat_iff_exists_uncorrectable rows hS] at h
    obtain ⟨E, -, hamb⟩ := h
    exact exists_isDistance _ (uncorrectable_mono _ hS (Finset.subset_univ E) hamb)
  · rintro ⟨d, hd, hdn⟩
    exact (distance_le_iff_sat rows hS hd n).mp hdn

/-- A distance exists iff the full erasure is uncorrectable, i.e. iff `dim S < n` (`k > 0`). -/
theorem exists_distance_iff_rank {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) :
    (∃ d, IsDistance (rowSpace rows) d) ↔ Module.finrank Bit (rowSpace rows) < n := by
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨E, -, hamb⟩ := hd.2
    have h := uncorrectable_mono _ hS (Finset.subset_univ E) hamb
    rw [ambiguity_full _ hS] at h
    omega
  · intro h
    have hu : 0 < ambiguity (symplectic n) (rowSpace rows) (supported Finset.univ) := by
      rw [ambiguity_full _ hS]; omega
    obtain ⟨d, hd, -⟩ := exists_isDistance _ hu
    exact ⟨d, hd⟩

end QecPhysical.Stabilizer.Completeness

#print axioms QecPhysical.Stabilizer.Completeness.certFormula_model
#print axioms QecPhysical.Stabilizer.Completeness.certFormula_sat_iff
#print axioms QecPhysical.Stabilizer.Completeness.sat_mono
#print axioms QecPhysical.Stabilizer.Completeness.distance_le_iff_sat
#print axioms QecPhysical.Stabilizer.Completeness.distance_isLeast
#print axioms QecPhysical.Stabilizer.Completeness.sat_at_n_iff_exists_distance
#print axioms QecPhysical.Stabilizer.Completeness.exists_distance_iff_rank
