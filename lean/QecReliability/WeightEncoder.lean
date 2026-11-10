import QecReliability.PopulationCounter

/-! Linear-size fixed-weight constraints compiled from the constructed population counter. -/
namespace QecReliability.SharedCircuit
open PrefixCNF
open scoped BigOperators

theorem wordValue_injective (k : ℕ) : Function.Injective (@wordValue k) := by
  induction k with
  | zero => intro a b _; exact Subsingleton.elim _ _
  | succ k ih =>
    intro a b h
    have ha := Fin.cons_self_tail a
    have hb := Fin.cons_self_tail b
    rw [← ha, ← hb, wordValue_cons, wordValue_cons] at h
    have he : a 0 = b 0 := by
      cases ha₀ : a 0 <;> cases hb₀ : b 0 <;> simp_all
      all_goals omega
    have ht : wordValue (Fin.tail a) = wordValue (Fin.tail b) := by rw [he] at h; omega
    rw [← ha, ← hb, he, ih ht]

def targetBits : (k : ℕ) → ℕ → BitModels k
  | 0, _ => finZeroElim
  | k + 1, j => Fin.cons (decide (j % 2 = 1)) (targetBits k (j / 2))

theorem targetBits_value (k j : ℕ) (hj : j < 2 ^ k) : wordValue (targetBits k j) = j := by
  induction k generalizing j with
  | zero =>
    simp only [pow_zero] at hj
    have hj0 : j = 0 := by omega
    subst j
    rfl
  | succ k ih =>
    rw [targetBits, wordValue_cons, ih]
    · have hm : j % 2 < 2 := Nat.mod_lt j (by omega)
      by_cases h : j % 2 = 1 <;> simp [h] <;> omega
    · rw [pow_succ] at hj
      omega

def outputUnits {v k : ℕ} (outs : Fin k → Fin v) (bits : BitModels k) : Formula v :=
  List.ofFn (fun i => [(outs i, bits i)])

theorem outputUnits_eval {v k : ℕ} (outs : Fin k → Fin v) (bits : BitModels k) (a : BitModels v) :
    PrefixCNF.eval (outputUnits outs bits) a = true ↔ (fun i => a (outs i)) = bits := by
  simp only [outputUnits, PrefixCNF.eval, List.all_eq_true, List.mem_ofFn]
  constructor
  · intro h
    funext i
    simpa [evalClause] using h _ ⟨i, rfl⟩
  · intro h c hc
    obtain ⟨i, rfl⟩ := hc
    simpa [evalClause] using congrFun h i

theorem outputUnits_width {v k : ℕ} (outs : Fin k → Fin v) (bits : BitModels k) :
    Width 1 (outputUnits outs bits) := by
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  simp

@[simp] theorem outputUnits_length {v k : ℕ} (outs : Fin k → Fin v) (bits : BitModels k) :
    (outputUnits outs bits).length = k := by simp [outputUnits]

def Program.matchBlock {v k : ℕ} (P : Program v k) (bits : BitModels k) : Block v :=
  ⟨P.gates, P.circuit.compile ++ outputUnits P.output bits⟩

set_option backward.isDefEq.respectTransparency false in
theorem Program.matchBlock_correct {v k : ℕ} (P : Program v k) (bits : BitModels k) (a : BitModels v) :
    (P.matchBlock bits).Accepts a ↔ P.eval a = bits := by
  have he : ∀ u, PrefixCNF.eval (P.matchBlock bits).formula (Fin.append a u) = true ↔
      PrefixCNF.eval P.circuit.compile (Fin.append a u) = true ∧
      (fun i => Fin.append a u (P.output i)) = bits := by
    intro u
    change PrefixCNF.eval (_ ++ _) _ = true ↔ _
    simp only [PrefixCNF.eval, List.all_append, Bool.and_eq_true]
    exact and_congr_right (fun _ => outputUnits_eval _ _ _)
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hc, hout⟩ := (he u).mp hu
    have hu' := Circuit.satisfying_unique P.circuit a (Fin.append a u) hc
      (by funext i; exact Fin.append_left _ _ _)
    funext i
    change P.circuit.run a (P.output i) = bits i
    have hi := congrFun hout i
    rw [hu'] at hi
    exact hi
  · intro h
    refine ⟨P.circuit.auxiliaries a, (he _).mpr ?_⟩
    rw [Circuit.append_auxiliaries]
    exact ⟨Circuit.run_satisfies _ _, h⟩

set_option backward.isDefEq.respectTransparency false in
theorem Program.matchBlock_deterministic {v k : ℕ} (P : Program v k) (bits : BitModels k) :
    (P.matchBlock bits).Deterministic := by
  intro a u v hu hv
  have hc : ∀ t, PrefixCNF.eval (P.matchBlock bits).formula (Fin.append a t) = true →
      PrefixCNF.eval P.circuit.compile (Fin.append a t) = true := by
    intro t ht
    change PrefixCNF.eval (_ ++ _) _ = true at ht
    simp only [PrefixCNF.eval, List.all_append, Bool.and_eq_true] at ht
    exact ht.1
  exact (Circuit.unique_auxiliaries _ _).unique (hc u hu) (hc v hv)

set_option backward.isDefEq.respectTransparency false in
theorem Program.matchBlock_width {v k : ℕ} (P : Program v k) (bits : BitModels k) :
    Width 3 (P.matchBlock bits).formula := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact Circuit.compile_width _ c hc
  · have h := outputUnits_width P.output bits c hc; omega

theorem Program.matchBlock_length {v k : ℕ} (P : Program v k) (bits : BitModels k) :
    (P.matchBlock bits).formula.length ≤ 4 * P.gates + k := by
  have h := Circuit.compile_length P.circuit
  simpa [Program.matchBlock] using Nat.add_le_add_right h k

theorem counter_width_bound (n : ℕ) : counterDepth n + 1 ≤ n + 3 := by
  have h := Nat.log2_le_self (max 1 n)
  unfold counterDepth
  omega

def weightBlock {n v : ℕ} (xs : Fin n → Fin v) (j : ℕ) : Block v :=
  ((population n).rewire xs).matchBlock (targetBits (counterDepth n + 1) j)

theorem weightBlock_correct {n v : ℕ} (xs : Fin n → Fin v) (j : ℕ) (hj : j ≤ n) (a : BitModels v) :
    (weightBlock xs j).Accepts a ↔ (∑ i, (a (xs i)).toNat) = j := by
  have hj' : j < 2 ^ (counterDepth n + 1) := by
    have hn := (counterDepth_bounds n).1
    rw [leaves_pow] at hn
    have hp : 0 < 2 ^ counterDepth n := by positivity
    rw [pow_succ]
    omega
  rw [weightBlock, Program.matchBlock_correct, Program.rewire_eval]
  constructor
  · intro h
    have hv := congrArg wordValue h
    rwa [population_correct, targetBits_value _ _ hj'] at hv
  · intro h
    apply wordValue_injective
    rw [population_correct, targetBits_value _ _ hj']
    exact h

theorem weightBlock_size {n v : ℕ} (xs : Fin n → Fin v) (j : ℕ) :
    (weightBlock xs j).aux ≤ 20 * n + 11 ∧
    (weightBlock xs j).formula.length ≤ 81 * n + 47 ∧
    Width 3 (weightBlock xs j).formula ∧ (weightBlock xs j).Deterministic := by
  have hg := population_gates n
  have hk := counter_width_bound n
  have hl := Program.matchBlock_length ((population n).rewire xs) (targetBits (counterDepth n + 1) j)
  refine ⟨hg, ?_, Program.matchBlock_width _ _, Program.matchBlock_deterministic _ _⟩
  change (weightBlock xs j).formula.length ≤ 4 * (population n).gates + (counterDepth n + 1) at hl
  omega

end QecReliability.SharedCircuit
