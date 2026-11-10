import CompletenessConverse
import EnumeratorExample

set_option autoImplicit false

/-!
# Weight enumerators as model counts of 3-CNF formulas

`normWeightFormula rows t` (on `normWeightVars rows t` variables) has the `2n` bits of `x` as
inputs and only gate-defined auxiliary variables: one XOR chain per row (the parity of `x`
against the row), one OR gate per qubit (its support bit) and a sequential counter over the
support bits; unit clauses say that every row parity is `0` and that the weight is exactly `t`.
`stabWeightFormula rows t` has one input `u_r` per row instead, each coordinate of `x = uH`
defined by an XOR chain over the rows containing it, then the same OR gates and counter.

* `gform_count`: a formula whose non-input variables are all defined by well-formed two-sided
  Tseitin gates has exactly one model per input vector satisfying the extra clauses
  (`extend_unique`: gate-OK assignments are determined by their inputs).
* `normWeightFormula_count`: model count `= weightCount (normalizer (symplectic n) (rowSpace rows)) t`.
* `stabWeightFormula_count`: model count `= 2 ^ (m - dim S) * weightCount (rowSpace rows) t`
  (`m = rows.length`, `S = rowSpace rows`; the factor is the size of the kernel of `u ↦ uH`).
* `*_width`: every clause has at most three literals; `*_vars`: every variable is below the
  declared count; `normWeightVars_eq`, `stabWeightVars_eq`: the counts are
  `(2t + 5) n + I + 2` and `(2t + 3) n + I + m + 2`, `I = rowIncidences rows`.
-/

namespace QecPhysical.Stabilizer.Enumerator

open Std.Sat
open QecReliability QecReliability.Binary QecReliability.SharedCircuit
open QecPhysical.Stabilizer.Completeness
open QecPhysical.Stabilizer.EnumeratorExample (pauliWeight weightCount)

/-! ## Gate-defined assignments are unique -/

theorem extend_unique (σ0 σ : Nat → Bool) (G : List Gate) (hA : Inputs G)
    (hok : ∀ g ∈ G, g.OK σ) (hbase : ∀ v, (∀ g ∈ G, g.out ≠ v) → σ0 v = σ v) :
    ∀ v, extend σ0 G v = σ v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rw [extend]
    split
    · rename_i g hg
      have hmem := List.mem_of_find?_eq_some hg
      have hout : g.out = v := by simpa using List.find?_some hg
      have hlt : g.a < v ∧ g.b < v := by rw [← hout]; exact hA g hmem
      rw [dite_eq_left hlt, ih _ hlt.1, ih _ hlt.2]
      have := hok g hmem
      unfold Gate.OK at this
      rw [← hout, this]
    · rename_i hn
      exact hbase v (fun g hg h => by
        have := List.find?_eq_none.mp hn g hg
        simp [h] at this)

def Cover (G : List Gate) (s t : Nat) : Prop := ∀ v, s ≤ v → v < t → ∃ g ∈ G, g.out = v

theorem Cover.append {G H : List Gate} {s t u : Nat} (hG : Cover G s t) (hH : Cover H t u) :
    Cover (G ++ H) s u := by
  intro v h1 h2
  by_cases hv : v < t
  · obtain ⟨g, hg, rfl⟩ := hG v h1 hv
    exact ⟨g, List.mem_append_left _ hg, rfl⟩
  · obtain ⟨g, hg, rfl⟩ := hH v (by omega) h2
    exact ⟨g, List.mem_append_right _ hg, rfl⟩

theorem chain_cover (acc : Nat) (vs : List Nat) (s : Nat) :
    Cover (chainGates acc vs s) s (s + vs.length) := by
  induction vs generalizing acc s with
  | nil => intro v h1 h2; simp at h2; omega
  | cons w vs ih =>
    intro v h1 h2
    by_cases hv : v = s
    · exact ⟨⟨s, .xor, acc, w⟩, by simp [chainGates], hv.symm⟩
    · obtain ⟨g, hg, rfl⟩ := ih s (s + 1) v (by omega) (by simp at h2; omega)
      exact ⟨g, by simp [chainGates, hg], rfl⟩

/-! ## Families of XOR chains -/

def chainsGates (F : Nat) : List (List Nat) → Nat → List Gate
  | [], _ => []
  | l :: ls, s => chainGates F l s ++ chainsGates F ls (s + l.length)

def chainsOuts (F : Nat) : List (List Nat) → Nat → List Nat
  | [], _ => []
  | l :: ls, s => chainOut F l s :: chainsOuts F ls (s + l.length)

def totalLen (ls : List (List Nat)) : Nat := (ls.map List.length).sum

theorem chains_wf (F : Nat) (ls : List (List Nat)) (s : Nat) (hF : F < s)
    (hls : ∀ l ∈ ls, ∀ v ∈ l, v < s) :
    Inj (chainsGates F ls s) ∧ Inputs (chainsGates F ls s) ∧
      InRange (chainsGates F ls s) s (s + totalLen ls) ∧
      Cover (chainsGates F ls s) s (s + totalLen ls) := by
  induction ls generalizing s with
  | nil => refine ⟨?_, ?_, ?_, ?_⟩ <;> intro v <;> simp [chainsGates, totalLen]
  | cons l ls ih =>
    obtain ⟨c1, c2, c3⟩ := chain_wf F l s hF (hls l (by simp))
    have c4 := chain_cover F l s
    obtain ⟨i1, i2, i3, i4⟩ := ih (s + l.length) (by omega) (fun l' hl' v hv => by
      have := hls l' (by simp [hl']) v hv; omega)
    have ht : totalLen (l :: ls) = l.length + totalLen ls := by simp [totalLen]
    rw [ht, ← Nat.add_assoc]
    exact ⟨Inj.append c1 i1 c3 i3, Inputs.append c2 i2,
      InRange.append c3 i3 (by omega) (by omega), Cover.append c4 i4⟩

theorem chainsOuts_iff (σ : Nat → Bool) (F : Nat) (ls : List (List Nat)) (s : Nat)
    (hok : ∀ g ∈ chainsGates F ls s, g.OK σ) :
    (∀ o ∈ chainsOuts F ls s, σ o = false) ↔ ∀ l ∈ ls, (σ F ^^ xorList (l.map σ)) = false := by
  induction ls generalizing s with
  | nil => simp [chainsOuts]
  | cons l ls ih =>
    have h1 := chain_value σ F l s (fun g hg => hok g (by simp [chainsGates, hg]))
    have h2 := ih (s + l.length) (fun g hg => hok g (by simp [chainsGates, hg]))
    simp only [chainsOuts, List.forall_mem_cons, h1, h2]

/-! ## A sequential counter over arbitrary input variables -/

/-- `gcol F T L C i j`: "at least `j` of the inputs `inp 0, …, inp (i-1)` are true". -/
def gcol (F T L C : Nat) : Nat → Nat → Nat
  | 0, 0 => T
  | 0, _ + 1 => F
  | _ + 1, 0 => T
  | i + 1, j + 1 => orOut L C i j

def gcounterGates (F T L C : Nat) (inp : Nat → Nat) (n : Nat) : List Gate :=
  (List.range n).flatMap fun i => (List.range (L + 1)).flatMap fun j =>
    [⟨andOut L C i j, .and, gcol F T L C i j, inp i⟩,
     ⟨orOut L C i j, .or, gcol F T L C i (j + 1), andOut L C i j⟩]

theorem gcol_lt (F T L C i j : Nat) (hF : F < C) (hT : T < C) (hj : j ≤ L + 1) :
    gcol F T L C i j < C + 2 * ((L + 1) * i + j) := by
  cases i with
  | zero => cases j <;> simp [gcol] <;> omega
  | succ i =>
    cases j with
    | zero => simp [gcol]; omega
    | succ j =>
      simp only [gcol, orOut]
      rw [Nat.mul_succ]
      omega

theorem gcounter_wf (F T L C : Nat) (inp : Nat → Nat) (n : Nat) (hF : F < C) (hT : T < C)
    (hinp : ∀ i < n, inp i < C) :
    Inj (gcounterGates F T L C inp n) ∧ Inputs (gcounterGates F T L C inp n) ∧
      InRange (gcounterGates F T L C inp n) C (C + 2 * ((L + 1) * n)) ∧
      Cover (gcounterGates F T L C inp n) C (C + 2 * ((L + 1) * n)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [gcounterGates, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at ha hb
    obtain ⟨i, hi, j, hj, rfl | rfl⟩ := ha <;> obtain ⟨i', hi', j', hj', rfl | rfl⟩ := hb <;>
      simp only [andOut, orOut] at hab
    · obtain ⟨rfl, rfl⟩ := lin_inj (by omega) (by omega)
        (by omega : (L + 1) * i + j = (L + 1) * i' + j')
      rfl
    · omega
    · omega
    · obtain ⟨rfl, rfl⟩ := lin_inj (by omega) (by omega)
        (by omega : (L + 1) * i + j = (L + 1) * i' + j')
      rfl
  · intro g hg
    simp only [gcounterGates, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    obtain ⟨i, hi, j, hj, rfl | rfl⟩ := hg
    · have := gcol_lt F T L C i j hF hT (by omega)
      have := hinp i hi
      simp only [andOut]
      omega
    · have h1 := gcol_lt F T L C i (j + 1) hF hT (by omega)
      cases i with
      | zero =>
        simp only [gcol, orOut, andOut]
        omega
      | succ i =>
        simp only [gcol, orOut, andOut] at h1 ⊢
        rw [Nat.mul_succ] at h1 ⊢
        omega
  · intro g hg
    simp only [gcounterGates, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    obtain ⟨i, hi, j, hj, rfl | rfl⟩ := hg
    · have := lin_lt (L := L) hi (Nat.lt_succ_iff.mp hj)
      simp only [andOut]; omega
    · have := lin_lt (L := L) hi (Nat.lt_succ_iff.mp hj)
      simp only [orOut]; omega
  · intro v h1 h2
    obtain ⟨q, r, hr, hv⟩ : ∃ q r, r < 2 ∧ v = C + 2 * q + r :=
      ⟨(v - C) / 2, (v - C) % 2, Nat.mod_lt _ (by omega), by omega⟩
    have hq : q < (L + 1) * n := by omega
    have hqd := Nat.div_add_mod q (L + 1)
    have hj : q % (L + 1) < L + 1 := Nat.mod_lt _ (by omega)
    have hi : q / (L + 1) < n := by
      by_contra hc
      have : (L + 1) * n ≤ (L + 1) * (q / (L + 1)) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hmem : ∀ g ∈ [(⟨andOut L C (q / (L + 1)) (q % (L + 1)), .and,
        gcol F T L C (q / (L + 1)) (q % (L + 1)), inp (q / (L + 1))⟩ : Gate),
        ⟨orOut L C (q / (L + 1)) (q % (L + 1)), .or, gcol F T L C (q / (L + 1)) (q % (L + 1) + 1),
          andOut L C (q / (L + 1)) (q % (L + 1))⟩], g ∈ gcounterGates F T L C inp n := by
      intro g hg
      simp only [gcounterGates, List.mem_flatMap, List.mem_range]
      exact ⟨_, hi, _, hj, hg⟩
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · refine ⟨_, hmem _ (List.mem_cons.mpr (Or.inl rfl)), ?_⟩
      simp only [andOut]; omega
    · refine ⟨_, hmem _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))), ?_⟩
      simp only [orOut]; omega

/-- Number of true inputs among `inp 0, …, inp (i-1)`. -/
def gcnt (σ : Nat → Bool) (inp : Nat → Nat) (i : Nat) : Nat :=
  ∑ k ∈ Finset.range i, if σ (inp k) then 1 else 0

theorem gcol_value (σ : Nat → Bool) (F T L C : Nat) (inp : Nat → Nat) (n : Nat)
    (hok : ∀ g ∈ gcounterGates F T L C inp n, g.OK σ) (hT : σ T = true) (hF : σ F = false) :
    ∀ i ≤ n, ∀ j ≤ L + 1, σ (gcol F T L C i j) = decide (j ≤ gcnt σ inp i) := by
  intro i
  induction i with
  | zero =>
    intro _ j _
    cases j with
    | zero => simp [gcol, hT]
    | succ j => simp [gcol, hF, gcnt]
  | succ i ih =>
    intro hi j hj
    cases j with
    | zero => simp [gcol, hT]
    | succ j =>
      have hmem : ∀ g ∈ [(⟨andOut L C i j, .and, gcol F T L C i j, inp i⟩ : Gate),
          ⟨orOut L C i j, .or, gcol F T L C i (j + 1), andOut L C i j⟩],
          g ∈ gcounterGates F T L C inp n := by
        intro g hg
        simp only [gcounterGates, List.mem_flatMap, List.mem_range]
        exact ⟨i, by omega, j, by omega, hg⟩
      have hand := hok _ (hmem ⟨andOut L C i j, .and, gcol F T L C i j, inp i⟩ (by simp))
      have hor := hok _ (hmem ⟨orOut L C i j, .or, gcol F T L C i (j + 1), andOut L C i j⟩
        (by simp))
      simp only [Gate.OK, GateOp.eval] at hand hor
      have h1 := ih (by omega) j (by omega)
      have h2 := ih (by omega) (j + 1) (by omega)
      simp only [gcol]
      rw [hor, hand, h1, h2]
      have hc : gcnt σ inp (i + 1) = gcnt σ inp i + (if σ (inp i) then 1 else 0) := by
        unfold gcnt
        rw [Finset.sum_range_succ]
      rw [hc]
      cases σ (inp i) <;> simp <;> omega

/-! ## Formulas whose auxiliary variables are all gate-defined -/

/-- Inputs `0, …, k-1`; `k` is the constant false, `k + 1` the constant true; gate clauses;
extra clauses `cs`. -/
def gform (k : Nat) (G : List Gate) (cs : List (CNF.Clause Nat)) : CNF Nat :=
  ⟨([[(k, false)], [(k + 1, true)]] ++ (G.flatMap Gate.clauses ++ cs)).toArray⟩

def baseOf {k : Nat} (b : Fin k → Bool) (v : Nat) : Bool :=
  if h : v < k then b ⟨v, h⟩ else decide (v = k + 1)

theorem gform_eval (k : Nat) (G : List Gate) (cs : List (CNF.Clause Nat)) (σ : Nat → Bool) :
    (gform k G cs).eval σ = true ↔
      σ k = false ∧ σ (k + 1) = true ∧ (∀ g ∈ G, g.OK σ) ∧ ∀ c ∈ cs, c.eval σ = true := by
  rw [gform, cnf_eval_toArray, List.all_eq_true]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [CNF.Clause.eval] using h [(k, false)] (by simp)
    · simpa [CNF.Clause.eval] using h [(k + 1, true)] (by simp)
    · intro g hg
      exact Gate.ok_of_clauses σ g (fun c hc => h c (by
        simp only [List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inl ⟨g, hg, hc⟩)))
    · intro c hc
      exact h c (by simp [hc])
  · rintro ⟨h1, h2, h3, h4⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_flatMap] at hc
    rcases hc with (rfl | rfl) | ⟨g, hg, hcg⟩ | hc
    · simp [CNF.Clause.eval, h1]
    · simp [CNF.Clause.eval, h2]
    · exact Gate.clauses_sat σ g (h3 g hg) c hcg
    · exact h4 c hc

theorem gform_width (k : Nat) (G : List Gate) (cs : List (CNF.Clause Nat))
    (hcs : ∀ c ∈ cs, c.length ≤ 3) : ∀ c ∈ (gform k G cs).clauses, c.length ≤ 3 := by
  intro c hc
  simp only [gform, List.mem_toArray, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatMap] at hc
  rcases hc with (rfl | rfl) | ⟨g, -, hcg⟩ | hc
  · simp
  · simp
  · obtain ⟨t, op, a, b⟩ := g
    cases op <;> simp only [Completeness.Gate.clauses, List.mem_cons, List.not_mem_nil, or_false] at hcg <;>
      rcases hcg with rfl | rfl | rfl | rfl <;> simp
  · exact hcs c hc

section Generic

variable (k N : Nat) (G : List Gate) (cs : List (CNF.Clause Nat))

/-- **Model count of a gate-defined formula.** If the gates define exactly the variables
`k + 2, …, N - 1`, the models on `N` variables correspond to the input vectors `b` whose
extension satisfies the extra clauses. -/
theorem gform_count (hk : k + 2 ≤ N) (hI : Inj G) (hA : Inputs G) (hR : InRange G (k + 2) N)
    (hC : Cover G (k + 2) N) :
    (Finset.univ.filter (fun a : Fin N → Bool =>
        (gform k G cs).eval (fun v => if h : v < N then a ⟨v, h⟩ else false) = true)).card =
      (Finset.univ.filter (fun b : Fin k → Bool =>
        ∀ c ∈ cs, c.eval (extend (baseOf b) G) = true)).card := by
  have hlift : ∀ b : Fin k → Bool,
      (fun v => if h : v < N then extend (baseOf b) G v else false) = extend (baseOf b) G := by
    intro b
    funext v
    split_ifs with h
    · rfl
    · rw [extend_base _ _ _ (fun g hg => by have := hR g hg; omega)]
      unfold baseOf
      rw [dite_eq_right (by omega)]
      exact (decide_eq_false (by omega)).symm
  have hmodel : ∀ a : Fin N → Bool,
      (gform k G cs).eval (fun v => if h : v < N then a ⟨v, h⟩ else false) = true →
      extend (baseOf (fun j : Fin k => a ⟨j.val, by have := j.isLt; omega⟩)) G =
        (fun v => if h : v < N then a ⟨v, h⟩ else false) := by
    intro a ha
    obtain ⟨h1, h2, h3, -⟩ := (gform_eval k G cs _).mp ha
    funext v
    refine extend_unique _ _ G hA h3 ?_ v
    intro v hv
    show baseOf _ v = (if h : v < N then a ⟨v, h⟩ else false)
    by_cases hvk : v < k
    · unfold baseOf
      rw [dite_eq_left hvk, dite_eq_left (show v < N by omega)]
    · unfold baseOf
      rw [dite_eq_right hvk]
      by_cases hv1 : v = k + 1
      · subst hv1; rw [h2]; simp
      · by_cases hv0 : v = k
        · subst hv0; rw [h1]; simp
        · by_cases hvN : v < N
          · obtain ⟨g, hg, hgv⟩ := hC v (by omega) hvN
            exact absurd hgv (hv g hg)
          · rw [dite_eq_right hvN]
            exact decide_eq_false hv1
  refine Finset.card_bij' (fun a _ => fun j : Fin k => a ⟨j.val, by have := j.isLt; omega⟩)
    (fun b _ => fun v : Fin N => extend (baseOf b) G v) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hmodel a ha.2]
    exact ((gform_eval k G cs _).mp ha.2).2.2.2
  · intro b hb
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hlift b]
    refine (gform_eval k G cs _).mpr ⟨?_, ?_, extend_ok _ G hI hA, hb.2⟩
    · rw [extend_base _ _ _ (fun g hg => by have := hR g hg; omega)]
      simp [baseOf]
    · rw [extend_base _ _ _ (fun g hg => by have := hR g hg; omega)]
      simp [baseOf]
  · intro a ha
    funext v
    have := congrFun (hmodel a (Finset.mem_filter.mp ha).2) v.val
    simp only [v.isLt, dite_true] at this
    exact this
  · intro b _
    funext j
    show extend (baseOf b) G j.val = b j
    rw [extend_base _ _ _ (fun g hg => by have := hR g hg; omega)]
    unfold baseOf
    rw [dite_eq_left j.isLt]

end Generic

/-! ## Bits and binary values -/

theorem ofBool_bb (y : Bit) : ofBool (bb y) = y := by revert y; decide

theorem bb_or_iff (y y' : Bit) : ((bb y || bb y') = true) ↔ (y ≠ 0 ∨ y' ≠ 0) := by
  revert y y'; decide

/-! ## The normalizer enumerator -/

section Normalizer
variable {n : ℕ}

/-- Variable of the coordinate of `x` that a row coordinate pairs with
(`x.1 i` is variable `i`, `x.2 i` is variable `n + i`). -/
def nSel : PauliCoord n → Nat
  | .inl i => n + i.val
  | .inr i => i.val

def nLists (rows : List (List (PauliCoord n))) : List (List Nat) := rows.map (·.map nSel)

/-- Support bits: variable `S + i` is `p i ∨ q i` (the two coordinates of qubit `i`). -/
def supGates (n S : Nat) (p q : Nat → Nat) : List Gate :=
  List.ofFn (fun i : Fin n => (⟨S + i.val, .or, p i.val, q i.val⟩ : Gate))

theorem sup_wf (n S : Nat) (p q : Nat → Nat) (hp : ∀ i < n, p i < S) (hq : ∀ i < n, q i < S) :
    Inj (supGates n S p q) ∧ Inputs (supGates n S p q) ∧ InRange (supGates n S p q) S (S + n) ∧
      Cover (supGates n S p q) S (S + n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [supGates, List.mem_ofFn] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    have : i = j := Fin.ext (by simp only at hab; omega)
    subst this; rfl
  · intro g hg
    simp only [supGates, List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    have := hp i i.isLt
    have := hq i i.isLt
    simp only; omega
  · intro g hg
    simp only [supGates, List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    simp only; omega
  · intro v h1 h2
    exact ⟨_, List.mem_ofFn.mpr ⟨⟨v - S, by omega⟩, rfl⟩, by simp only; omega⟩

variable (rows : List (List (PauliCoord n))) (t : ℕ)

def nSupStart : Nat := 2 * n + 2 + totalLen (nLists rows)
def nCtrStart : Nat := nSupStart rows + n

/-- Number of variables of `normWeightFormula rows t`. -/
def normWeightVars : Nat := nCtrStart rows + 2 * ((t + 1) * n)

def normGates : List Gate :=
  chainsGates (2 * n) (nLists rows) (2 * n + 2) ++
  (supGates n (nSupStart rows) (fun i => i) (fun i => n + i) ++
   gcounterGates (2 * n) (2 * n + 1) t (nCtrStart rows) (fun i => nSupStart rows + i) n)

def normUnits : List (CNF.Clause Nat) :=
  (chainsOuts (2 * n) (nLists rows) (2 * n + 2)).map (fun o => [(o, false)]) ++
  [[(gcol (2 * n) (2 * n + 1) t (nCtrStart rows) n t, true)],
   [(gcol (2 * n) (2 * n + 1) t (nCtrStart rows) n (t + 1), false)]]

/-- **The normalizer weight formula.** Inputs `x.1 i = i`, `x.2 i = n + i`; constants `2n`
(false) and `2n + 1` (true); one XOR chain per row (from `2n + 2` on), one OR gate per qubit
(from `nSupStart`), a sequential counter over the support bits (from `nCtrStart`); unit
clauses: every row parity is `0`, the counter says "at least `t`" and not "at least `t + 1`". -/
def normWeightFormula : CNF Nat := gform (2 * n) (normGates rows t) (normUnits rows t)

theorem normGates_wf :
    Inj (normGates rows t) ∧ Inputs (normGates rows t) ∧
      InRange (normGates rows t) (2 * n + 2) (normWeightVars rows t) ∧
      Cover (normGates rows t) (2 * n + 2) (normWeightVars rows t) := by
  have hX := chains_wf (2 * n) (nLists rows) (2 * n + 2) (by omega) (fun l hl v hv => by
    simp only [nLists, List.mem_map] at hl
    obtain ⟨r, -, rfl⟩ := hl
    simp only [List.mem_map] at hv
    obtain ⟨c, -, rfl⟩ := hv
    cases c with
    | inl i => simp only [nSel]; have := i.isLt; omega
    | inr i => simp only [nSel]; have := i.isLt; omega)
  have e1 : 2 * n + 2 + totalLen (nLists rows) = nSupStart rows := rfl
  rw [e1] at hX
  have hS := sup_wf n (nSupStart rows) (fun i => i) (fun i => n + i)
    (fun i hi => by simp only [nSupStart]; omega) (fun i hi => by simp only [nSupStart]; omega)
  have hK := gcounter_wf (2 * n) (2 * n + 1) t (nCtrStart rows) (fun i => nSupStart rows + i) n
    (by simp [nCtrStart, nSupStart]; omega) (by simp [nCtrStart, nSupStart]; omega)
    (fun i hi => by simp only [nCtrStart]; omega)
  have e2 : nSupStart rows + n = nCtrStart rows := rfl
  rw [e2] at hS
  have r2 := InRange.append hS.2.2.1 hK.2.2.1 (by simp [nCtrStart]) (by omega)
  have r1 := InRange.append hX.2.2.1 r2 (by simp [nSupStart]) (by simp only [nCtrStart]; omega)
  refine ⟨Inj.append hX.1 (Inj.append hS.1 hK.1 hS.2.2.1 hK.2.2.1) hX.2.2.1 r2,
    Inputs.append hX.2.1 (Inputs.append hS.2.1 hK.2.1), r1,
    Cover.append hX.2.2.2 (Cover.append hS.2.2.2 hK.2.2.2)⟩

/-- The Pauli vector of an input assignment. -/
def pOf (b : Fin (2 * n) → Bool) : Pauli n :=
  (fun i => ofBool (b ⟨i.val, by have := i.isLt; omega⟩),
   fun i => ofBool (b ⟨n + i.val, by have := i.isLt; omega⟩))

def bOf (x : Pauli n) : Fin (2 * n) → Bool := fun v =>
  if h : v.val < n then bb (x.1 ⟨v.val, h⟩) else bb (x.2 ⟨v.val - n, by have := v.isLt; omega⟩)

omit rows t in
theorem pOf_bOf (x : Pauli n) : pOf (bOf x) = x := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp [pOf, bOf, ofBool_bb]
  · simp [pOf, bOf, ofBool_bb]

omit rows t in
theorem bOf_pOf (b : Fin (2 * n) → Bool) : bOf (pOf b) = b := by
  funext v
  unfold bOf pOf
  split_ifs with h
  · simp
  · simp only [bb_ofBool]
    congr 1
    ext
    simp only
    omega

theorem normUnits_iff (b : Fin (2 * n) → Bool) :
    (∀ c ∈ normUnits rows t, c.eval (extend (baseOf b) (normGates rows t)) = true) ↔
      pOf b ∈ normalizer (symplectic n) (rowSpace rows) ∧ pauliWeight (pOf b) = t := by
  set G := normGates rows t with hG
  set σ := extend (baseOf b) G with hσ
  obtain ⟨hI, hA, hR, -⟩ := normGates_wf rows t
  have hok : ∀ g ∈ G, g.OK σ := extend_ok _ G hI hA
  have hbase : ∀ v < 2 * n + 2, σ v = baseOf b v := fun v hv =>
    extend_base _ _ _ (fun g hg => by have := hR g hg; omega)
  have sx : ∀ v (h : v < 2 * n), σ v = b ⟨v, h⟩ := fun v h => by
    rw [hbase v (by omega)]; unfold baseOf; rw [dite_eq_left h]
  have sF : σ (2 * n) = false := by rw [hbase _ (by omega)]; simp [baseOf]
  have sT : σ (2 * n + 1) = true := by rw [hbase _ (by omega)]; simp [baseOf]
  set x := pOf b with hx
  have hsel : ∀ c, σ (nSel c) = bb (Sum.elim (fun i => x.2 i) (fun i => x.1 i) c) := by
    intro c
    cases c with
    | inl i =>
      simp only [nSel, Sum.elim_inl]
      rw [sx _ (by have := i.isLt; omega)]
      simp [x, pOf]
    | inr i =>
      simp only [nSel, Sum.elim_inr]
      rw [sx _ (by have := i.isLt; omega)]
      simp [x, pOf]
  have mX : ∀ g ∈ chainsGates (2 * n) (nLists rows) (2 * n + 2), g ∈ G := fun g hg => by
    simp [hG, normGates, hg]
  have mS : ∀ g ∈ supGates n (nSupStart rows) (fun i => i) (fun i => n + i), g ∈ G := fun g hg => by
    simp [hG, normGates, hg]
  have mK : ∀ g ∈ gcounterGates (2 * n) (2 * n + 1) t (nCtrStart rows)
      (fun i => nSupStart rows + i) n, g ∈ G := fun g hg => by
    simp [hG, normGates, hg]
  -- rows
  have hrow : (∀ o ∈ chainsOuts (2 * n) (nLists rows) (2 * n + 2), σ o = false) ↔
      x ∈ normalizer (symplectic n) (rowSpace rows) := by
    rw [chainsOuts_iff σ _ _ _ (fun g hg => hok g (mX g hg)), sF, mem_normalizer_rows]
    simp only [nLists, List.forall_mem_map, Bool.false_xor]
    refine forall_congr' fun r => imp_congr_right fun _ => ?_
    rw [List.map_map]
    have hfun : (σ ∘ nSel) = (bb ∘ Sum.elim (fun i => x.2 i) (fun i => x.1 i)) := by
      funext c; exact hsel c
    rw [hfun, ← List.map_map, ← bb_sum, ← symplectic_decodeRow, bb_eq_false_iff]
  -- weight
  have hsup : ∀ i : Fin n, σ (nSupStart rows + i.val) = (bb (x.1 i) || bb (x.2 i)) := by
    intro i
    have := hok _ (mS _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    simp only [Gate.OK, GateOp.eval] at this
    rw [this, sx _ (by have := i.isLt; omega), sx _ (by have := i.isLt; omega)]
    simp [x, pOf]
  have hcnt : gcnt σ (fun i => nSupStart rows + i) n = pauliWeight x := by
    unfold gcnt pauliWeight
    rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range
      (fun k => if σ (nSupStart rows + k) = true then 1 else 0)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hsup i]
    exact if_congr (bb_or_iff _ _) rfl rfl
  have hv1 := gcol_value σ (2 * n) (2 * n + 1) t (nCtrStart rows) (fun i => nSupStart rows + i) n
    (fun g hg => hok g (mK g hg)) sT sF n le_rfl t (by omega)
  have hv2 := gcol_value σ (2 * n) (2 * n + 1) t (nCtrStart rows) (fun i => nSupStart rows + i) n
    (fun g hg => hok g (mK g hg)) sT sF n le_rfl (t + 1) le_rfl
  have e : ∀ o p, CNF.Clause.eval σ [(o, p)] = true ↔ σ o = p := by
    intro o p; cases p <;> simp [CNF.Clause.eval]
  simp only [normUnits, List.forall_mem_append, List.forall_mem_map, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, e]
  rw [hrow, hv1, hv2, hcnt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h2 h3
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_, ?_⟩
    · simp only [decide_eq_true_eq]; omega
    · simp only [decide_eq_false_iff_not]; omega

/-- **Normalizer weight enumerator as a model count.** The number of assignments of the
`normWeightVars rows t` declared variables satisfying `normWeightFormula rows t` equals the
number of elements of the normalizer `N(rowSpace rows)` of Pauli weight `t`. -/
theorem normWeightFormula_count :
    (Finset.univ.filter (fun a : Fin (normWeightVars rows t) → Bool =>
      (normWeightFormula rows t).eval
        (fun v => if h : v < normWeightVars rows t then a ⟨v, h⟩ else false) = true)).card =
      weightCount (normalizer (symplectic n) (rowSpace rows)) t := by
  classical
  obtain ⟨hI, hA, hR, hC⟩ := normGates_wf rows t
  rw [normWeightFormula, gform_count (2 * n) (normWeightVars rows t) _ _
    (by simp [normWeightVars, nCtrStart, nSupStart]; omega) hI hA hR hC]
  simp_rw [normUnits_iff rows t]
  unfold weightCount
  refine Finset.card_bij' (fun b _ => pOf b) (fun x _ => bOf x) ?_ ?_ ?_ ?_
  · intro b hb
    simpa using hb
  · intro x hx
    simpa [pOf_bOf] using hx
  · intro b _
    exact bOf_pOf b
  · intro x _
    exact pOf_bOf x

/-- Every clause of the normalizer weight formula has at most three literals. -/
theorem normWeightFormula_width :
    ∀ c ∈ (normWeightFormula rows t).clauses, c.length ≤ 3 :=
  gform_width _ _ _ (fun c hc => by
    simp only [normUnits, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with ⟨o, -, rfl⟩ | rfl | rfl <;> simp)

end Normalizer

/-! ## Linear algebra: counting through a linear map -/

theorem card_filter_comp_linear {V W : Type} [AddCommGroup V] [Module Bit V] [Fintype V]
    [DecidableEq V] [AddCommGroup W] [Module Bit W] [Fintype W] [DecidableEq W]
    (φ : V →ₗ[Bit] W) (P : W → Prop) [DecidablePred P] [DecidablePred (· ∈ LinearMap.range φ)] :
    (Finset.univ.filter (fun u => P (φ u))).card =
      (Finset.univ.filter (fun u => φ u = 0)).card *
        (Finset.univ.filter (fun x => x ∈ LinearMap.range φ ∧ P x)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := φ)
    (t := Finset.univ.filter (fun x => x ∈ LinearMap.range φ ∧ P x))
    (fun u hu => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu ⊢
      exact ⟨LinearMap.mem_range_self φ u, hu⟩)]
  rw [Finset.sum_const_nat (m := (Finset.univ.filter (fun u => φ u = 0)).card), mul_comm]
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨⟨u0, rfl⟩, hP⟩ := hx
  refine Finset.card_bij' (fun u _ => u - u0) (fun z _ => z + u0) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [map_sub, hu.2, sub_self]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [map_add, hz, zero_add]
    exact ⟨hP, rfl⟩
  · intro u _; exact sub_add_cancel u u0
  · intro z _; exact add_sub_cancel_right z u0

theorem card_ker_eq {m : ℕ} {W : Type} [AddCommGroup W] [Module Bit W] [DecidableEq W]
    (φ : (Fin m → Bit) →ₗ[Bit] W) :
    (Finset.univ.filter (fun u => φ u = 0)).card = 2 ^ (m - Module.finrank Bit (LinearMap.range φ)) := by
  classical
  rw [← Fintype.card_subtype]
  have h1 : Fintype.card {u // φ u = 0} = Fintype.card (LinearMap.ker φ) :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun u => LinearMap.mem_ker.symm))
  rw [h1, Module.card_eq_pow_finrank (K := Bit), ZMod.card]
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  rw [Module.finrank_fin_fun] at h2
  congr 1
  omega

/-! ## The stabilizer enumerator -/

/-- Number of occurrences of the coordinate `c` in a sparse row. -/
def coordCount {n : ℕ} (c : PauliCoord n) (row : List (PauliCoord n)) : ℕ :=
  (row.map fun c' => if c' = c then 1 else 0).sum

theorem coordCount_cons {n : ℕ} (c c' : PauliCoord n) (row : List (PauliCoord n)) :
    coordCount c (c' :: row) = (if c' = c then 1 else 0) + coordCount c row := by
  simp only [coordCount, List.map_cons, List.sum_cons]

theorem decodeRow_fst {n : ℕ} (row : List (PauliCoord n)) (i : Fin n) :
    (decodeRow row).1 i = (coordCount (.inl i) row : Bit) := by
  induction row with
  | nil => simp [decodeRow, coordCount]
  | cons c row ih =>
    have hd : decodeRow (c :: row) = coordPauli c + decodeRow row := by simp [decodeRow]
    rw [hd, Prod.fst_add, Pi.add_apply, ih, coordCount_cons, Nat.cast_add]
    congr 1
    cases c with
    | inl j =>
      rcases eq_or_ne j i with rfl | h
      · simp [coordPauli, xUnit]
      · simp [coordPauli, xUnit, Pi.single_apply, h, Ne.symm h]
    | inr j => simp [coordPauli, zUnit]

theorem decodeRow_snd {n : ℕ} (row : List (PauliCoord n)) (i : Fin n) :
    (decodeRow row).2 i = (coordCount (.inr i) row : Bit) := by
  induction row with
  | nil => simp [decodeRow, coordCount]
  | cons c row ih =>
    have hd : decodeRow (c :: row) = coordPauli c + decodeRow row := by simp [decodeRow]
    rw [hd, Prod.snd_add, Pi.add_apply, ih, coordCount_cons, Nat.cast_add]
    congr 1
    cases c with
    | inl j => simp [coordPauli, xUnit]
    | inr j =>
      rcases eq_or_ne j i with rfl | h
      · simp [coordPauli, zUnit]
      · simp [coordPauli, zUnit, Pi.single_apply, h, Ne.symm h]

theorem xorList_replicate (k : ℕ) (β : Bool) :
    xorList (List.replicate k β) = bb ((k : Bit) * ofBool β) := by
  induction k with
  | zero => simp [xorList]
  | succ k ih =>
    rw [List.replicate_succ, xorList, ih]
    push_cast
    rw [add_mul, one_mul, bb_add, bb_ofBool, Bool.xor_comm]

theorem xorList_occ {m : ℕ} (σ : Nat → Bool) (b : Fin m → Bool) (hσ : ∀ r : Fin m, σ r.val = b r)
    (k : Fin m → ℕ) (L : List (Fin m)) :
    xorList ((L.flatMap fun r => List.replicate (k r) r.val).map σ) =
      bb ((L.map fun r => (k r : Bit) * ofBool (b r)).sum) := by
  induction L with
  | nil => simp [xorList]
  | cons r L ih =>
    rw [List.flatMap_cons, List.map_append, xorList_append, ih, List.map_replicate, hσ,
      xorList_replicate, List.map_cons, List.sum_cons, bb_add]

theorem chainOut_lt (acc : Nat) (l : List Nat) (s : Nat) (h : acc < s) :
    chainOut acc l s < s + l.length := by
  induction l generalizing acc s with
  | nil => simpa [chainOut] using h
  | cons v l ih =>
    have := ih s (s + 1) (by omega)
    simp only [chainOut, List.length_cons]
    omega

theorem chainsOuts_get (F : Nat) (ls : List (List Nat)) (s : Nat) :
    ∀ i (hi : i < ls.length), ∃ s', (chainsOuts F ls s).getD i 0 = chainOut F ls[i] s' ∧
      (∀ g ∈ chainGates F ls[i] s', g ∈ chainsGates F ls s) ∧ s ≤ s' ∧
      s' + ls[i].length ≤ s + totalLen ls := by
  induction ls generalizing s with
  | nil => intro i hi; simp at hi
  | cons l ls ih =>
    intro i hi
    have ht : totalLen (l :: ls) = l.length + totalLen ls := by simp [totalLen]
    cases i with
    | zero =>
      refine ⟨s, by simp [chainsOuts], fun g hg => by
        simp only [List.getElem_cons_zero] at hg; simp [chainsGates, hg], le_rfl, ?_⟩
      simp only [List.getElem_cons_zero, ht]; omega
    | succ i =>
      obtain ⟨s', h1, h2, h3, h4⟩ := ih (s + l.length) i (by simp at hi; omega)
      refine ⟨s', by simpa [chainsOuts] using h1, fun g hg => by simp [chainsGates, h2 g hg],
        by omega, ?_⟩
      simp only [List.getElem_cons_succ, ht]; omega

section Stabilizer
variable {n : ℕ} (rows : List (List (PauliCoord n))) (t : ℕ)

/-- Row variables `u_r` (`r < m`) of the rows containing the coordinate `c`, with
multiplicity. -/
def occ (c : PauliCoord n) : List Nat :=
  (List.finRange rows.length).flatMap fun r => List.replicate (coordCount c (rows.get r)) r.val

def sLists : List (List Nat) :=
  (List.finRange n).map (fun i => occ rows (.inl i)) ++
    (List.finRange n).map (fun i => occ rows (.inr i))

theorem sLists_length : (sLists rows).length = 2 * n := by simp [sLists]; omega

theorem sLists_fst (i : Fin n) (h : i.val < (sLists rows).length) :
    (sLists rows)[i.val] = occ rows (.inl i) := by
  simp [sLists, List.getElem_append_left]

theorem sLists_snd (i : Fin n) (h : n + i.val < (sLists rows).length) :
    (sLists rows)[n + i.val] = occ rows (.inr i) := by
  simp [sLists, List.getElem_append_right]

/-- Variable holding coordinate `j` of `x = uH` (`j < n`: `x.1 j`; `n + j`: `x.2 j`). -/
def xVar (j : Nat) : Nat := (chainsOuts rows.length (sLists rows) (rows.length + 2)).getD j 0

def sSupStart : Nat := rows.length + 2 + totalLen (sLists rows)
def sCtrStart : Nat := sSupStart rows + n

/-- Number of variables of `stabWeightFormula rows t`. -/
def stabWeightVars : Nat := sCtrStart rows + 2 * ((t + 1) * n)

def stabGates : List Gate :=
  chainsGates rows.length (sLists rows) (rows.length + 2) ++
  (supGates n (sSupStart rows) (xVar rows) (fun i => xVar rows (n + i)) ++
   gcounterGates rows.length (rows.length + 1) t (sCtrStart rows) (fun i => sSupStart rows + i) n)

def stabUnits : List (CNF.Clause Nat) :=
  [[(gcol rows.length (rows.length + 1) t (sCtrStart rows) n t, true)],
   [(gcol rows.length (rows.length + 1) t (sCtrStart rows) n (t + 1), false)]]

/-- **The stabilizer weight formula.** Inputs `u_r = r` (`r < m = rows.length`); constants `m`
(false) and `m + 1` (true); one XOR chain per coordinate of `x = uH` over the rows containing
it (from `m + 2` on), one OR gate per qubit (from `sSupStart`), a sequential counter over the
support bits (from `sCtrStart`); unit clauses: "at least `t`" and not "at least `t + 1`". -/
def stabWeightFormula : CNF Nat := gform rows.length (stabGates rows t) (stabUnits rows t)

theorem xVar_spec (j : Nat) (hj : j < (sLists rows).length) :
    ∃ s', xVar rows j = chainOut rows.length (sLists rows)[j] s' ∧
      (∀ g ∈ chainGates rows.length (sLists rows)[j] s',
        g ∈ chainsGates rows.length (sLists rows) (rows.length + 2)) ∧
      xVar rows j < sSupStart rows := by
  obtain ⟨s', h1, h2, h3, h4⟩ := chainsOuts_get rows.length (sLists rows) (rows.length + 2) j hj
  refine ⟨s', h1, h2, ?_⟩
  rw [xVar, h1]
  have := chainOut_lt rows.length (sLists rows)[j] s' (by omega)
  unfold sSupStart
  omega

theorem stabGates_wf :
    Inj (stabGates rows t) ∧ Inputs (stabGates rows t) ∧
      InRange (stabGates rows t) (rows.length + 2) (stabWeightVars rows t) ∧
      Cover (stabGates rows t) (rows.length + 2) (stabWeightVars rows t) := by
  have hX := chains_wf rows.length (sLists rows) (rows.length + 2) (by omega)
    (fun l hl v hv => by
      simp only [sLists, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hl
      rcases hl with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      · simp only [occ, List.mem_flatMap, List.mem_finRange, true_and, List.mem_replicate] at hv
        obtain ⟨r, -, rfl⟩ := hv
        have := r.isLt
        omega)
  have e1 : rows.length + 2 + totalLen (sLists rows) = sSupStart rows := rfl
  rw [e1] at hX
  have hS := sup_wf n (sSupStart rows) (xVar rows) (fun i => xVar rows (n + i))
    (fun i hi => by
      obtain ⟨_, -, -, h⟩ := xVar_spec rows i (by rw [sLists_length]; omega); exact h)
    (fun i hi => by
      obtain ⟨_, -, -, h⟩ := xVar_spec rows (n + i) (by rw [sLists_length]; omega); exact h)
  have hK := gcounter_wf rows.length (rows.length + 1) t (sCtrStart rows)
    (fun i => sSupStart rows + i) n
    (by simp [sCtrStart, sSupStart]; omega) (by simp [sCtrStart, sSupStart]; omega)
    (fun i hi => by simp only [sCtrStart]; omega)
  have e2 : sSupStart rows + n = sCtrStart rows := rfl
  rw [e2] at hS
  have r2 := InRange.append hS.2.2.1 hK.2.2.1 (by simp [sCtrStart]) (by omega)
  have r1 := InRange.append hX.2.2.1 r2 (by simp [sSupStart]) (by simp only [sCtrStart]; omega)
  refine ⟨Inj.append hX.1 (Inj.append hS.1 hK.1 hS.2.2.1 hK.2.2.1) hX.2.2.1 r2,
    Inputs.append hX.2.1 (Inputs.append hS.2.1 hK.2.1), r1,
    Cover.append hX.2.2.2 (Cover.append hS.2.2.2 hK.2.2.2)⟩

/-- The linear map `u ↦ uH = Σ_r u_r · row_r`; its range is `rowSpace rows`. -/
noncomputable def genMap : (Fin rows.length → Bit) →ₗ[Bit] Pauli n :=
  Fintype.linearCombination Bit (fun r : Fin rows.length => decodeRow (rows.get r))

theorem genMap_range : LinearMap.range (genMap rows) = rowSpace rows := by
  rw [genMap, Fintype.range_linearCombination, rowSpace]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨rows.get r, List.get_mem rows r, rfl⟩
  · rintro ⟨row, hrow, rfl⟩
    obtain ⟨r, rfl⟩ := List.mem_iff_get.mp hrow
    exact ⟨r, rfl⟩

theorem genMap_fst (u : Fin rows.length → Bit) (i : Fin n) :
    (genMap rows u).1 i = ∑ r, ((coordCount (.inl i) (rows.get r) : ℕ) : Bit) * u r := by
  rw [genMap, Fintype.linearCombination_apply, Prod.fst_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, decodeRow_fst, mul_comm]

theorem genMap_snd (u : Fin rows.length → Bit) (i : Fin n) :
    (genMap rows u).2 i = ∑ r, ((coordCount (.inr i) (rows.get r) : ℕ) : Bit) * u r := by
  rw [genMap, Fintype.linearCombination_apply, Prod.snd_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, decodeRow_snd, mul_comm]

def uOf (b : Fin rows.length → Bool) : Fin rows.length → Bit := fun r => ofBool (b r)

theorem stabUnits_iff (b : Fin rows.length → Bool) :
    (∀ c ∈ stabUnits rows t, c.eval (extend (baseOf b) (stabGates rows t)) = true) ↔
      pauliWeight (genMap rows (uOf rows b)) = t := by
  set G := stabGates rows t with hG
  set σ := extend (baseOf b) G with hσ
  obtain ⟨hI, hA, hR, -⟩ := stabGates_wf rows t
  have hok : ∀ g ∈ G, g.OK σ := extend_ok _ G hI hA
  have hbase : ∀ v < rows.length + 2, σ v = baseOf b v := fun v hv =>
    extend_base _ _ _ (fun g hg => by have := hR g hg; omega)
  have su : ∀ r : Fin rows.length, σ r.val = b r := fun r => by
    rw [hbase _ (by have := r.isLt; omega)]; unfold baseOf; rw [dite_eq_left r.isLt]
  have sF : σ rows.length = false := by rw [hbase _ (by omega)]; simp [baseOf]
  have sT : σ (rows.length + 1) = true := by rw [hbase _ (by omega)]; simp [baseOf]
  set x := genMap rows (uOf rows b) with hx
  have mX : ∀ g ∈ chainsGates rows.length (sLists rows) (rows.length + 2), g ∈ G := fun g hg => by
    simp [hG, stabGates, hg]
  have mS : ∀ g ∈ supGates n (sSupStart rows) (xVar rows) (fun i => xVar rows (n + i)),
      g ∈ G := fun g hg => by simp [hG, stabGates, hg]
  have mK : ∀ g ∈ gcounterGates rows.length (rows.length + 1) t (sCtrStart rows) (fun i => sSupStart rows + i) n,
      g ∈ G := fun g hg => by simp [hG, stabGates, hg]
  -- the coordinates of `x`
  have hocc : ∀ (c : PauliCoord n) (s' : Nat),
      (∀ g ∈ chainGates rows.length (occ rows c) s', g ∈ G) →
      σ (chainOut rows.length (occ rows c) s') =
        bb (∑ r : Fin rows.length, ((coordCount c (rows.get r) : ℕ) : Bit) * uOf rows b r) := by
    intro c s' hmem
    rw [chain_value σ _ _ _ (fun g hg => hok g (hmem g hg)), sF, Bool.false_xor, occ,
      xorList_occ σ b su, Fin.sum_univ_def]
    rfl
  have hx1 : ∀ i : Fin n, σ (xVar rows i.val) = bb (x.1 i) := by
    intro i
    obtain ⟨s', h1, h2, -⟩ := xVar_spec rows i.val (by rw [sLists_length]; have := i.isLt; omega)
    rw [h1]
    simp only [sLists_fst rows i] at h2 ⊢
    rw [hocc _ s' (fun g hg => mX g (h2 g hg)), hx, genMap_fst]
  have hx2 : ∀ i : Fin n, σ (xVar rows (n + i.val)) = bb (x.2 i) := by
    intro i
    obtain ⟨s', h1, h2, -⟩ := xVar_spec rows (n + i.val) (by rw [sLists_length]; have := i.isLt; omega)
    rw [h1]
    simp only [sLists_snd rows i] at h2 ⊢
    rw [hocc _ s' (fun g hg => mX g (h2 g hg)), hx, genMap_snd]
  -- weight
  have hsup : ∀ i : Fin n, σ (sSupStart rows + i.val) = (bb (x.1 i) || bb (x.2 i)) := by
    intro i
    have := hok _ (mS _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
    simp only [Gate.OK, GateOp.eval] at this
    rw [this, hx1, hx2]
  have hcnt : gcnt σ (fun i => sSupStart rows + i) n = pauliWeight x := by
    unfold gcnt pauliWeight
    rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range
      (fun k => if σ (sSupStart rows + k) = true then 1 else 0)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hsup i]
    exact if_congr (bb_or_iff _ _) rfl rfl
  have hv1 := gcol_value σ rows.length (rows.length + 1) t (sCtrStart rows) (fun i => sSupStart rows + i) n
    (fun g hg => hok g (mK g hg)) sT sF n le_rfl t (by omega)
  have hv2 := gcol_value σ rows.length (rows.length + 1) t (sCtrStart rows) (fun i => sSupStart rows + i) n
    (fun g hg => hok g (mK g hg)) sT sF n le_rfl (t + 1) le_rfl
  have e : ∀ o p, CNF.Clause.eval σ [(o, p)] = true ↔ σ o = p := by
    intro o p; cases p <;> simp [CNF.Clause.eval]
  simp only [stabUnits, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, e]
  rw [hv1, hv2, hcnt]
  constructor
  · rintro ⟨h2, h3⟩
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h2 h3
    omega
  · intro h2
    refine ⟨?_, ?_⟩
    · simp only [decide_eq_true_eq]; omega
    · simp only [decide_eq_false_iff_not]; omega

/-- **Stabilizer weight enumerator as a model count.** The number of assignments of the
`stabWeightVars rows t` declared variables satisfying `stabWeightFormula rows t` is
`2 ^ (m - dim S)` times the number of elements of `S = rowSpace rows` of Pauli weight `t`
(`m = rows.length`; the factor counts the choices of `u` with the same `uH`). -/
theorem stabWeightFormula_count :
    (Finset.univ.filter (fun a : Fin (stabWeightVars rows t) → Bool =>
      (stabWeightFormula rows t).eval
        (fun v => if h : v < stabWeightVars rows t then a ⟨v, h⟩ else false) = true)).card =
      2 ^ (rows.length - Module.finrank Bit (rowSpace rows)) * weightCount (rowSpace rows) t := by
  classical
  obtain ⟨hI, hA, hR, hC⟩ := stabGates_wf rows t
  rw [stabWeightFormula, gform_count rows.length (stabWeightVars rows t) _ _
    (by simp [stabWeightVars, sCtrStart, sSupStart]; omega) hI hA hR hC]
  simp_rw [stabUnits_iff rows t]
  have hb : (Finset.univ.filter (fun b : Fin rows.length → Bool =>
      pauliWeight (genMap rows (uOf rows b)) = t)).card =
      (Finset.univ.filter (fun u : Fin rows.length → Bit =>
        pauliWeight (genMap rows u) = t)).card := by
    refine Finset.card_bij' (fun b _ => uOf rows b) (fun u _ => fun r => bb (u r)) ?_ ?_ ?_ ?_
    · intro b hb; simpa using hb
    · intro u hu
      have : uOf rows (fun r => bb (u r)) = u := by funext r; simp [uOf, ofBool_bb]
      simpa [this] using hu
    · intro b _; funext r; simp [uOf]
    · intro u _; funext r; simp [uOf, ofBool_bb]
  rw [hb, card_filter_comp_linear (genMap rows) (fun x => pauliWeight x = t), card_ker_eq,
    genMap_range]
  unfold weightCount
  congr 2

/-- Every clause of the stabilizer weight formula has at most three literals. -/
theorem stabWeightFormula_width :
    ∀ c ∈ (stabWeightFormula rows t).clauses, c.length ≤ 3 :=
  gform_width _ _ _ (fun c hc => by
    simp only [stabUnits, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp)

end Stabilizer

/-! ## Variable ranges and sizes -/

theorem gform_vars (k N : Nat) (G : List Gate) (cs : List (CNF.Clause Nat)) (hk : k + 2 ≤ N)
    (hA : Inputs G) (hR : InRange G (k + 2) N) (hcs : ∀ c ∈ cs, ∀ l ∈ c, l.1 < N) :
    ∀ c ∈ (gform k G cs).clauses, ∀ l ∈ c, l.1 < N := by
  intro c hc l hl
  simp only [gform, List.mem_toArray, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatMap] at hc
  rcases hc with (rfl | rfl) | ⟨g, hg, hcg⟩ | hc
  · simp at hl; rw [hl]; simp; omega
  · simp at hl; rw [hl]; simp; omega
  · have h1 := hA g hg
    have h2 := hR g hg
    obtain ⟨t, op, a, b⟩ := g
    simp only at h1 h2
    cases op <;> simp only [Completeness.Gate.clauses, List.mem_cons, List.not_mem_nil,
      or_false] at hcg <;> rcases hcg with rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
      rcases hl with rfl | rfl | rfl <;> simp <;> omega
  · exact hcs c hc l hl

theorem chainsOuts_lt (F : Nat) (ls : List (List Nat)) (s : Nat) (hF : F < s) :
    ∀ o ∈ chainsOuts F ls s, o < s + totalLen ls := by
  induction ls generalizing s with
  | nil => simp [chainsOuts]
  | cons l ls ih =>
    have ht : totalLen (l :: ls) = l.length + totalLen ls := by simp [totalLen]
    intro o ho
    simp only [chainsOuts, List.mem_cons] at ho
    rcases ho with rfl | ho
    · have := chainOut_lt F l s hF; omega
    · have := ih (s + l.length) (by omega) o ho; omega

theorem gcol_lt_end (F T L C i j : Nat) (hF : F < C) (hT : T < C) (hj : j ≤ L + 1) :
    gcol F T L C i j < C + 2 * ((L + 1) * i) := by
  cases i with
  | zero => cases j <;> simp [gcol] <;> omega
  | succ i =>
    cases j with
    | zero => simp [gcol]; omega
    | succ j =>
      simp only [gcol, orOut]
      rw [Nat.mul_succ]
      omega

section Sizes
variable {n : ℕ} (rows : List (List (PauliCoord n))) (t : ℕ)

/-- Every variable of `normWeightFormula rows t` is below `normWeightVars rows t`. -/
theorem normWeightFormula_vars :
    ∀ c ∈ (normWeightFormula rows t).clauses, ∀ l ∈ c, l.1 < normWeightVars rows t := by
  obtain ⟨-, hA, hR, -⟩ := normGates_wf rows t
  refine gform_vars _ _ _ _ (by simp [normWeightVars, nCtrStart, nSupStart]; omega) hA hR ?_
  intro c hc l hl
  simp only [normUnits, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with ⟨o, ho, rfl⟩ | rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil,
    or_false] at hl <;> subst hl
  · have := chainsOuts_lt _ _ _ (by omega) o ho
    simp only [normWeightVars, nCtrStart, nSupStart] at this ⊢; omega
  · have := gcol_lt_end (2 * n) (2 * n + 1) t (nCtrStart rows) n t
      (by simp [nCtrStart, nSupStart]; omega) (by simp [nCtrStart, nSupStart]; omega) (by omega)
    simp only [normWeightVars]; omega
  · have := gcol_lt_end (2 * n) (2 * n + 1) t (nCtrStart rows) n (t + 1)
      (by simp [nCtrStart, nSupStart]; omega) (by simp [nCtrStart, nSupStart]; omega) le_rfl
    simp only [normWeightVars]; omega

/-- Every variable of `stabWeightFormula rows t` is below `stabWeightVars rows t`. -/
theorem stabWeightFormula_vars :
    ∀ c ∈ (stabWeightFormula rows t).clauses, ∀ l ∈ c, l.1 < stabWeightVars rows t := by
  obtain ⟨-, hA, hR, -⟩ := stabGates_wf rows t
  refine gform_vars _ _ _ _ (by simp [stabWeightVars, sCtrStart, sSupStart]; omega) hA hR ?_
  intro c hc l hl
  simp only [stabUnits, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
    subst hl
  · have := gcol_lt_end rows.length (rows.length + 1) t (sCtrStart rows) n t
      (by simp [sCtrStart, sSupStart]; omega) (by simp [sCtrStart, sSupStart]; omega) (by omega)
    simp only [stabWeightVars]; omega
  · have := gcol_lt_end rows.length (rows.length + 1) t (sCtrStart rows) n (t + 1)
      (by simp [sCtrStart, sSupStart]; omega) (by simp [sCtrStart, sSupStart]; omega) le_rfl
    simp only [stabWeightVars]; omega

theorem totalLen_nLists : totalLen (nLists rows) = rowIncidences rows := by
  simp [totalLen, nLists, rowIncidences, Function.comp_def]

omit rows in
theorem coordCount_total (row : List (PauliCoord n)) :
    ∑ i : Fin n, coordCount (.inl i) row + ∑ i : Fin n, coordCount (.inr i) row = row.length := by
  induction row with
  | nil => simp [coordCount]
  | cons c row ih =>
    simp only [coordCount_cons, Finset.sum_add_distrib, List.length_cons]
    cases c with
    | inl j => simp [Finset.sum_ite_eq]; omega
    | inr j => simp [Finset.sum_ite_eq]; omega

theorem totalLen_sLists : totalLen (sLists rows) = rowIncidences rows := by
  have hocc : ∀ c : PauliCoord n,
      (occ rows c).length = ∑ r : Fin rows.length, coordCount c (rows.get r) := by
    intro c
    simp [occ, List.length_flatMap, Fin.sum_univ_def]
  simp only [totalLen, sLists, List.map_append, List.map_map, List.sum_append]
  have e1 : ((List.finRange n).map (List.length ∘ fun i => occ rows (.inl i))).sum =
      ∑ i : Fin n, ∑ r : Fin rows.length, coordCount (.inl i) (rows.get r) := by
    rw [Fin.sum_univ_def]; congr 1; simp [hocc]
  have e2 : ((List.finRange n).map (List.length ∘ fun i => occ rows (.inr i))).sum =
      ∑ i : Fin n, ∑ r : Fin rows.length, coordCount (.inr i) (rows.get r) := by
    rw [Fin.sum_univ_def]; congr 1; simp [hocc]
  rw [e1, e2, Finset.sum_comm, Finset.sum_comm (f := fun i r => coordCount (.inr i) (rows.get r)),
    ← Finset.sum_add_distrib]
  simp only [coordCount_total]
  rw [Fin.sum_univ_def, rowIncidences]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- **Size of the normalizer formula:** `(2t + 5) n + I + 2` variables, `I = rowIncidences rows`. -/
theorem normWeightVars_eq :
    normWeightVars rows t = (2 * t + 5) * n + rowIncidences rows + 2 := by
  simp only [normWeightVars, nCtrStart, nSupStart, totalLen_nLists]
  ring

/-- **Size of the stabilizer formula:** `(2t + 3) n + I + m + 2` variables. -/
theorem stabWeightVars_eq :
    stabWeightVars rows t = (2 * t + 3) * n + rowIncidences rows + rows.length + 2 := by
  simp only [stabWeightVars, sCtrStart, sSupStart, totalLen_sLists]
  ring

end Sizes

end QecPhysical.Stabilizer.Enumerator

#print axioms QecPhysical.Stabilizer.Enumerator.normWeightFormula_count
#print axioms QecPhysical.Stabilizer.Enumerator.normWeightFormula_width
#print axioms QecPhysical.Stabilizer.Enumerator.normWeightFormula_vars
#print axioms QecPhysical.Stabilizer.Enumerator.stabWeightFormula_count
#print axioms QecPhysical.Stabilizer.Enumerator.stabWeightFormula_width
#print axioms QecPhysical.Stabilizer.Enumerator.stabWeightFormula_vars
#print axioms QecPhysical.Stabilizer.Enumerator.normWeightVars_eq
#print axioms QecPhysical.Stabilizer.Enumerator.stabWeightVars_eq
