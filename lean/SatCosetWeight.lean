import DistanceExtraction
import Std.Sat.CNF.Basic

set_option autoImplicit false

/-!
# Step A: CNF satisfiability as a minimum-weight solution of a GF(2) system

A normalized formula `F : Formula` has `F.N` variables, `F.M` clauses, clause `c` has
`F.len c` literals, and literal `j` of clause `c` is `F.lit c j : Fin F.N × Bool`
(`(v, true)` is the literal `v`, `(v, false)` is `¬v`, as in `Std.Sat`).
Occurrences are `F.Occ = Σ c, Fin (F.len c)`; there are `F.K = ∑ c, F.len c` of them.

Coordinates (`2N + 3K` of them): `p_i, n_i` for each variable, `σ_o, w_o, c_o` for each
occurrence. Writing `b_o = p_{var o} + [o negative]` for the value of the literal, the equations
are

    p_i + n_i = 1,   ∑_{o ∈ c} σ_o = 1,   w_o = σ_o + b_o,   c_o = 1 + b_o.

Main results:
* `wt_of_sol`: every solution has weight exactly `N + K + 2·#{o : σ_o = 1, b_o = 0}`;
* `sat_sol`: a satisfying assignment gives a solution of weight `N + K`;
* `wt_ge`, `wt_of_unsat`: every solution has weight `≥ N + K`, and `≥ N + K + 2` when the formula
  is unsatisfiable;
* `ker_mem_span`: the explicit list `kerGens` spans the solution space of the homogeneous system
  (no Gaussian elimination), and `kerGens_ker` says each generator lies in it;
* `formulaOf φ` turns any `φ : Std.Sat.CNF Nat` into a formula with no empty clause and the same
  satisfiability (`cnf_sat_iff`, `formulaOf_len_pos`). A formula with an empty clause is replaced
  by the fixed unsatisfiable formula `x₀ ∧ ¬x₀`; duplicate literals, tautological clauses and
  variables that occur nowhere need no treatment (the gadget is correct for arbitrary literal
  lists; variable indices are `< N = 1 + max index`).
-/

namespace QecReliability.SatReduction

open scoped BigOperators
open Finset
open QecReliability.Binary

/- Lists are counted with the `BEq` instance coming from `DecidableEq`, also on sum types. -/
attribute [local instance 2000] instBEqOfDecidableEq

/-- The vector of a list of coordinates: entry `y` is the multiplicity of `y`, mod 2. -/
def listVec {α : Type} [DecidableEq α] (l : List α) : α → Bit := fun y => ((l.count y : ℕ) : Bit)

theorem bit_cases (b : Bit) : b = 0 ∨ b = 1 := by
  revert b; decide

theorem bit_eq_one_of_ne_zero {b : Bit} (h : b ≠ 0) : b = 1 := by
  rcases bit_cases b with h' | h'
  · exact absurd h' h
  · exact h'

theorem bit_eq_zero_of_ne_one {b : Bit} (h : b ≠ 1) : b = 0 := by
  rcases bit_cases b with h' | h'
  · exact h'
  · exact absurd h' h

theorem bit_add_self (b : Bit) : b + b = 0 := by
  revert b; decide

/-- A normalized CNF formula. -/
structure Formula where
  N : ℕ
  M : ℕ
  len : Fin M → ℕ
  lit : (c : Fin M) → Fin (len c) → Fin N × Bool

namespace Formula

variable (F : Formula)

/-- Literal occurrences. -/
abbrev Occ : Type := (c : Fin F.M) × Fin (F.len c)

def var (o : F.Occ) : Fin F.N := (F.lit o.1 o.2).1
def pol (o : F.Occ) : Bool := (F.lit o.1 o.2).2

/-- Number of literal occurrences. -/
def K : ℕ := ∑ c, F.len c

theorem card_occ : Fintype.card F.Occ = F.K := by
  simp [K, Occ, Fintype.card_sigma]

/-- Satisfaction of the normalized formula. -/
def Sat (a : Fin F.N → Bool) : Prop :=
  ∀ c : Fin F.M, ∃ j : Fin (F.len c), (a (F.lit c j).1 == (F.lit c j).2) = true

/-- Coordinates: `p`, `n` per variable; `σ`, `w`, `c` per occurrence. -/
abbrev Coord : Type := Fin F.N ⊕ Fin F.N ⊕ F.Occ ⊕ F.Occ ⊕ F.Occ

instance instDecEqCoord : DecidableEq F.Coord :=
  @instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance
    (@instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance)))

abbrev cP (i : Fin F.N) : F.Coord := Sum.inl i
abbrev cN (i : Fin F.N) : F.Coord := Sum.inr (Sum.inl i)
abbrev cS (o : F.Occ) : F.Coord := Sum.inr (Sum.inr (Sum.inl o))
abbrev cW (o : F.Occ) : F.Coord := Sum.inr (Sum.inr (Sum.inr (Sum.inl o)))
abbrev cC (o : F.Occ) : F.Coord := Sum.inr (Sum.inr (Sum.inr (Sum.inr o)))

/-- Equations: one per variable, one per clause, two per occurrence. -/
abbrev Row : Type := Fin F.N ⊕ Fin F.M ⊕ F.Occ ⊕ F.Occ

/-- `1` for a negative literal, `0` for a positive one. -/
def negB (o : F.Occ) : Bit := if F.pol o then 0 else 1

def eqList : F.Row → List F.Coord
  | Sum.inl i => [F.cP i, F.cN i]
  | Sum.inr (Sum.inl c) => (List.finRange (F.len c)).map (fun j => F.cS ⟨c, j⟩)
  | Sum.inr (Sum.inr (Sum.inl o)) => [F.cW o, F.cS o, F.cP (F.var o)]
  | Sum.inr (Sum.inr (Sum.inr o)) => [F.cC o, F.cP (F.var o)]

def eqRhs : F.Row → Bit
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl o)) => F.negB o
  | Sum.inr (Sum.inr (Sum.inr o)) => 1 + F.negB o

/-- `x` solves `H x = s`. -/
def IsSol (x : F.Coord → Bit) : Prop := ∀ r, ((F.eqList r).map x).sum = F.eqRhs r

/-- `x` solves `H x = 0`. -/
def IsKer (x : F.Coord → Bit) : Prop := ∀ r, ((F.eqList r).map x).sum = 0

/-- Hamming weight. -/
def wt (x : F.Coord → Bit) : ℕ := (univ.filter (fun g => x g ≠ 0)).card

theorem eqList_clause_sum (x : F.Coord → Bit) (c : Fin F.M) :
    ((F.eqList (Sum.inr (Sum.inl c))).map x).sum = ∑ j, x (F.cS ⟨c, j⟩) := by
  simp only [eqList, List.map_map]
  rw [Fin.sum_univ_def]
  rfl

theorem isSol_iff (x : F.Coord → Bit) : F.IsSol x ↔
    (∀ i, x (F.cP i) + x (F.cN i) = 1) ∧ (∀ c, ∑ j, x (F.cS ⟨c, j⟩) = 1) ∧
      (∀ o, x (F.cW o) + (x (F.cS o) + x (F.cP (F.var o))) = F.negB o) ∧
        (∀ o, x (F.cC o) + x (F.cP (F.var o)) = 1 + F.negB o) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun c => ?_, fun o => ?_, fun o => ?_⟩
    · simpa [eqList, eqRhs] using h (Sum.inl i)
    · rw [← eqList_clause_sum]; exact h (Sum.inr (Sum.inl c))
    · simpa [eqList, eqRhs] using h (Sum.inr (Sum.inr (Sum.inl o)))
    · simpa [eqList, eqRhs] using h (Sum.inr (Sum.inr (Sum.inr o)))
  · rintro ⟨h1, h2, h3, h4⟩ r
    rcases r with i | c | o | o
    · simpa [eqList, eqRhs] using h1 i
    · rw [eqList_clause_sum]; exact h2 c
    · simpa [eqList, eqRhs] using h3 o
    · simpa [eqList, eqRhs] using h4 o

theorem isKer_iff (x : F.Coord → Bit) : F.IsKer x ↔
    (∀ i, x (F.cP i) + x (F.cN i) = 0) ∧ (∀ c, ∑ j, x (F.cS ⟨c, j⟩) = 0) ∧
      (∀ o, x (F.cW o) + (x (F.cS o) + x (F.cP (F.var o))) = 0) ∧
        (∀ o, x (F.cC o) + x (F.cP (F.var o)) = 0) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun c => ?_, fun o => ?_, fun o => ?_⟩
    · simpa [eqList] using h (Sum.inl i)
    · rw [← eqList_clause_sum]; exact h (Sum.inr (Sum.inl c))
    · simpa [eqList] using h (Sum.inr (Sum.inr (Sum.inl o)))
    · simpa [eqList] using h (Sum.inr (Sum.inr (Sum.inr o)))
  · rintro ⟨h1, h2, h3, h4⟩ r
    rcases r with i | c | o | o
    · simpa [eqList] using h1 i
    · rw [eqList_clause_sum]; exact h2 c
    · simpa [eqList] using h3 o
    · simpa [eqList] using h4 o

/-! ## The weight of a solution -/

/-- The value of the literal at occurrence `o` under the `p`-coordinates of `x`. -/
def lv (x : F.Coord → Bit) (o : F.Occ) : Bit := x (F.cP (F.var o)) + F.negB o

theorem wt_eq_sum (x : F.Coord → Bit) : F.wt x = ∑ g, if x g ≠ 0 then 1 else 0 := by
  unfold wt
  rw [Finset.card_filter]

private theorem key_pair : ∀ p q : Bit, p + q = 1 →
    (if p ≠ 0 then 1 else 0) + (if q ≠ 0 then 1 else 0) = (1 : ℕ) := by decide

private theorem key_occ : ∀ s b : Bit,
    (if s ≠ 0 then 1 else 0) + (if s + b ≠ 0 then 1 else 0) + (if 1 + b ≠ 0 then 1 else 0) =
      1 + 2 * (if s = 1 ∧ b = 0 then 1 else 0 : ℕ) := by decide

private theorem solve_w : ∀ w s p g : Bit, w + (s + p) = g → w = s + (p + g) := by decide
private theorem solve_c : ∀ c p g : Bit, c + p = 1 + g → c = 1 + (p + g) := by decide

/-- **Exact weight of every solution.** -/
theorem wt_of_sol {x : F.Coord → Bit} (hx : F.IsSol x) :
    F.wt x = F.N + F.K +
      2 * (univ.filter (fun o => x (F.cS o) = 1 ∧ F.lv x o = 0)).card := by
  obtain ⟨h1, -, h3, h4⟩ := (F.isSol_iff x).1 hx
  have hp : ∀ i : Fin F.N, (if x (F.cP i) ≠ 0 then 1 else 0) +
      (if x (F.cN i) ≠ 0 then 1 else 0) = (1 : ℕ) := fun i => key_pair _ _ (h1 i)
  have ho : ∀ o : F.Occ, (if x (F.cS o) ≠ 0 then 1 else 0) + (if x (F.cW o) ≠ 0 then 1 else 0) +
      (if x (F.cC o) ≠ 0 then 1 else 0) =
        1 + 2 * (if x (F.cS o) = 1 ∧ F.lv x o = 0 then 1 else 0 : ℕ) := by
    intro o
    rw [solve_w _ _ _ _ (h3 o), solve_c _ _ _ (h4 o)]
    exact key_occ _ _
  rw [wt_eq_sum]
  have hsplit : (∑ g, if x g ≠ 0 then 1 else 0) =
      ∑ i : Fin F.N, ((if x (F.cP i) ≠ 0 then 1 else 0) + (if x (F.cN i) ≠ 0 then 1 else 0)) +
      ∑ o : F.Occ, ((if x (F.cS o) ≠ 0 then 1 else 0) + (if x (F.cW o) ≠ 0 then 1 else 0) +
        (if x (F.cC o) ≠ 0 then 1 else 0)) := by
    simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
    ring
  rw [hsplit, Finset.sum_congr rfl (fun i _ => hp i), Finset.sum_congr rfl (fun o _ => ho o),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    card_occ]
  ring

theorem wt_ge {x : F.Coord → Bit} (hx : F.IsSol x) : F.N + F.K ≤ F.wt x := by
  rw [F.wt_of_sol hx]; omega

/-- The assignment read off the `p`-coordinates. -/
def assignOf (x : F.Coord → Bit) : Fin F.N → Bool := fun i => decide (x (F.cP i) = 1)

private theorem lit_key : ∀ (p : Bit) (b : Bool),
    ((decide (p = 1)) == b) = true ↔ p + (if b then 0 else 1) = 1 := by decide

theorem lit_true_iff (x : F.Coord → Bit) (o : F.Occ) :
    (F.assignOf x (F.var o) == F.pol o) = true ↔ F.lv x o = 1 := by
  unfold assignOf lv negB
  exact lit_key _ _

/-- **Unsatisfiable formulas:** every solution has weight `≥ N + K + 2`. -/
theorem wt_of_unsat {x : F.Coord → Bit} (hx : F.IsSol x) (h : ¬ F.Sat (F.assignOf x)) :
    F.N + F.K + 2 ≤ F.wt x := by
  rw [F.wt_of_sol hx]
  have hpos : 0 < (univ.filter (fun o => x (F.cS o) = 1 ∧ F.lv x o = 0)).card := by
    obtain ⟨c, hc⟩ := not_forall.1 h
    have hc' := not_exists.1 hc
    have hsum := ((F.isSol_iff x).1 hx).2.1 c
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ)
      (f := fun j => x (F.cS ⟨c, j⟩)) (by rw [hsum]; decide)
    apply Finset.card_pos.2
    refine ⟨⟨c, j⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨bit_eq_one_of_ne_zero hj, bit_eq_zero_of_ne_one fun h1 => hc' j ?_⟩
    exact (F.lit_true_iff x ⟨c, j⟩).2 h1
  omega

/-! ## Solutions from assignments -/

def bitOf (b : Bool) : Bit := if b then 1 else 0

/-- The solution attached to an assignment and a choice of one literal per clause. -/
def solOf (a : Fin F.N → Bool) (pick : ∀ c, Fin (F.len c)) : F.Coord → Bit :=
  Sum.elim (fun i => bitOf (a i)) (Sum.elim (fun i => bitOf (!a i))
    (Sum.elim (fun o => if o.2 = pick o.1 then 1 else 0)
      (Sum.elim (fun o => (if o.2 = pick o.1 then 1 else 0) + (bitOf (a (F.var o)) + F.negB o))
        (fun o => 1 + (bitOf (a (F.var o)) + F.negB o)))))

private theorem pair_bool : ∀ b : Bool, bitOf b + bitOf (!b) = 1 := by decide
private theorem w_id : ∀ s p g : Bit, s + (p + g) + (s + p) = g := by decide
private theorem c_id : ∀ p g : Bit, 1 + (p + g) + p = 1 + g := by decide

theorem isSol_solOf (a : Fin F.N → Bool) (pick : ∀ c, Fin (F.len c)) :
    F.IsSol (F.solOf a pick) := by
  rw [isSol_iff]
  refine ⟨fun i => pair_bool (a i), fun c => ?_, fun o => w_id _ _ _, fun o => c_id _ _⟩
  simp [solOf]

private theorem lit_key' : ∀ (a b : Bool), (a == b) = true → bitOf a + (if b then 0 else 1) = 1 := by
  decide

theorem lv_solOf (a : Fin F.N → Bool) (pick : ∀ c, Fin (F.len c)) (o : F.Occ) :
    F.lv (F.solOf a pick) o = bitOf (a (F.var o)) + F.negB o := rfl

theorem assignOf_solOf (a : Fin F.N → Bool) (pick : ∀ c, Fin (F.len c)) :
    F.assignOf (F.solOf a pick) = a := by
  funext i
  unfold assignOf
  change decide (bitOf (a i) = 1) = a i
  cases a i <;> decide

/-- **Satisfiable formulas:** a solution of weight exactly `N + K`. -/
theorem sat_sol {a : Fin F.N → Bool} (ha : F.Sat a) :
    ∃ x, F.IsSol x ∧ F.wt x = F.N + F.K ∧ F.assignOf x = a := by
  choose pick hpick using ha
  refine ⟨F.solOf a pick, F.isSol_solOf a pick, ?_, F.assignOf_solOf a pick⟩
  rw [F.wt_of_sol (F.isSol_solOf a pick)]
  have : univ.filter (fun o => F.solOf a pick (F.cS o) = 1 ∧ F.lv (F.solOf a pick) o = 0) = ∅ := by
    apply Finset.filter_false_of_mem
    rintro ⟨c, j⟩ -
    rintro ⟨h1, h2⟩
    have hj : j = pick c := by
      by_contra hne
      simp [solOf, hne] at h1
    subst hj
    have := lit_key' _ _ (hpick c)
    rw [lv_solOf] at h2
    unfold negB pol var at h2
    rw [this] at h2
    exact one_ne_zero h2
  rw [this]
  simp

/-- With no empty clause, every assignment gives a solution. -/
theorem exists_sol (hpos : ∀ c, 0 < F.len c) : ∃ x, F.IsSol x :=
  ⟨F.solOf (fun _ => false) (fun c => ⟨0, hpos c⟩), F.isSol_solOf _ _⟩

/-! ## An explicit basis of the homogeneous solutions -/

/-- The first occurrence of the clause of `o`. -/
def zeroOcc (o : F.Occ) : F.Occ := ⟨o.1, ⟨0, Nat.zero_lt_of_lt o.2.isLt⟩⟩

theorem eq_zeroOcc_iff (o' o : F.Occ) : o' = F.zeroOcc o ↔ o'.1 = o.1 ∧ o'.2.val = 0 := by
  rcases o' with ⟨c', j'⟩
  rcases o with ⟨c, j⟩
  simp only [zeroOcc]
  constructor
  · intro h
    have h1 : c' = c := congrArg Sigma.fst h
    subst h1
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact ⟨rfl, by rw [h]⟩
  · rintro ⟨h1, h2⟩
    subst h1
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    exact Fin.ext h2

/-- Occurrences of variable `i`, as a coordinate list `w_o, c_o, …`. -/
def occPart (i : Fin F.N) : List F.Coord :=
  (List.finRange F.M).flatMap (fun c => (List.finRange (F.len c)).flatMap
    (fun j => if F.var ⟨c, j⟩ = i then [F.cW ⟨c, j⟩, F.cC ⟨c, j⟩] else []))

/-- Generator for variable `i`: `p_i + n_i + ∑_{var o = i} (w_o + c_o)`. -/
def genP (i : Fin F.N) : List F.Coord := [F.cP i, F.cN i] ++ F.occPart i

/-- Generator for occurrence `o`: `σ_{o₀} + σ_o + w_{o₀} + w_o` (`o₀` the first occurrence of the
same clause; zero vector when `o = o₀`). -/
def genD (o : F.Occ) : List F.Coord := [F.cS (F.zeroOcc o), F.cS o, F.cW (F.zeroOcc o), F.cW o]

def allOcc : List F.Occ :=
  (List.finRange F.M).flatMap (fun c => (List.finRange (F.len c)).map (fun j => ⟨c, j⟩))

theorem mem_allOcc (o : F.Occ) : o ∈ F.allOcc := by
  rcases o with ⟨c, j⟩
  simp only [allOcc, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨c, j, rfl⟩

def kerGens : List (List F.Coord) := (List.finRange F.N).map F.genP ++ F.allOcc.map F.genD

/-- `listVec (genP i)` as a function. -/
def vP (i : Fin F.N) : F.Coord → Bit :=
  Sum.elim (fun i' => if i = i' then 1 else 0) (Sum.elim (fun i' => if i = i' then 1 else 0)
    (Sum.elim (fun _ => 0) (Sum.elim (fun o => if F.var o = i then 1 else 0)
      (fun o => if F.var o = i then 1 else 0))))

/-- `listVec (genD o)` as a function. -/
def vD (o : F.Occ) : F.Coord → Bit :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
    (Sum.elim (fun o' => (if o'.1 = o.1 ∧ o'.2.val = 0 then 1 else 0) + (if o = o' then 1 else 0))
      (Sum.elim (fun o' => (if o'.1 = o.1 ∧ o'.2.val = 0 then 1 else 0) + (if o = o' then 1 else 0))
        (fun _ => 0))))

theorem count_occPart (i : Fin F.N) (y : F.Coord) :
    (F.occPart i).count y =
      ∑ o : F.Occ, (if F.var o = i then [F.cW o, F.cC o] else []).count y := by
  simp only [occPart, List.count_flatMap, Function.comp_def, ← Fin.sum_univ_def]
  rw [Fintype.sum_sigma]

theorem listVec_genP (i : Fin F.N) : listVec (F.genP i) = F.vP i := by
  funext y
  unfold listVec genP
  rw [List.count_append, count_occPart]
  rcases y with i' | i' | o' | o' | o'
  · have : ∀ o : F.Occ, (if F.var o = i then [F.cW o, F.cC o] else []).count (F.cP i') = 0 := by
      intro o; split_ifs <;> simp
    simp only [this, Finset.sum_const_zero, add_zero, List.count_cons, List.count_nil, beq_iff_eq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, vP, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> simp_all
  · have : ∀ o : F.Occ, (if F.var o = i then [F.cW o, F.cC o] else []).count (F.cN i') = 0 := by
      intro o; split_ifs <;> simp
    simp only [this, Finset.sum_const_zero, add_zero, List.count_cons, List.count_nil, beq_iff_eq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, vP, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> simp_all
  · have : ∀ o : F.Occ, (if F.var o = i then [F.cW o, F.cC o] else []).count (F.cS o') = 0 := by
      intro o; split_ifs <;> simp
    simp [this, vP]
  · have : ∀ o : F.Occ, (if F.var o = i then [F.cW o, F.cC o] else []).count (F.cW o') =
        if o = o' then (if F.var o' = i then 1 else 0) else 0 := by
      intro o
      by_cases ho : o = o'
      · subst ho; split_ifs <;> simp_all
      · split_ifs <;> simp [ho]
    simp [this, vP]
  · have : ∀ o : F.Occ, (if F.var o = i then [F.cW o, F.cC o] else []).count (F.cC o') =
        if o = o' then (if F.var o' = i then 1 else 0) else 0 := by
      intro o
      by_cases ho : o = o'
      · subst ho; split_ifs <;> simp_all
      · split_ifs <;> simp [ho]
    simp [this, vP]

theorem listVec_genD (o : F.Occ) : listVec (F.genD o) = F.vD o := by
  funext y
  unfold listVec genD
  rcases y with i' | i' | o' | o' | o'
  · simp [vD]
  · simp [vD]
  · simp only [List.count_cons, List.count_nil, beq_iff_eq, Sum.inr.injEq, Sum.inl.injEq,
      reduceCtorEq, ite_false, add_zero, zero_add, vD, Sum.elim_inr, Sum.elim_inl]
    simp only [show (F.zeroOcc o = o') ↔ (o'.1 = o.1 ∧ o'.2.val = 0) from
      eq_comm.trans (F.eq_zeroOcc_iff o' o)]
    push_cast
    ring
  · simp only [List.count_cons, List.count_nil, beq_iff_eq, Sum.inr.injEq, Sum.inl.injEq,
      reduceCtorEq, ite_false, add_zero, zero_add, vD, Sum.elim_inr, Sum.elim_inl]
    simp only [show (F.zeroOcc o = o') ↔ (o'.1 = o.1 ∧ o'.2.val = 0) from
      eq_comm.trans (F.eq_zeroOcc_iff o' o)]
    push_cast
    ring
  · simp [vD]

theorem sum_clause_indicator (c : Fin F.M) (o : F.Occ) :
    (∑ j : Fin (F.len c), (if o = (⟨c, j⟩ : F.Occ) then (1 : Bit) else 0)) =
      if o.1 = c then 1 else 0 := by
  rcases o with ⟨c', j'⟩
  by_cases h : c' = c
  · subst h
    simp [Sigma.mk.inj_iff]
  · have : ∀ j : Fin (F.len c), ¬ ((⟨c', j'⟩ : F.Occ) = ⟨c, j⟩) := by
      intro j hj
      exact h (congrArg Sigma.fst hj)
    simp [this, h]

theorem sum_clause_first (c : Fin F.M) (o : F.Occ) :
    (∑ j : Fin (F.len c), (if (⟨c, j⟩ : F.Occ).1 = o.1 ∧ (⟨c, j⟩ : F.Occ).2.val = 0
      then (1 : Bit) else 0)) = if c = o.1 then 1 else 0 := by
  by_cases h : c = o.1
  · subst h
    simp only [true_and, ite_true]
    have hpos : 0 < F.len o.1 := Nat.zero_lt_of_lt o.2.isLt
    rw [Finset.sum_eq_single ⟨0, hpos⟩]
    · simp
    · intro j _ hj
      have : j.val ≠ 0 := fun h0 => hj (Fin.ext h0)
      simp [this]
    · simp
  · simp [h]

theorem vP_ker (i : Fin F.N) : F.IsKer (F.vP i) := by
  rw [isKer_iff]
  refine ⟨fun i' => ?_, fun c => ?_, fun o => ?_, fun o => ?_⟩
  · simp only [vP, Sum.elim_inl, Sum.elim_inr]; exact bit_add_self _
  · simp [vP]
  · simp only [vP, Sum.elim_inl, Sum.elim_inr, zero_add]
    split_ifs with h1 h2 h2
    · decide
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · decide
  · simp only [vP, Sum.elim_inl, Sum.elim_inr]
    split_ifs with h1 h2 h2
    · decide
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · decide

theorem vD_ker (o : F.Occ) : F.IsKer (F.vD o) := by
  rw [isKer_iff]
  refine ⟨fun i' => ?_, fun c => ?_, fun o' => ?_, fun o' => ?_⟩
  · simp [vD]
  · simp only [vD, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_add_distrib, sum_clause_first, sum_clause_indicator]
    by_cases h : c = o.1
    · subst h; simp only [ite_true]; decide
    · simp [h, Ne.symm h]
  · simp only [vD, Sum.elim_inl, Sum.elim_inr, add_zero]
    exact bit_add_self _
  · simp [vD]

theorem kerGens_ker (gen : List F.Coord) (h : gen ∈ F.kerGens) : F.IsKer (listVec gen) := by
  simp only [kerGens, List.mem_append, List.mem_map, List.mem_finRange, true_and] at h
  rcases h with ⟨i, rfl⟩ | ⟨o, -, rfl⟩
  · rw [listVec_genP]; exact F.vP_ker i
  · rw [listVec_genD]; exact F.vD_ker o

/-- **Explicit decomposition of a homogeneous solution.** -/
theorem ker_eq_comb {x : F.Coord → Bit} (hx : F.IsKer x) :
    x = ∑ i, x (F.cP i) • F.vP i + ∑ o, x (F.cS o) • F.vD o := by
  obtain ⟨h1, h2, h3, h4⟩ := (F.isKer_iff x).1 hx
  have hsig : ∀ o' : F.Occ, ∑ o : F.Occ, x (F.cS o) *
      ((if o'.1 = o.1 ∧ o'.2.val = 0 then 1 else 0) + (if o = o' then 1 else 0)) = x (F.cS o') := by
    intro o'
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    have : ∑ o : F.Occ, (if o'.1 = o.1 ∧ o'.2.val = 0 then x (F.cS o) else 0) = 0 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_eq_zero
      intro c _
      show ∑ j : Fin (F.len c), (if o'.1 = c ∧ o'.2.val = 0 then x (F.cS ⟨c, j⟩) else 0) = 0
      by_cases hc : o'.1 = c ∧ o'.2.val = 0
      · simp only [hc, and_self, ite_true]
        exact h2 c
      · simp only [hc, ite_false, Finset.sum_const_zero]
    rw [this, zero_add]
  have hvar : ∀ v : Fin F.N, ∑ i : Fin F.N, x (F.cP i) * (if v = i then 1 else 0) = x (F.cP v) := by
    intro v
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have hvarL : ∀ v : Fin F.N, ∑ i : Fin F.N, x (F.cP i) * (if i = v then 1 else 0) = x (F.cP v) := by
    intro v
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  funext y
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rcases y with i' | i' | o' | o' | o'
  · simp only [vP, vD, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hvarL]
  · simp only [vP, vD, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hvarL]
    have := h1 i'
    rcases bit_cases (x (F.cP i')) with h | h <;> rcases bit_cases (x (F.cN i')) with h' | h' <;>
      simp_all
  · simp only [vP, vD, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add]
    rw [hsig]
  · simp only [vP, vD, Sum.elim_inl, Sum.elim_inr]
    rw [hsig]
    have hv : ∑ i : Fin F.N, x (F.cP i) * (if F.var o' = i then 1 else 0) = x (F.cP (F.var o')) :=
      hvar _
    rw [hv]
    have := h3 o'
    revert this
    generalize x (F.cW o') = a
    generalize x (F.cS o') = b
    generalize x (F.cP (F.var o')) = c
    revert a b c
    decide
  · simp only [vP, vD, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hvar]
    have := h4 o'
    revert this
    generalize x (F.cC o') = a
    generalize x (F.cP (F.var o')) = c
    revert a c
    decide

/-- **The explicit generators span the homogeneous solutions.** -/
theorem ker_mem_span {x : F.Coord → Bit} (hx : F.IsKer x) :
    x ∈ Submodule.span Bit {v | v ∈ F.kerGens.map listVec} := by
  have hmem : (∑ i, x (F.cP i) • F.vP i + ∑ o, x (F.cS o) • F.vD o) ∈
      Submodule.span Bit {v | v ∈ F.kerGens.map listVec} := ?_
  · rw [← F.ker_eq_comb hx] at hmem
    exact hmem
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine List.mem_map.2 ⟨F.genP i, ?_, F.listVec_genP i⟩
    simp [kerGens]
  · apply Submodule.sum_mem
    intro o _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine List.mem_map.2 ⟨F.genD o, ?_, F.listVec_genD o⟩
    simp only [kerGens, List.mem_append, List.mem_map]
    exact Or.inr ⟨o, F.mem_allOcc o, rfl⟩

end Formula

/-! ## From `Std.Sat.CNF Nat` -/

/-- Semantics of a clause list (`(v, true)` is `v`, `(v, false)` is `¬v`). -/
def ListSat (L : List (List (ℕ × Bool))) (a : ℕ → Bool) : Prop :=
  ∀ c ∈ L, ∃ l ∈ c, (a l.1 == l.2) = true

/-- Largest variable index occurring in `L` (`0` if none). -/
def maxVar (L : List (List (ℕ × Bool))) : ℕ := (L.flatten.map Prod.fst).foldr max 0

/-- Number of variables of the normalized formula: `1 + maxVar`. -/
def varBound (L : List (List (ℕ × Bool))) : ℕ := maxVar L + 1

/-- Total number of literal occurrences. -/
def litCount (L : List (List (ℕ × Bool))) : ℕ := (L.map List.length).sum

theorem le_foldr_max (l : List ℕ) : ∀ v ∈ l, v ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro v hv
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · exact le_max_left _ _
    · exact le_trans (ih v hv) (le_max_right _ _)

theorem var_lt (L : List (List (ℕ × Bool))) {c : List (ℕ × Bool)} (hc : c ∈ L)
    {l : ℕ × Bool} (hl : l ∈ c) : l.1 < varBound L := by
  have := le_foldr_max (L.flatten.map Prod.fst) l.1
    (List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩)
  unfold varBound maxVar
  omega

/-- The normalized formula of a clause list. Variable `v` becomes `v % varBound L`, which is `v`
itself (`var_lt`). -/
def ofList (L : List (List (ℕ × Bool))) : Formula where
  N := varBound L
  M := L.length
  len c := (L.get c).length
  lit c j := (⟨((L.get c).get j).1 % varBound L, Nat.mod_lt _ (Nat.succ_pos (maxVar L))⟩,
    ((L.get c).get j).2)

/-- Extension of an assignment of the normalized variables to all of `ℕ`. -/
def liftAssign (L : List (List (ℕ × Bool))) (a : Fin (varBound L) → Bool) : ℕ → Bool :=
  fun v => if h : v < varBound L then a ⟨v, h⟩ else false

theorem liftAssign_apply (L : List (List (ℕ × Bool))) (a : Fin (varBound L) → Bool) {v : ℕ}
    (h : v < varBound L) :
    liftAssign L a v = a ⟨v % varBound L, Nat.mod_lt _ (Nat.succ_pos (maxVar L))⟩ := by
  unfold liftAssign
  rw [dif_pos h]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt h).symm

theorem ofList_sat_iff (L : List (List (ℕ × Bool))) :
    (∃ a : ℕ → Bool, ListSat L a) ↔ ∃ a, (ofList L).Sat a := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.val, fun c => ?_⟩
    obtain ⟨l, hl, hla⟩ := ha (L.get c) (List.get_mem L c)
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hl
    refine ⟨j, ?_⟩
    have hlt := var_lt L (List.get_mem L c) hl
    simp only [ofList]
    rw [Nat.mod_eq_of_lt hlt]
    exact hla
  · rintro ⟨a, ha⟩
    refine ⟨liftAssign L a, fun c hc => ?_⟩
    obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hc
    obtain ⟨j, hj⟩ := ha k
    refine ⟨(L.get k).get j, List.get_mem _ j, ?_⟩
    have hlt := var_lt L hc (List.get_mem _ j)
    rw [liftAssign_apply L a hlt]
    exact hj

theorem cnf_sat_iff_list (φ : Std.Sat.CNF Nat) (a : ℕ → Bool) :
    φ.Sat a ↔ ListSat φ.clauses.toList a := by
  rw [Std.Sat.CNF.sat_def]
  simp [Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval, ListSat, List.any_eq_true]
  exact ⟨fun h c hc => by
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hc
      exact h i hi,
    fun h i hi => h _ (Array.getElem_mem hi)⟩

/-- The fixed unsatisfiable formula `x₀ ∧ ¬x₀`, used for formulas with an empty clause. -/
def fixedUnsat : List (List (ℕ × Bool)) := [[(0, true)], [(0, false)]]

/-- Replace a clause list containing an empty clause by `fixedUnsat`. -/
def normalizeList (L : List (List (ℕ × Bool))) : List (List (ℕ × Bool)) :=
  if [] ∈ L then fixedUnsat else L

theorem not_listSat_fixedUnsat (a : ℕ → Bool) : ¬ ListSat fixedUnsat a := by
  intro h
  obtain ⟨l1, hl1, h1⟩ := h [(0, true)] (by simp [fixedUnsat])
  obtain ⟨l2, hl2, h2⟩ := h [(0, false)] (by simp [fixedUnsat])
  simp only [List.mem_singleton] at hl1 hl2
  subst hl1 hl2
  cases h0 : a 0 <;> simp_all

theorem normalize_sat_iff (L : List (List (ℕ × Bool))) :
    (∃ a, ListSat (normalizeList L) a) ↔ ∃ a, ListSat L a := by
  unfold normalizeList
  split_ifs with h
  · constructor
    · rintro ⟨a, ha⟩; exact absurd ha (not_listSat_fixedUnsat a)
    · rintro ⟨a, ha⟩
      obtain ⟨l, hl, -⟩ := ha [] h
      simp at hl
  · exact Iff.rfl

theorem normalize_nonempty (L : List (List (ℕ × Bool))) :
    ∀ c ∈ normalizeList L, c ≠ [] := by
  unfold normalizeList
  split_ifs with h
  · intro c hc
    simp only [fixedUnsat, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp
  · intro c hc hc0
    exact h (hc0 ▸ hc)

/-- **The normalized formula of a CNF.** -/
def formulaOf (φ : Std.Sat.CNF Nat) : Formula := ofList (normalizeList φ.clauses.toList)

/-- **Satisfiability is preserved.** -/
theorem cnf_sat_iff (φ : Std.Sat.CNF Nat) :
    (∃ a, φ.Sat a) ↔ ∃ a, (formulaOf φ).Sat a := by
  unfold formulaOf
  rw [← ofList_sat_iff, normalize_sat_iff]
  simp only [cnf_sat_iff_list]

/-- **No empty clause** after normalization. -/
theorem formulaOf_len_pos (φ : Std.Sat.CNF Nat) (c : Fin (formulaOf φ).M) :
    0 < (formulaOf φ).len c := by
  unfold formulaOf ofList
  simp only
  apply List.length_pos_of_ne_nil
  exact normalize_nonempty _ _ (List.get_mem _ c)

theorem ofList_K (L : List (List (ℕ × Bool))) : (ofList L).K = litCount L := by
  unfold Formula.K ofList litCount
  simp only
  rw [← List.sum_ofFn]
  conv_rhs => rw [← List.ofFn_get L]
  rw [List.map_ofFn]
  rfl

theorem varBound_normalize_le (L : List (List (ℕ × Bool))) :
    varBound (normalizeList L) ≤ varBound L := by
  unfold normalizeList
  split_ifs
  · have : varBound fixedUnsat = 1 := by decide
    rw [this]; unfold varBound; omega
  · exact le_refl _

theorem litCount_normalize_le (L : List (List (ℕ × Bool))) :
    litCount (normalizeList L) ≤ litCount L + 2 := by
  unfold normalizeList
  split_ifs
  · have : litCount fixedUnsat = 2 := by decide
    omega
  · omega

/-- **Size of the normalized formula.** `N ≤ 1 + (largest variable index of φ)`,
`K ≤ (number of literal occurrences of φ) + 2`, and `M ≤ K`. -/
theorem formulaOf_size (φ : Std.Sat.CNF Nat) :
    (formulaOf φ).N ≤ varBound φ.clauses.toList ∧
      (formulaOf φ).K ≤ litCount φ.clauses.toList + 2 ∧ (formulaOf φ).M ≤ (formulaOf φ).K := by
  refine ⟨varBound_normalize_le _, ?_, ?_⟩
  · unfold formulaOf
    rw [ofList_K]
    exact litCount_normalize_le _
  · unfold Formula.K
    calc (formulaOf φ).M = ∑ _c : Fin (formulaOf φ).M, 1 := by simp
      _ ≤ ∑ c, (formulaOf φ).len c :=
        Finset.sum_le_sum (fun c _ => formulaOf_len_pos φ c)

end QecReliability.SatReduction

open QecReliability.SatReduction in
#print axioms Formula.wt_of_sol
open QecReliability.SatReduction in
#print axioms Formula.sat_sol
open QecReliability.SatReduction in
#print axioms Formula.wt_ge
open QecReliability.SatReduction in
#print axioms Formula.wt_of_unsat
open QecReliability.SatReduction in
#print axioms Formula.ker_mem_span
open QecReliability.SatReduction in
#print axioms Formula.kerGens_ker
#print axioms QecReliability.SatReduction.cnf_sat_iff
#print axioms QecReliability.SatReduction.formulaOf_len_pos
#print axioms QecReliability.SatReduction.formulaOf_size
