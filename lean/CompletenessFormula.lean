import UncorrectableProbability
import QecReliability.SparseNormalizer
import Std.Tactic.BVDecide.LRAT.Checker

set_option autoImplicit false

/-!
# The completeness formula, built and interpreted inside Lean

`certFormula rows L mins units : Std.Sat.CNF Nat` says

  "there is an erased set `E` with `|E| ≤ L`, satisfying the unit constraints `units`,
   containing none of the listed sets `mins`, and vectors `x, z` with
   `x ∈ N(rowSpace rows)`, `supp x ⊆ E`, `z ∈ N(rowSpace rows)`, `⟪x, z⟫ = 1`".

`certFormula_unsat` proves that if this formula is unsatisfiable then every uncorrectable
erased set of size `≤ L` satisfying the unit constraints contains a listed set
(the certificate characterization `uncorrectable_iff_certificate` turns uncorrectability into
the existence of `x, z`). `certFormula_checked` composes this with the verified LRAT checker
`Std.Tactic.BVDecide.LRAT.check_sound`.

## Variable numbering (`n` qubits, `B = 5n + 2`)

* `e_i = i`, `x.1 i = n + i`, `x.2 i = 2n + i`, `z.1 i = 3n + i`, `z.2 i = 4n + i` (`i < n`);
* `5n` is the constant false, `5n + 1` the constant true (forced by unit clauses);
* auxiliary variables from `B` on, every one *defined* by a two-sided Tseitin gate
  (`xor`, `and`, `or`) from smaller variables:
  - `[B, B + I)`: prefix-XOR chains of the rows against `x` (`I = rowIncidences rows`),
  - `[B + I, B + 2I)`: the same against `z`,
  - `[P, P + 2n)` with `P = B + 2I`: products `x.1 i ∧ z.2 i` (at `P + i`) and
    `x.2 i ∧ z.1 i` (at `P + n + i`),
  - `[P + 2n, P + 4n)`: the XOR chain of the `2n` products,
  - `[C, C + 2n(L+1))` with `C = P + 4n`: a sequential counter
    `c(i+1, j+1) = c(i, j+1) ∨ (c(i, j) ∧ e_i)` with `c(i, 0) = true`, `c(0, j+1) = false`,
    the `and` at `C + 2((L+1)i + j)`, the `or` at `C + 2((L+1)i + j) + 1`.

Clauses: the two constants; the gate clauses (4 per XOR, 3 per AND/OR); `¬out` for every row
chain (orthogonality to the rows, for `x` and for `z`); `x.1 i → e_i`, `x.2 i → e_i`;
`out` for the product chain (`⟪x, z⟫ = 1`); `¬c(n, L+1)` (`|E| ≤ L`); one blocking clause
`⋁_{i ∈ M} ¬e_i` per listed `M`; one unit clause per element of `units`.

Coordinates: `.inl i` is the X (first) coordinate of qubit `i` (`coordPauli = Sum.elim xUnit
zUnit`); a row containing `.inl i` pairs with the *second* coordinate of the other vector.
-/

namespace QecPhysical.Stabilizer.Completeness

open Std.Sat
open QecReliability QecReliability.Binary QecReliability.SharedCircuit

/-! ## Gates -/

inductive GateOp
  | xor
  | and
  | or
  deriving DecidableEq, Repr

def GateOp.eval : GateOp → Bool → Bool → Bool
  | .xor, a, b => a ^^ b
  | .and, a, b => a && b
  | .or, a, b => a || b

/-- A gate defines the variable `out` as `op a b`. -/
structure Gate where
  out : Nat
  op : GateOp
  a : Nat
  b : Nat

/-- Full (two-sided) Tseitin clauses of a gate. -/
def Gate.clauses (g : Gate) : List (CNF.Clause Nat) :=
  match g.op with
  | .xor => [[(g.out, false), (g.a, true), (g.b, true)],
             [(g.out, false), (g.a, false), (g.b, false)],
             [(g.out, true), (g.a, false), (g.b, true)],
             [(g.out, true), (g.a, true), (g.b, false)]]
  | .and => [[(g.out, false), (g.a, true)], [(g.out, false), (g.b, true)],
             [(g.out, true), (g.a, false), (g.b, false)]]
  | .or => [[(g.out, true), (g.a, false)], [(g.out, true), (g.b, false)],
            [(g.out, false), (g.a, true), (g.b, true)]]

def Gate.OK (σ : Nat → Bool) (g : Gate) : Prop := σ g.out = g.op.eval (σ g.a) (σ g.b)

theorem Gate.clauses_sat (σ : Nat → Bool) (g : Gate) (h : g.OK σ) :
    ∀ c ∈ g.clauses, c.eval σ = true := by
  obtain ⟨t, op, a, b⟩ := g
  unfold Gate.OK at h
  rw [← List.all_eq_true]
  revert h
  cases op <;> simp only [Gate.clauses, GateOp.eval, List.all_cons, List.all_nil,
    CNF.Clause.eval_cons, CNF.Clause.eval_nil] <;>
    cases σ t <;> cases σ a <;> cases σ b <;> decide

/-! ## Variables -/

def eVar {n : ℕ} (i : Fin n) : Nat := i.val
def x1Var {n : ℕ} (i : Fin n) : Nat := n + i.val
def x2Var {n : ℕ} (i : Fin n) : Nat := 2 * n + i.val
def z1Var {n : ℕ} (i : Fin n) : Nat := 3 * n + i.val
def z2Var {n : ℕ} (i : Fin n) : Nat := 4 * n + i.val
def fVar (n : ℕ) : Nat := 5 * n
def tVar (n : ℕ) : Nat := 5 * n + 1
def baseEnd (n : ℕ) : Nat := 5 * n + 2

/-- Variable of the coordinate of `x` that a row coordinate pairs with. -/
def selX {n : ℕ} : PauliCoord n → Nat
  | .inl i => x2Var i
  | .inr i => x1Var i

def selZ {n : ℕ} : PauliCoord n → Nat
  | .inl i => z2Var i
  | .inr i => z1Var i

/-! ## Gadgets -/

/-- Prefix-XOR chain starting from `acc`; the `k`-th new variable is `s + k`. -/
def chainGates (acc : Nat) : List Nat → Nat → List Gate
  | [], _ => []
  | v :: vs, s => ⟨s, .xor, acc, v⟩ :: chainGates s vs (s + 1)

def chainOut (acc : Nat) : List Nat → Nat → Nat
  | [], _ => acc
  | _ :: vs, s => chainOut s vs (s + 1)

def rowGates {n : ℕ} (sel : PauliCoord n → Nat) (F : Nat) :
    List (List (PauliCoord n)) → Nat → List Gate
  | [], _ => []
  | r :: rs, s => chainGates F (r.map sel) s ++ rowGates sel F rs (s + r.length)

def rowOuts {n : ℕ} (sel : PauliCoord n → Nat) (F : Nat) :
    List (List (PauliCoord n)) → Nat → List Nat
  | [], _ => []
  | r :: rs, s => chainOut F (r.map sel) s :: rowOuts sel F rs (s + r.length)

def prodGates (n s : Nat) : List Gate :=
  List.ofFn (fun i : Fin n => (⟨s + i.val, .and, x1Var i, z2Var i⟩ : Gate)) ++
    List.ofFn (fun i : Fin n => (⟨s + n + i.val, .and, x2Var i, z1Var i⟩ : Gate))

def prodVars (n s : Nat) : List Nat :=
  List.ofFn (fun i : Fin n => s + i.val) ++ List.ofFn (fun i : Fin n => s + n + i.val)

def andOut (L C i j : Nat) : Nat := C + 2 * ((L + 1) * i + j)
def orOut (L C i j : Nat) : Nat := C + 2 * ((L + 1) * i + j) + 1

/-- `col n L C i j` is the variable "at least `j` of `e_0, …, e_{i-1}` are true". -/
def col (n L C : Nat) : Nat → Nat → Nat
  | 0, 0 => tVar n
  | 0, _ + 1 => fVar n
  | _ + 1, 0 => tVar n
  | i + 1, j + 1 => orOut L C i j

def counterGates (n L C : Nat) : List Gate :=
  (List.range n).flatMap fun i => (List.range (L + 1)).flatMap fun j =>
    [⟨andOut L C i j, .and, col n L C i j, i⟩, ⟨orOut L C i j, .or, col n L C i (j + 1), andOut L C i j⟩]

/-! ## The formula -/

section Layout
variable {n : ℕ} (rows : List (List (PauliCoord n))) (L : ℕ)

def zStart : Nat := baseEnd n + rowIncidences rows
def prodStart : Nat := baseEnd n + 2 * rowIncidences rows
def sympStart : Nat := prodStart rows + 2 * n
def counterStart : Nat := prodStart rows + 4 * n

def allGates : List Gate :=
  rowGates selX (fVar n) rows (baseEnd n) ++
  (rowGates selZ (fVar n) rows (zStart rows) ++
  (prodGates n (prodStart rows) ++
  (chainGates (fVar n) (prodVars n (prodStart rows)) (sympStart rows) ++
  counterGates n L (counterStart rows))))

def supportClauses : List (CNF.Clause Nat) :=
  (List.finRange n).flatMap fun i => [[(x1Var i, false), (eVar i, true)],
    [(x2Var i, false), (eVar i, true)]]

def certClauses (mins : List (List (Fin n))) (units : List (Fin n × Bool)) :
    List (CNF.Clause Nat) :=
  [[(fVar n, false)], [(tVar n, true)]] ++
  ((allGates rows L).flatMap Gate.clauses ++
  ((rowOuts selX (fVar n) rows (baseEnd n)).map (fun o => [(o, false)]) ++
  ((rowOuts selZ (fVar n) rows (zStart rows)).map (fun o => [(o, false)]) ++
  (supportClauses (n := n) ++
  ([[(chainOut (fVar n) (prodVars n (prodStart rows)) (sympStart rows), true)]] ++
  ([[(col n L (counterStart rows) n (L + 1), false)]] ++
  (mins.map (fun M => M.map fun i => (eVar i, false)) ++
  units.map (fun u => [(eVar u.1, u.2)]))))))))

/-- **The completeness formula.** -/
def certFormula (mins : List (List (Fin n))) (units : List (Fin n × Bool)) : CNF Nat :=
  ⟨(certClauses rows L mins units).toArray⟩

end Layout

/-! ## Assignments defined by the gates -/

/-- The assignment extending `σ0` through the gate definitions. -/
def extend (σ0 : Nat → Bool) (G : List Gate) (v : Nat) : Bool :=
  match G.find? (fun g => g.out == v) with
  | some g =>
    if h : g.a < v ∧ g.b < v then g.op.eval (extend σ0 G g.a) (extend σ0 G g.b) else false
  | none => σ0 v
termination_by v
decreasing_by all_goals omega

def Inj (G : List Gate) : Prop := ∀ g ∈ G, ∀ h ∈ G, g.out = h.out → g = h
def Inputs (G : List Gate) : Prop := ∀ g ∈ G, g.a < g.out ∧ g.b < g.out
def InRange (G : List Gate) (s t : Nat) : Prop := ∀ g ∈ G, s ≤ g.out ∧ g.out < t

theorem extend_ok (σ0 : Nat → Bool) (G : List Gate) (hI : Inj G) (hA : Inputs G) :
    ∀ g ∈ G, g.OK (extend σ0 G) := by
  intro g hg
  unfold Gate.OK
  have hsome : (G.find? (fun g' => g'.out == g.out)).isSome := by
    rw [List.find?_isSome]
    exact ⟨g, hg, by simp⟩
  obtain ⟨g', hg'⟩ := Option.isSome_iff_exists.mp hsome
  have hmem := List.mem_of_find?_eq_some hg'
  have hout : g'.out = g.out := by simpa using List.find?_some hg'
  have heq : g' = g := hI g' hmem g hg hout
  subst heq
  rw [extend, hg']
  simp only
  rw [dite_eq_left ⟨(hA g' hmem).1, (hA g' hmem).2⟩]

theorem extend_base (σ0 : Nat → Bool) (G : List Gate) (v : Nat) (hv : ∀ g ∈ G, g.out ≠ v) :
    extend σ0 G v = σ0 v := by
  have hnone : G.find? (fun g => g.out == v) = none := by
    rw [List.find?_eq_none]
    intro g hg
    simpa using hv g hg
  rw [extend, hnone]

theorem Inj.cons {g : Gate} {G : List Gate} (hG : Inj G) (hg : ∀ h ∈ G, h.out ≠ g.out) :
    Inj (g :: G) := by
  intro a ha b hb hab
  simp only [List.mem_cons] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · rfl
  · exact absurd hab.symm (hg b hb)
  · exact absurd hab (hg a ha)
  · exact hG a ha b hb hab

theorem Inj.append {G H : List Gate} {s t u : Nat} (hG : Inj G) (hH : Inj H)
    (rG : InRange G s t) (rH : InRange H t u) : Inj (G ++ H) := by
  intro a ha b hb hab
  simp only [List.mem_append] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hG a ha b hb hab
  · have := rG a ha; have := rH b hb; omega
  · have := rH a ha; have := rG b hb; omega
  · exact hH a ha b hb hab

theorem InRange.append {G H : List Gate} {s t u : Nat} (rG : InRange G s t)
    (rH : InRange H t u) (hst : s ≤ t) (htu : t ≤ u) : InRange (G ++ H) s u := by
  intro g hg
  simp only [List.mem_append] at hg
  rcases hg with hg | hg
  · have := rG g hg; omega
  · have := rH g hg; omega

theorem Inputs.append {G H : List Gate} (hG : Inputs G) (hH : Inputs H) : Inputs (G ++ H) := by
  intro g hg
  simp only [List.mem_append] at hg
  rcases hg with hg | hg
  · exact hG g hg
  · exact hH g hg

/-! ## Well-formedness of the gadgets -/

theorem chain_wf (acc : Nat) (vs : List Nat) (s : Nat) (hacc : acc < s)
    (hvs : ∀ v ∈ vs, v < s) :
    Inj (chainGates acc vs s) ∧ Inputs (chainGates acc vs s) ∧
      InRange (chainGates acc vs s) s (s + vs.length) := by
  induction vs generalizing acc s with
  | nil => simp [Inj, Inputs, InRange, chainGates]
  | cons v vs ih =>
    have hv : v < s := hvs v (by simp)
    obtain ⟨i1, i2, i3⟩ := ih s (s + 1) (by omega) (fun w hw => by
      have := hvs w (by simp [hw]); omega)
    refine ⟨Inj.cons i1 (fun h hh => by have := i3 h hh; simp; omega), ?_, ?_⟩
    · intro g hg
      simp only [chainGates, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨hacc, hv⟩
      · exact i2 g hg
    · intro g hg
      simp only [chainGates, List.mem_cons] at hg
      rcases hg with rfl | hg
      · simp
      · have := i3 g hg; simp only [List.length_cons]; omega

theorem rowIncidences_cons {n : ℕ} (r : List (PauliCoord n)) (rs : List (List (PauliCoord n))) :
    rowIncidences (r :: rs) = r.length + rowIncidences rs := by
  simp [rowIncidences]

theorem rowGates_wf {n : ℕ} (sel : PauliCoord n → Nat) (F : Nat) (rows : List (List (PauliCoord n)))
    (s : Nat) (hF : F < s) (hsel : ∀ c, sel c < s) :
    Inj (rowGates sel F rows s) ∧ Inputs (rowGates sel F rows s) ∧
      InRange (rowGates sel F rows s) s (s + rowIncidences rows) := by
  induction rows generalizing s with
  | nil => simp [Inj, Inputs, InRange, rowGates]
  | cons r rs ih =>
    obtain ⟨c1, c2, c3⟩ := chain_wf F (r.map sel) s hF (fun v hv => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hv; exact hsel c)
    obtain ⟨i1, i2, i3⟩ := ih (s + r.length) (by omega) (fun c => by have := hsel c; omega)
    simp only [List.length_map] at c3
    rw [rowIncidences_cons]
    refine ⟨Inj.append c1 i1 c3 i3, Inputs.append c2 i2, ?_⟩
    have := InRange.append c3 i3 (by omega) (by omega)
    simpa [rowGates, Nat.add_assoc] using this

theorem prod_wf (n s : Nat) (hs : 5 * n + 2 ≤ s) :
    Inj (prodGates n s) ∧ Inputs (prodGates n s) ∧ InRange (prodGates n s) s (s + 2 * n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [prodGates, List.mem_append, List.mem_ofFn] at ha hb
    rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hb with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp only at hab
    · have : i = j := Fin.ext (by omega)
      subst this; rfl
    · have := i.isLt; omega
    · have := j.isLt; omega
    · have : i = j := Fin.ext (by omega)
      subst this; rfl
  · intro g hg
    simp only [prodGates, List.mem_append, List.mem_ofFn] at hg
    rcases hg with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      simp only [x1Var, x2Var, z1Var, z2Var] <;> have := i.isLt <;> omega
  · intro g hg
    simp only [prodGates, List.mem_append, List.mem_ofFn] at hg
    rcases hg with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp only <;> have := i.isLt <;> omega

theorem lin_lt {L i j n : Nat} (hi : i < n) (hj : j ≤ L) : (L + 1) * i + j < (L + 1) * n := by
  have : (L + 1) * (i + 1) ≤ (L + 1) * n := Nat.mul_le_mul_left _ hi
  rw [Nat.mul_succ] at this
  omega

theorem lin_inj {L i j i' j' : Nat} (hj : j ≤ L) (hj' : j' ≤ L)
    (h : (L + 1) * i + j = (L + 1) * i' + j') : i = i' ∧ j = j' := by
  have key : ∀ {a b c d : Nat}, b ≤ L → a < c → (L + 1) * a + b < (L + 1) * c + d := by
    intro a b c d hb hac
    have : (L + 1) * (a + 1) ≤ (L + 1) * c := Nat.mul_le_mul_left _ hac
    rw [Nat.mul_succ] at this
    omega
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (key hj hlt))
  · subst heq; omega
  · exact absurd h.symm (Nat.ne_of_lt (key hj' hgt))

theorem col_lt (n L C i j : Nat) (hC : 5 * n + 2 ≤ C) (hj : j ≤ L + 1) :
    col n L C i j < C + 2 * ((L + 1) * i + j) := by
  cases i with
  | zero => cases j <;> simp [col, tVar, fVar] <;> omega
  | succ i =>
    cases j with
    | zero => simp [col, tVar]; omega
    | succ j =>
      simp only [col, orOut]
      rw [Nat.mul_succ]
      omega

theorem counter_wf (n L C : Nat) (hC : 5 * n + 2 ≤ C) :
    Inj (counterGates n L C) ∧ Inputs (counterGates n L C) ∧
      InRange (counterGates n L C) C (C + 2 * ((L + 1) * n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [counterGates, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at ha hb
    obtain ⟨i, hi, j, hj, rfl | rfl⟩ := ha <;> obtain ⟨i', hi', j', hj', rfl | rfl⟩ := hb <;>
      simp only [andOut, orOut] at hab
    · obtain ⟨rfl, rfl⟩ := lin_inj (by omega) (by omega) (by omega : (L + 1) * i + j = (L + 1) * i' + j')
      rfl
    · omega
    · omega
    · obtain ⟨rfl, rfl⟩ := lin_inj (by omega) (by omega) (by omega : (L + 1) * i + j = (L + 1) * i' + j')
      rfl
  · intro g hg
    simp only [counterGates, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    obtain ⟨i, hi, j, hj, rfl | rfl⟩ := hg
    · have := col_lt n L C i j hC (by omega)
      simp only [andOut]
      omega
    · have h1 := col_lt n L C i (j + 1) hC (by omega)
      cases i with
      | zero =>
        simp only [col, fVar, orOut, andOut]
        omega
      | succ i =>
        simp only [col, orOut, andOut] at h1 ⊢
        rw [Nat.mul_succ] at h1 ⊢
        omega
  · intro g hg
    simp only [counterGates, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    obtain ⟨i, hi, j, hj, rfl | rfl⟩ := hg
    · have := lin_lt (L := L) hi (Nat.lt_succ_iff.mp hj)
      simp only [andOut]; omega
    · have := lin_lt (L := L) hi (Nat.lt_succ_iff.mp hj)
      simp only [orOut]; omega

theorem allGates_wf {n : ℕ} (rows : List (List (PauliCoord n))) (L : ℕ) :
    Inj (allGates rows L) ∧ Inputs (allGates rows L) ∧
      InRange (allGates rows L) (baseEnd n) (counterStart rows + 2 * ((L + 1) * n)) := by
  have hX := rowGates_wf selX (fVar n) rows (baseEnd n) (by simp [fVar, baseEnd])
    (fun c => by cases c <;> simp [selX, x1Var, x2Var, baseEnd] <;> omega)
  have hZ := rowGates_wf selZ (fVar n) rows (zStart rows) (by simp [fVar, zStart, baseEnd]; omega)
    (fun c => by cases c <;> simp [selZ, z1Var, z2Var, zStart, baseEnd] <;> omega)
  have hP := prod_wf n (prodStart rows) (by simp [prodStart, baseEnd])
  have hC := chain_wf (fVar n) (prodVars n (prodStart rows)) (sympStart rows)
    (by simp [fVar, sympStart, prodStart, baseEnd]; omega)
    (fun v hv => by
      simp only [prodVars, List.mem_append, List.mem_ofFn] at hv
      rcases hv with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp [sympStart] <;> omega)
  have hK := counter_wf n L (counterStart rows) (by simp [counterStart, prodStart, baseEnd]; omega)
  have hlen : (prodVars n (prodStart rows)).length = 2 * n := by simp [prodVars]; omega
  rw [hlen] at hC
  have e1 : zStart rows = baseEnd n + rowIncidences rows := rfl
  have e2 : prodStart rows = zStart rows + rowIncidences rows := by
    simp [prodStart, zStart]; omega
  have e3 : sympStart rows = prodStart rows + 2 * n := rfl
  have e4 : counterStart rows = sympStart rows + 2 * n := by
    simp [counterStart, sympStart]; omega
  rw [← e1] at hX
  rw [← e2] at hZ
  rw [← e3] at hP
  rw [← e4] at hC
  have r4 := InRange.append hC.2.2 hK.2.2 (by omega) (by omega)
  have r3 := InRange.append hP.2.2 r4 (by omega) (by omega)
  have r2 := InRange.append hZ.2.2 r3 (by omega) (by omega)
  have r1 := InRange.append hX.2.2 r2 (by simp [e1]) (by omega)
  refine ⟨?_, ?_, r1⟩
  · exact Inj.append hX.1 (Inj.append hZ.1 (Inj.append hP.1 (Inj.append hC.1 hK.1
      hC.2.2 hK.2.2) hP.2.2 r4) hZ.2.2 r3) hX.2.2 r2
  · exact Inputs.append hX.2.1 (Inputs.append hZ.2.1 (Inputs.append hP.2.1
      (Inputs.append hC.2.1 hK.2.1)))

/-! ## Semantics of the gadgets -/

def xorList : List Bool → Bool
  | [] => false
  | b :: bs => b ^^ xorList bs

theorem xorList_append (l1 l2 : List Bool) : xorList (l1 ++ l2) = (xorList l1 ^^ xorList l2) := by
  induction l1 with
  | nil => simp [xorList]
  | cons b bs ih => simp [xorList, ih]

theorem chain_value (σ : Nat → Bool) (acc : Nat) (vs : List Nat) (s : Nat)
    (h : ∀ g ∈ chainGates acc vs s, g.OK σ) :
    σ (chainOut acc vs s) = (σ acc ^^ xorList (vs.map σ)) := by
  induction vs generalizing acc s with
  | nil => simp [chainOut, xorList]
  | cons v vs ih =>
    have h0 := h ⟨s, .xor, acc, v⟩ (by simp [chainGates])
    have h1 := ih s (s + 1) (fun g hg => h g (by simp [chainGates, hg]))
    simp only [chainOut, List.map_cons, xorList]
    rw [h1]
    simp only [Gate.OK, GateOp.eval] at h0
    rw [h0, Bool.xor_assoc]

theorem rowOuts_spec {n : ℕ} (sel : PauliCoord n → Nat) (F : Nat)
    (rows : List (List (PauliCoord n))) (s : Nat) :
    ∀ o ∈ rowOuts sel F rows s, ∃ r ∈ rows, ∃ s', o = chainOut F (r.map sel) s' ∧
      ∀ g ∈ chainGates F (r.map sel) s', g ∈ rowGates sel F rows s := by
  induction rows generalizing s with
  | nil => simp [rowOuts]
  | cons r rs ih =>
    intro o ho
    simp only [rowOuts, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact ⟨r, by simp, s, rfl, fun g hg => by simp [rowGates, hg]⟩
    · obtain ⟨r', hr', s', rfl, hsub⟩ := ih (s + r.length) o ho
      exact ⟨r', by simp [hr'], s', rfl, fun g hg => by simp [rowGates, hsub g hg]⟩

/-! ## Binary values -/

def bb (b : Bit) : Bool := decide (b = 1)

theorem bb_add (a b : Bit) : bb (a + b) = (bb a ^^ bb b) := by
  revert a b; decide

theorem bb_mul (a b : Bit) : bb (a * b) = (bb a && bb b) := by
  revert a b; decide

@[simp] theorem bb_zero : bb 0 = false := by decide
@[simp] theorem bb_one : bb 1 = true := by decide

theorem bb_sum (l : List Bit) : bb l.sum = xorList (l.map bb) := by
  induction l with
  | nil => simp [xorList]
  | cons a l ih => simp [xorList, bb_add, ih]

theorem symplectic_xUnit_left {n : ℕ} (i : Fin n) (w : Pauli n) :
    symplectic n (xUnit i) w = w.2 i := by
  simp [symplectic_apply, xUnit, Pi.single_apply]

theorem symplectic_zUnit_left {n : ℕ} (i : Fin n) (w : Pauli n) :
    symplectic n (zUnit i) w = w.1 i := by
  simp [symplectic_apply, zUnit, Pi.single_apply]

/-- The pairing of a sparse row with `w` is the sum of the selected coordinates. -/
theorem symplectic_decodeRow {n : ℕ} (row : List (PauliCoord n)) (w : Pauli n) :
    symplectic n (decodeRow row) w =
      (row.map (Sum.elim (fun i => w.2 i) (fun i => w.1 i))).sum := by
  induction row with
  | nil => simp [decodeRow]
  | cons c row ih =>
    have hd : decodeRow (c :: row) = coordPauli c + decodeRow row := by simp [decodeRow]
    rw [hd, map_add, LinearMap.add_apply, ih, List.map_cons, List.sum_cons]
    congr 1
    cases c with
    | inl i => exact symplectic_xUnit_left i w
    | inr i => exact symplectic_zUnit_left i w

/-! ## The assignment built from a counterexample -/

section Witness

variable {n : ℕ}

noncomputable def baseAssign (E : Finset (Fin n)) (x z : Pauli n) (v : Nat) : Bool :=
  if h : v < n then decide ((⟨v, h⟩ : Fin n) ∈ E)
  else if h1 : v < 2 * n then bb (x.1 ⟨v - n, by omega⟩)
  else if h2 : v < 3 * n then bb (x.2 ⟨v - 2 * n, by omega⟩)
  else if h3 : v < 4 * n then bb (z.1 ⟨v - 3 * n, by omega⟩)
  else if h4 : v < 5 * n then bb (z.2 ⟨v - 4 * n, by omega⟩)
  else decide (v = 5 * n + 1)

variable (E : Finset (Fin n)) (x z : Pauli n)

theorem base_e (i : Fin n) : baseAssign E x z (eVar i) = decide (i ∈ E) := by
  unfold baseAssign eVar
  rw [dite_eq_left i.isLt]

theorem base_x1 (i : Fin n) : baseAssign E x z (x1Var i) = bb (x.1 i) := by
  have := i.isLt
  unfold baseAssign x1Var
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  exact congrArg _ (congrArg _ (Fin.ext (by simp)))

theorem base_x2 (i : Fin n) : baseAssign E x z (x2Var i) = bb (x.2 i) := by
  have := i.isLt
  unfold baseAssign x2Var
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  exact congrArg _ (congrArg _ (Fin.ext (by simp)))

theorem base_z1 (i : Fin n) : baseAssign E x z (z1Var i) = bb (z.1 i) := by
  have := i.isLt
  unfold baseAssign z1Var
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  exact congrArg _ (congrArg _ (Fin.ext (by simp)))

theorem base_z2 (i : Fin n) : baseAssign E x z (z2Var i) = bb (z.2 i) := by
  have := i.isLt
  unfold baseAssign z2Var
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_left (by omega)]
  exact congrArg _ (congrArg _ (Fin.ext (by simp)))

theorem base_f : baseAssign E x z (fVar n) = false := by
  unfold baseAssign fVar
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega)]
  simp

theorem base_t : baseAssign E x z (tVar n) = true := by
  unfold baseAssign tVar
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega)]
  simp

/-- Number of true variables among `0, …, i-1`. -/
def cnt (σ : Nat → Bool) (i : Nat) : Nat := ∑ k ∈ Finset.range i, if σ k then 1 else 0

theorem col_value (σ : Nat → Bool) (L C : Nat)
    (hok : ∀ g ∈ counterGates n L C, g.OK σ) (hT : σ (tVar n) = true) (hF : σ (fVar n) = false) :
    ∀ i ≤ n, ∀ j ≤ L + 1, σ (col n L C i j) = decide (j ≤ cnt σ i) := by
  intro i
  induction i with
  | zero =>
    intro _ j _
    cases j with
    | zero => simp [col, hT]
    | succ j => simp [col, hF, cnt]
  | succ i ih =>
    intro hi j hj
    cases j with
    | zero => simp [col, hT]
    | succ j =>
      have hmem : ∀ g ∈ [(⟨andOut L C i j, .and, col n L C i j, i⟩ : Gate),
          ⟨orOut L C i j, .or, col n L C i (j + 1), andOut L C i j⟩], g ∈ counterGates n L C := by
        intro g hg
        simp only [counterGates, List.mem_flatMap, List.mem_range]
        exact ⟨i, by omega, j, by omega, hg⟩
      have hand := hok _ (hmem ⟨andOut L C i j, .and, col n L C i j, i⟩ (by simp))
      have hor := hok _ (hmem ⟨orOut L C i j, .or, col n L C i (j + 1), andOut L C i j⟩ (by simp))
      simp only [Gate.OK, GateOp.eval] at hand hor
      have h1 := ih (by omega) j (by omega)
      have h2 := ih (by omega) (j + 1) (by omega)
      simp only [col]
      rw [hor, hand, h1, h2]
      have hc : cnt σ (i + 1) = cnt σ i + (if σ i then 1 else 0) := by
        unfold cnt
        rw [Finset.sum_range_succ]
      rw [hc]
      cases σ i <;> simp <;> omega

theorem cnt_base (G : List Gate) (hG : ∀ g ∈ G, baseEnd n ≤ g.out) :
    cnt (extend (baseAssign E x z) G) n = E.card := by
  have hval : ∀ k < n, extend (baseAssign E x z) G k = baseAssign E x z k := fun k hk =>
    extend_base _ _ _ (fun g hg => by have := hG g hg; simp [baseEnd] at this; omega)
  unfold cnt
  rw [Finset.sum_congr rfl (fun k hk => by rw [hval k (Finset.mem_range.mp hk)])]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if baseAssign E x z k then 1 else 0)]
  have : ∀ i : Fin n, (if baseAssign E x z i.val then 1 else 0) = if i ∈ E then 1 else 0 := by
    intro i
    have := base_e E x z i
    simp only [eVar] at this
    rw [this]; simp
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_boole]
  simp

end Witness

/-! ## Main theorem -/

theorem cnf_eval_toArray (σ : Nat → Bool) (l : List (CNF.Clause Nat)) :
    CNF.eval σ ⟨l.toArray⟩ = l.all (fun c => c.eval σ) := by
  simp [CNF.eval]

/-- A counterexample to completeness gives a satisfying assignment of the formula. -/
theorem certFormula_sat {n : ℕ} (rows : List (List (PauliCoord n))) (L : ℕ)
    (mins : List (List (Fin n))) (units : List (Fin n × Bool)) (E : Finset (Fin n))
    (hE : E.card ≤ L) (hunits : ∀ u ∈ units, (u.1 ∈ E ↔ u.2 = true))
    (hmins : ∀ M ∈ mins, ¬ M.toFinset ⊆ E) (x z : Pauli n)
    (hxN : x ∈ normalizer (symplectic n) (rowSpace rows)) (hxE : x ∈ supported E)
    (hzN : z ∈ normalizer (symplectic n) (rowSpace rows)) (hxz : symplectic n x z = 1) :
    (certFormula rows L mins units).eval (extend (baseAssign E x z) (allGates rows L)) = true := by
  set G := allGates rows L with hGdef
  set σ := extend (baseAssign E x z) G with hσ
  obtain ⟨hInj, hInp, hRange⟩ := allGates_wf rows L
  have hok : ∀ g ∈ G, g.OK σ := extend_ok _ G hInj hInp
  have hbase : ∀ v < baseEnd n, σ v = baseAssign E x z v := fun v hv =>
    extend_base _ _ _ (fun g hg => by have := hRange g hg; omega)
  have se : ∀ i : Fin n, σ (eVar i) = decide (i ∈ E) := fun i => by
    rw [hbase _ (by simp [eVar, baseEnd]; omega), base_e]
  have sx1 : ∀ i : Fin n, σ (x1Var i) = bb (x.1 i) := fun i => by
    rw [hbase _ (by simp [x1Var, baseEnd]; omega), base_x1]
  have sx2 : ∀ i : Fin n, σ (x2Var i) = bb (x.2 i) := fun i => by
    rw [hbase _ (by simp [x2Var, baseEnd]; omega), base_x2]
  have sz1 : ∀ i : Fin n, σ (z1Var i) = bb (z.1 i) := fun i => by
    rw [hbase _ (by simp [z1Var, baseEnd]; omega), base_z1]
  have sz2 : ∀ i : Fin n, σ (z2Var i) = bb (z.2 i) := fun i => by
    rw [hbase _ (by simp [z2Var, baseEnd]; omega), base_z2]
  have sF : σ (fVar n) = false := by rw [hbase _ (by simp [fVar, baseEnd]), base_f]
  have sT : σ (tVar n) = true := by rw [hbase _ (by simp [tVar, baseEnd]), base_t]
  -- membership of the gadgets in `G`
  have mX : ∀ g ∈ rowGates selX (fVar n) rows (baseEnd n), g ∈ G := fun g hg => by
    simp [hGdef, allGates, hg]
  have mZ : ∀ g ∈ rowGates selZ (fVar n) rows (zStart rows), g ∈ G := fun g hg => by
    simp [hGdef, allGates, hg]
  have mP : ∀ g ∈ prodGates n (prodStart rows), g ∈ G := fun g hg => by
    simp [hGdef, allGates, hg]
  have mS : ∀ g ∈ chainGates (fVar n) (prodVars n (prodStart rows)) (sympStart rows), g ∈ G :=
    fun g hg => by simp [hGdef, allGates, hg]
  have mK : ∀ g ∈ counterGates n L (counterStart rows), g ∈ G := fun g hg => by
    simp [hGdef, allGates, hg]
  -- row chains
  have hrows : ∀ (sel : PauliCoord n → Nat) (w : Pauli n) (s : Nat),
      w ∈ normalizer (symplectic n) (rowSpace rows) →
      (∀ c, σ (sel c) = bb (Sum.elim (fun i => w.2 i) (fun i => w.1 i) c)) →
      (∀ g ∈ rowGates sel (fVar n) rows s, g ∈ G) →
      ∀ o ∈ rowOuts sel (fVar n) rows s, σ o = false := by
    intro sel w s hw hsel hmem o ho
    obtain ⟨r, hr, s', rfl, hsub⟩ := rowOuts_spec sel (fVar n) rows s o ho
    rw [chain_value σ _ _ _ (fun g hg => hok g (hmem g (hsub g hg))), sF, List.map_map]
    have hfun : (σ ∘ sel) = (bb ∘ Sum.elim (fun i => w.2 i) (fun i => w.1 i)) := by
      funext c; exact hsel c
    rw [hfun, ← List.map_map, ← bb_sum, ← symplectic_decodeRow,
      (mem_normalizer_rows rows w).mp hw r hr]
    simp
  have hselX : ∀ c, σ (selX c) = bb (Sum.elim (fun i => x.2 i) (fun i => x.1 i) c) := by
    intro c; cases c <;> simp [selX, sx1, sx2]
  have hselZ : ∀ c, σ (selZ c) = bb (Sum.elim (fun i => z.2 i) (fun i => z.1 i) c) := by
    intro c; cases c <;> simp [selZ, sz1, sz2]
  -- the symplectic chain
  have hsymp : σ (chainOut (fVar n) (prodVars n (prodStart rows)) (sympStart rows)) = true := by
    rw [chain_value σ _ _ _ (fun g hg => hok g (mS g hg)), sF]
    have hp1 : ∀ i : Fin n, σ (prodStart rows + i.val) = bb (x.1 i * z.2 i) := fun i => by
      have := hok _ (mP _ (by simp [prodGates]; exact Or.inl ⟨i, rfl⟩))
      simp only [Gate.OK, GateOp.eval] at this
      rw [this, sx1, sz2, bb_mul]
    have hp2 : ∀ i : Fin n, σ (prodStart rows + n + i.val) = bb (x.2 i * z.1 i) := fun i => by
      have := hok _ (mP _ (by simp [prodGates]; exact Or.inr ⟨i, rfl⟩))
      simp only [Gate.OK, GateOp.eval] at this
      rw [this, sx2, sz1, bb_mul]
    simp only [prodVars, List.map_append, List.map_ofFn]
    have e1 : (σ ∘ fun i : Fin n => prodStart rows + i.val) = fun i => bb (x.1 i * z.2 i) := by
      funext i; exact hp1 i
    have e2 : (σ ∘ fun i : Fin n => prodStart rows + n + i.val) =
        fun i => bb (x.2 i * z.1 i) := by
      funext i; exact hp2 i
    rw [e1, e2, xorList_append]
    have l1 : (List.ofFn fun i : Fin n => bb (x.1 i * z.2 i)) =
        (List.ofFn fun i : Fin n => x.1 i * z.2 i).map bb := by simp [List.map_ofFn]; rfl
    have l2 : (List.ofFn fun i : Fin n => bb (x.2 i * z.1 i)) =
        (List.ofFn fun i : Fin n => x.2 i * z.1 i).map bb := by simp [List.map_ofFn]; rfl
    rw [l1, l2, ← bb_sum, ← bb_sum, ← bb_add, List.sum_ofFn, List.sum_ofFn,
      ← Finset.sum_add_distrib, ← symplectic_apply, hxz]
    simp
  -- the counter
  have hcount : σ (col n L (counterStart rows) n (L + 1)) = false := by
    rw [col_value σ L _ (fun g hg => hok g (mK g hg)) sT sF n le_rfl (L + 1) le_rfl,
      cnt_base E x z G (fun g hg => (hRange g hg).1)]
    simp; omega
  -- all clauses
  rw [certFormula, cnf_eval_toArray, List.all_eq_true]
  intro c hc
  simp only [certClauses, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_flatMap] at hc
  rcases hc with ((rfl | rfl) | ⟨g, hg, hcg⟩ | ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩ | hsupp | rfl | rfl |
      ⟨M, hM, rfl⟩ | ⟨u, hu, rfl⟩)
  · simp [CNF.Clause.eval, sF]
  · simp [CNF.Clause.eval, sT]
  · exact Gate.clauses_sat σ g (hok g hg) c hcg
  · simp [CNF.Clause.eval, hrows selX x _ hxN hselX mX o ho]
  · simp [CNF.Clause.eval, hrows selZ z _ hzN hselZ mZ o ho]
  · simp only [supportClauses, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.not_mem_nil, or_false] at hsupp
    obtain ⟨i, rfl | rfl⟩ := hsupp
    · by_cases hi : i ∈ E
      · simp [CNF.Clause.eval, se, hi]
      · simp [CNF.Clause.eval, se, hi, sx1, (hxE i hi).1]
    · by_cases hi : i ∈ E
      · simp [CNF.Clause.eval, se, hi]
      · simp [CNF.Clause.eval, se, hi, sx2, (hxE i hi).2]
  · simp [CNF.Clause.eval, hsymp]
  · simp [CNF.Clause.eval, hcount]
  · obtain ⟨i, hiM, hiE⟩ := Finset.not_subset.mp (hmins M hM)
    simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
    exact ⟨i, List.mem_toFinset.mp hiM, by simp [se, hiE]⟩
  · have := hunits u hu
    cases hb : u.2 <;> simp_all [CNF.Clause.eval, se]

/-- **Meaning of unsatisfiability.** If `certFormula rows L mins units` is unsatisfiable, then
every uncorrectable erased set `E` with `|E| ≤ L` that satisfies the unit constraints
contains one of the listed sets. -/
theorem certFormula_unsat {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L : ℕ)
    (mins : List (List (Fin n))) (units : List (Fin n × Bool))
    (h : (certFormula rows L mins units).Unsat) :
    ∀ E : Finset (Fin n), E.card ≤ L → (∀ u ∈ units, (u.1 ∈ E ↔ u.2 = true)) →
      0 < ambiguity (symplectic n) (rowSpace rows) (supported E) →
        ∃ M ∈ mins, M.toFinset ⊆ E := by
  intro E hE hunits hamb
  by_contra hno
  have hmins : ∀ M ∈ mins, ¬ M.toFinset ⊆ E := fun M hM hsub => hno ⟨M, hM, hsub⟩
  obtain ⟨x, hx, z, hzN, hxz⟩ :=
    (Uncorrectable.uncorrectable_iff_certificate (rowSpace rows) hS E).mp hamb
  have hsat := certFormula_sat rows L mins units E hE hunits hmins x z hx.1 hx.2 hzN hxz
  rw [h _] at hsat
  exact Bool.false_ne_true hsat

/-- **Composition with the verified LRAT checker.** -/
theorem certFormula_checked {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L : ℕ)
    (mins : List (List (Fin n))) (units : List (Fin n × Bool))
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (h : Std.Tactic.BVDecide.LRAT.check proof (certFormula rows L mins units) = true) :
    ∀ E : Finset (Fin n), E.card ≤ L → (∀ u ∈ units, (u.1 ∈ E ↔ u.2 = true)) →
      0 < ambiguity (symplectic n) (rowSpace rows) (supported E) →
        ∃ M ∈ mins, M.toFinset ⊆ E :=
  certFormula_unsat rows hS L mins units
    (Std.Tactic.BVDecide.LRAT.check_sound proof _ h)

/-! ## Sanity checks on the 3-qubit repetition code (checks `Z0 Z1`, `Z1 Z2`) -/

/-- Rows of the 3-qubit repetition code. -/
def repRows : List (List (PauliCoord 3)) := [[.inr 0, .inr 1], [.inr 1, .inr 2]]

set_option maxRecDepth 20000 in
/-- The formula for `L = 1` and the three singletons has 127 clauses over 49 variables. -/
theorem rep_size : (certClauses repRows 1 [[0], [1], [2]] []).length = 127 := by decide

/-- Dropping the singleton `{2}` makes the formula satisfiable: the model below is
`E = {2}`, `x = Z_2` (variable `2n + 2 = 8`), `z = X_0 X_1 X_2` (variables `9, 10, 11`) plus the
gate outputs, as found by CaDiCaL on the emitted DIMACS file. So an incomplete list is not
certified. -/
theorem rep_incomplete_sat :
    (certFormula repRows 1 [[0], [1]] []).Sat
      (fun v => v ∈ [2, 8, 9, 10, 11, 16, 21, 23, 30, 36, 45, 46]) := by
  rw [CNF.sat_def, certFormula, cnf_eval_toArray]
  decide

end QecPhysical.Stabilizer.Completeness

#print axioms QecPhysical.Stabilizer.Completeness.certFormula_unsat
#print axioms QecPhysical.Stabilizer.Completeness.certFormula_checked
#print axioms QecPhysical.Stabilizer.Completeness.rep_size
#print axioms QecPhysical.Stabilizer.Completeness.rep_incomplete_sat
