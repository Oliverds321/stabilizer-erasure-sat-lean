import QecReliability.PrefixEnumeration

/-! Concrete bounded-width CNFs and unit-clause prefix restrictions. This does not
compile arbitrary semantic predicates, quantum certificates, or hash circuits. -/

namespace QecReliability
namespace PrefixCNF
open PrefixEnumeration

abbrev Literal (v : ℕ) := Fin v × Bool
abbrev Formula (v : ℕ) := List (List (Literal v))

def evalClause {v : ℕ} (c : List (Literal v)) (a : BitModels v) : Bool :=
  c.any (fun lit => a lit.1 == lit.2)

def eval {v : ℕ} (F : Formula v) (a : BitModels v) : Bool := F.all (fun c => evalClause c a)

def Width {v : ℕ} (k : ℕ) (F : Formula v) : Prop := ∀ c ∈ F, c.length ≤ k

def shift {v : ℕ} (F : Formula v) : Formula (v + 1) :=
  F.map (fun c => c.map (fun lit => (lit.1.succ, lit.2)))

theorem eval_shift {v : ℕ} (F : Formula v) (b : Bool) (a : BitModels v) :
    eval (shift F) (Fin.cons b a) = eval F a := by
  simp [eval, evalClause, shift, List.all_map, List.any_map, Function.comp_def]

theorem width_shift {v k : ℕ} {F : Formula v} (h : Width k F) : Width k (shift F) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa using h d hd

/-- Add one unit clause per prescribed projection bit. An overlong prefix is inconsistent. -/
def units : (q w : ℕ) → List Bool → Formula (q + w)
  | 0, _, [] => []
  | 0, _, _ :: _ => [[]]
  | q + 1, w, [] => []
  | q + 1, w, b :: pre =>
      [(⟨0, by omega⟩, b)] ::
        (shift (units q w pre)).map (fun c => c.map (fun lit => (Fin.cast (by omega) lit.1, lit.2)))

theorem eval_cast {v v' : ℕ} (h : v = v') (F : Formula v) (a : BitModels v') :
    eval (F.map (fun c => c.map (fun lit => (Fin.cast h lit.1, lit.2)))) a =
      eval F (fun i => a (Fin.cast h i)) := by
  simp [eval, evalClause, List.all_map, List.any_map, Function.comp_def]

theorem units_width (q w : ℕ) (pre : List Bool) : Width 1 (units q w pre) := by
  induction q generalizing pre with
  | zero => cases pre <;> simp [units, Width]
  | succ q ih =>
    cases pre with
    | nil => simp [units, Width]
    | cons b pre =>
      intro c hc
      simp only [units, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        simpa using width_shift (ih pre) d hd

theorem units_length (q w : ℕ) (pre : List Bool) (hlen : pre.length ≤ q) :
    (units q w pre).length = pre.length := by
  induction q generalizing pre with
  | zero => cases pre <;> simp_all [units]
  | succ q ih =>
    cases pre with
    | nil => simp [units]
    | cons b pre =>
      simp only [List.length_cons] at hlen
      simp [units, shift, ih pre (by omega)]

theorem units_length_bound (q w : ℕ) (pre : List Bool) : (units q w pre).length ≤ q + 1 := by
  induction q generalizing pre with
  | zero => cases pre <;> simp [units]
  | succ q ih =>
    cases pre with
    | nil => simp [units]
    | cons b pre => simpa [units, shift] using Nat.succ_le_succ (ih pre)

theorem units_eval (q w : ℕ) (pre : List Bool) (a : BitModels q) (b : BitModels w) :
    eval (units q w pre) (Fin.append a b) = true ↔ pre <+: List.ofFn a := by
  induction q generalizing pre with
  | zero => cases pre <;> simp [units, eval, evalClause]
  | succ q ih =>
    cases pre with
    | nil => simp [units, eval]
    | cons bit pre =>
      have ha : a = Fin.cons (a 0) (Fin.tail a) := (Fin.cons_self_tail a).symm
      rw [ha, List.ofFn_cons, List.cons_prefix_cons]
      simp only [units, eval, List.all_cons, Bool.and_eq_true]
      have hcast : (fun i : Fin (q + w + 1) =>
          Fin.append (Fin.cons (a 0) (Fin.tail a)) b (Fin.cast (by omega) i)) =
          Fin.cons (a 0) (Fin.append (Fin.tail a) b) := by
        funext i
        have hindex :
            Fin.cast (Nat.add_right_comm q 1 w)
              (Fin.cast (by omega : q + w + 1 = q + 1 + w) i) = i := by
          apply Fin.ext
          rfl
        simpa only [Function.comp_def, hindex] using
          congrFun (Fin.append_cons (a 0) (Fin.tail a) b)
            (Fin.cast (by omega : q + w + 1 = q + 1 + w) i)
      change evalClause [(⟨0, by omega⟩, bit)] (Fin.append (Fin.cons (a 0) (Fin.tail a)) b) = true ∧
        eval _ (Fin.append (Fin.cons (a 0) (Fin.tail a)) b) = true ↔ _
      rw [eval_cast, hcast, eval_shift, ih]
      have hzero : Fin.append (Fin.cons (a 0) (Fin.tail a)) b (⟨0, by omega⟩) = a 0 := by
        change Fin.append (Fin.cons (a 0) (Fin.tail a)) b (Fin.castAdd w (0 : Fin (q + 1))) = a 0
        rw [Fin.append_left, Fin.cons_zero]
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, hzero, beq_iff_eq]
      exact and_congr_left (fun _ => eq_comm)

def restrict {q w : ℕ} (F : Formula (q + w)) (pre : List Bool) : Formula (q + w) :=
  F ++ units q w pre

def Projected {q w : ℕ} (F : Formula (q + w)) (a : BitModels q) : Prop :=
  ∃ b : BitModels w, eval F (Fin.append a b) = true

theorem restrict_eval {q w : ℕ} (F : Formula (q + w)) (pre : List Bool)
    (a : BitModels q) (b : BitModels w) :
    eval (restrict F pre) (Fin.append a b) = true ↔
      eval F (Fin.append a b) = true ∧ pre <+: List.ofFn a := by
  simp only [restrict, eval, List.all_append, Bool.and_eq_true]
  exact and_congr_right (fun _ => units_eval q w pre a b)

theorem restrict_width {q w k : ℕ} {F : Formula (q + w)} (hF : Width k F) (hk : 1 ≤ k)
    (pre : List Bool) : Width k (restrict F pre) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hF c hc
  · exact (units_width q w pre c hc).trans hk

theorem restrict_length {q w : ℕ} (F : Formula (q + w)) (pre : List Bool) (hlen : pre.length ≤ q) :
    (restrict F pre).length = F.length + pre.length := by
  simp [restrict, units_length q w pre hlen]

theorem restrict_length_bound {q w : ℕ} (F : Formula (q + w)) (pre : List Bool) :
    (restrict F pre).length ≤ F.length + q + 1 := by
  simpa [restrict, Nat.add_assoc] using Nat.add_le_add_left (units_length_bound q w pre) F.length

/-- Splitting physical SAT assignments into projection bits and witness bits preserves existence. -/
theorem restrict_sat {q w : ℕ} (F : Formula (q + w)) (pre : List Bool) :
    (∃ z, eval (restrict F pre) z = true) ↔ PrefixSat (Projected F) pre := by
  constructor
  · rintro ⟨z, hz⟩
    let a : BitModels q := fun i => z (Fin.castAdd w i)
    let b : BitModels w := fun i => z (Fin.natAdd q i)
    have he : Fin.append a b = z := Fin.append_castAdd_natAdd
    rw [← he, restrict_eval] at hz
    exact ⟨a, ⟨b, hz.1⟩, hz.2⟩
  · rintro ⟨a, ⟨b, hab⟩, hpre⟩
    exact ⟨Fin.append a b, (restrict_eval F pre a b).mpr ⟨hab, hpre⟩⟩

/-- Concrete CNF input, Boolean output, semantic correctness restricted to width k. -/
structure ExactSAT (v k : ℕ) where
  solve : Formula v → Bool
  correct : ∀ F, Width k F → (solve F = true ↔ ∃ a, eval F a = true)

/-- Executable exhaustive reference solver. No favorable complexity claim is attached. -/
def exhaustiveSAT (v k : ℕ) : ExactSAT v k where
  solve F := decide (∃ a : BitModels v, eval F a = true)
  correct F _hF := by simp

def prefixDecision {q w k : ℕ} (solver : ExactSAT (q + w) k)
    (F : Formula (q + w)) (hF : Width k F) (hk : 1 ≤ k) : ExactDecision (Projected F) where
  answer pre := solver.solve (restrict F pre)
  correct pre := (solver.correct _ (restrict_width hF hk pre)).trans (restrict_sat F pre)

theorem projected_enumeration {q w k : ℕ} (solver : ExactSAT (q + w) k)
    (F : Formula (q + w)) (hF : Width k F) (hk : 1 ≤ k) (cap : ℕ) :
    (enumerate q (fun pre => solver.solve (restrict F pre)) cap).1 =
        min cap (modelCount (Projected F)) ∧
      (enumerate q (fun pre => solver.solve (restrict F pre)) cap).2 ≤
        1 + 2 * q * min cap (modelCount (Projected F)) :=
  enumerate_spec (prefixDecision solver F hF hk) cap

end PrefixCNF
end QecReliability
