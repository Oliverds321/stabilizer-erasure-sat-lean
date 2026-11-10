import QecReliability.SharedCircuitCore
import QecReliability.PrefixCNF

/-! Acyclic shared-wire Boolean circuits. Every gate references only earlier wires;
fan-out is represented by reusing an index, not by expanding expression trees. -/

namespace QecReliability
namespace SharedCircuit
open PrefixCNF

namespace Gate

/-- Full-equivalence clauses, not a one-way implication. -/
def clauses {v : ℕ} (out : Fin v) : Gate v → Formula v
  | andGate x y => [[(x, false), (y, false), (out, true)],
      [(x, true), (out, false)], [(y, true), (out, false)]]
  | xorGate x y => [[(x, true), (y, true), (out, false)],
      [(x, true), (y, false), (out, true)],
      [(x, false), (y, true), (out, true)],
      [(x, false), (y, false), (out, false)]]
  | notGate x => [[(x, true), (out, true)], [(x, false), (out, false)]]
  | constGate b => [[(out, b)]]

theorem clauses_correct {v : ℕ} (g : Gate v) (out : Fin v) (a : BitModels v) :
    PrefixCNF.eval (g.clauses out) a = true ↔ a out = g.eval a := by
  cases g with
  | andGate x y =>
    cases hx : a x <;> cases hy : a y <;> cases ho : a out <;>
      simp [clauses, PrefixCNF.eval, evalClause, eval, hx, hy, ho]
  | xorGate x y =>
    cases hx : a x <;> cases hy : a y <;> cases ho : a out <;>
      simp [clauses, PrefixCNF.eval, evalClause, eval, hx, hy, ho]
  | notGate x =>
    cases hx : a x <;> cases ho : a out <;>
      simp [clauses, PrefixCNF.eval, evalClause, eval, hx, ho]
  | constGate b => cases b <;> cases ho : a out <;>
      simp [clauses, PrefixCNF.eval, evalClause, eval, ho]

theorem clauses_width {v : ℕ} (g : Gate v) (out : Fin v) : Width 3 (g.clauses out) := by
  cases g <;> simp [clauses, Width]

theorem clauses_length {v : ℕ} (g : Gate v) (out : Fin v) : (g.clauses out).length ≤ 4 := by
  cases g <;> simp [clauses]

end Gate

def rename {v w : ℕ} (f : Fin v → Fin w) (F : Formula v) : Formula w :=
  F.map (fun c => c.map (fun lit => (f lit.1, lit.2)))

theorem eval_rename {v w : ℕ} (f : Fin v → Fin w) (F : Formula v) (a : BitModels w) :
    PrefixCNF.eval (rename f F) a = PrefixCNF.eval F (fun i => a (f i)) := by
  simp [rename, PrefixCNF.eval, evalClause, List.all_map, List.any_map, Function.comp_def]

theorem width_rename {v w k : ℕ} (f : Fin v → Fin w) (F : Formula v) (hF : Width k F) :
    Width k (rename f F) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa using hF d hd

@[simp] theorem length_rename {v w : ℕ} (f : Fin v → Fin w) (F : Formula v) :
    (rename f F).length = F.length := by simp [rename]

namespace Circuit

def compile {n : ℕ} : {g : ℕ} → Circuit n g → Formula (n + g)
  | _, nil => []
  | _, snoc C gate => rename Fin.castSucc C.compile ++
      (gate.map Fin.castSucc).clauses (Fin.last _)

theorem compile_width {n g : ℕ} (C : Circuit n g) : Width 3 C.compile := by
  induction C with
  | nil => simp [compile, Width]
  | snoc C gate ih =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact width_rename Fin.castSucc C.compile ih c hc
    · exact Gate.clauses_width _ _ c hc

theorem compile_length {n g : ℕ} (C : Circuit n g) : C.compile.length ≤ 4 * g := by
  induction C with
  | nil => simp [compile]
  | snoc C gate ih =>
    simp only [compile, List.length_append, length_rename]
    have h := Gate.clauses_length (gate.map Fin.castSucc) (Fin.last _)
    omega

theorem compile_snoc_eval {n g : ℕ} (C : Circuit n g) (gate : Gate (n + g))
    (v : BitModels (n + (g + 1))) :
    PrefixCNF.eval (C.snoc gate).compile v = true ↔
      PrefixCNF.eval C.compile (Fin.init v) = true ∧
        v (Fin.last (n + g)) = gate.eval (Fin.init v) := by
  simp only [compile, PrefixCNF.eval, List.all_append, Bool.and_eq_true]
  change PrefixCNF.eval (rename Fin.castSucc C.compile) v = true ∧
      PrefixCNF.eval ((gate.map Fin.castSucc).clauses (Fin.last _)) v = true ↔ _
  rw [eval_rename, Gate.clauses_correct, Gate.eval_map]
  rfl

theorem run_satisfies {n g : ℕ} (C : Circuit n g) (a : BitModels n) :
    PrefixCNF.eval C.compile (C.run a) = true := by
  induction C with
  | nil => rfl
  | @snoc g C gate ih =>
    rw [compile_snoc_eval]
    constructor
    · simpa only [run, Fin.init_snoc] using ih
    · change Fin.snoc (n := n + g) (α := fun _ => Bool) (C.run a) (gate.eval (C.run a)) (Fin.last (n + g)) =
        gate.eval (Fin.init (Fin.snoc (n := n + g) (α := fun _ => Bool) (C.run a) (gate.eval (C.run a))))
      rw [Fin.init_snoc]
      exact Fin.snoc_last _ _

/-- All satisfying wire assignments are the unique evaluation of their primary inputs. -/
theorem satisfying_unique {n g : ℕ} (C : Circuit n g) (a : BitModels n)
    (v : BitModels (n + g)) (hv : PrefixCNF.eval C.compile v = true) (ha : inputs v = a) :
    v = C.run a := by
  induction C with
  | nil => exact ha
  | @snoc g C gate ih =>
    obtain ⟨hold, hout⟩ := (compile_snoc_eval C gate v).mp hv
    have hinput : inputs (Fin.init v) = a := ha
    have he := ih (Fin.init v) hold hinput
    rw [he] at hout
    rw [← Fin.snoc_init_self v, he]
    change Fin.snoc (n := n + g) (α := fun _ => Bool) (C.run a) (v (Fin.last _)) = Fin.snoc (n := n + g) (α := fun _ => Bool) (C.run a) (gate.eval (C.run a))
    congr 1

theorem compile_iff_run {n g : ℕ} (C : Circuit n g) (v : BitModels (n + g)) :
    PrefixCNF.eval C.compile v = true ↔ v = C.run (inputs v) := by
  constructor
  · intro h; exact satisfying_unique C (inputs v) v h rfl
  · intro h; rw [h]; exact run_satisfies C _

end Circuit
end SharedCircuit
end QecReliability
