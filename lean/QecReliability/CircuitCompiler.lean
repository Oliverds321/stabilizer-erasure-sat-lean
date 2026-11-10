import QecReliability.SharedCircuit

/-! Global Tseitin semantics, unique auxiliary extension, and linear output size.
Primary inputs stay first; existential witness inputs are not counted as auxiliaries. -/

namespace QecReliability.SharedCircuit
open PrefixCNF

def literalCount {v : ℕ} (F : Formula v) : ℕ := (F.map List.length).sum

@[simp] theorem literalCount_append {v : ℕ} (F G : Formula v) :
    literalCount (F ++ G) = literalCount F + literalCount G := by
  simp [literalCount]

@[simp] theorem literalCount_rename {v w : ℕ} (f : Fin v → Fin w) (F : Formula v) :
    literalCount (rename f F) = literalCount F := by
  simp [literalCount, rename, List.map_map, Function.comp_def]

theorem gate_literalCount {v : ℕ} (g : Gate v) (out : Fin v) :
    literalCount (g.clauses out) ≤ 12 := by cases g <;> simp [literalCount, Gate.clauses]

namespace Circuit

theorem compile_literalCount {n g : ℕ} (C : Circuit n g) : literalCount C.compile ≤ 12 * g := by
  induction C with
  | nil => simp [compile, literalCount]
  | snoc C gate ih =>
    simp only [compile, literalCount_append, literalCount_rename]
    have h := gate_literalCount (gate.map Fin.castSucc) (Fin.last _)
    omega

def auxiliaries {n g : ℕ} (C : Circuit n g) (a : BitModels n) : BitModels g :=
  fun i => C.run a (Fin.natAdd n i)

theorem append_auxiliaries {n g : ℕ} (C : Circuit n g) (a : BitModels n) :
    Fin.append a (C.auxiliaries a) = C.run a := by
  have h := Fin.append_castAdd_natAdd (f := C.run a)
  change Fin.append (inputs (C.run a)) (C.auxiliaries a) = C.run a at h
  rwa [run_inputs] at h

/-- Exactly one gate-output assignment extends each fixed primary-input assignment. -/
theorem unique_auxiliaries {n g : ℕ} (C : Circuit n g) (a : BitModels n) :
    ∃! u : BitModels g, PrefixCNF.eval C.compile (Fin.append a u) = true := by
  refine ⟨C.auxiliaries a, ?_, ?_⟩
  · change PrefixCNF.eval C.compile (Fin.append a (C.auxiliaries a)) = true
    rw [append_auxiliaries]; exact run_satisfies C a
  · intro u hu
    have he := satisfying_unique C a (Fin.append a u) hu (by funext i; exact Fin.append_left a u i)
    funext i
    simpa [auxiliaries] using congrFun he (Fin.natAdd n i)

def asserted {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) : Formula (n + g) :=
  C.compile ++ [[(out, true)]]

def constrained {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (b : Bool) : Formula (n + g) :=
  C.compile ++ [[(out, b)]]

theorem constrained_eval {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (b : Bool)
    (v : BitModels (n + g)) :
    PrefixCNF.eval (C.constrained out b) v = true ↔ PrefixCNF.eval C.compile v = true ∧ v out = b := by
  simp [constrained, PrefixCNF.eval, evalClause]

theorem constrained_exists {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (b : Bool) (a : BitModels n) :
    (∃ u : BitModels g, PrefixCNF.eval (C.constrained out b) (Fin.append a u) = true) ↔
      C.run a out = b := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hcompile, hout⟩ := (constrained_eval C out b _).mp hu
    have he := satisfying_unique C a (Fin.append a u) hcompile (by funext i; exact Fin.append_left a u i)
    rwa [he] at hout
  · intro h
    refine ⟨C.auxiliaries a, ?_⟩
    rw [append_auxiliaries, constrained_eval]
    exact ⟨run_satisfies C a, h⟩

theorem constrained_width {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (b : Bool) :
    Width 3 (C.constrained out b) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact compile_width C c hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    simp

theorem constrained_length {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (b : Bool) :
    (C.constrained out b).length ≤ 4 * g + 1 := by
  simpa [constrained] using Nat.add_le_add_right (compile_length C) 1

theorem asserted_eval {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (v : BitModels (n + g)) :
    PrefixCNF.eval (C.asserted out) v = true ↔ PrefixCNF.eval C.compile v = true ∧ v out = true := by
  simp [asserted, PrefixCNF.eval, evalClause]

theorem asserted_width {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) : Width 3 (C.asserted out) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact compile_width C c hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    simp

theorem asserted_length {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) :
    (C.asserted out).length ≤ 4 * g + 1 := by
  simpa [asserted] using Nat.add_le_add_right (compile_length C) 1

theorem asserted_literalCount {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) :
    literalCount (C.asserted out) ≤ 12 * g + 1 := by
  simpa [asserted, literalCount_append, literalCount] using Nat.add_le_add_right (compile_literalCount C) 1

/-- Full-equivalence compilation, including the selected accepting output. -/
theorem asserted_exists {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (a : BitModels n) :
    (∃ u : BitModels g, PrefixCNF.eval (C.asserted out) (Fin.append a u) = true) ↔
      C.run a out = true := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hcompile, hout⟩ := (asserted_eval C out _).mp hu
    have he := satisfying_unique C a (Fin.append a u) hcompile (by funext i; exact Fin.append_left a u i)
    rwa [he] at hout
  · intro h
    refine ⟨C.auxiliaries a, ?_⟩
    rw [append_auxiliaries, asserted_eval]
    exact ⟨run_satisfies C a, h⟩

theorem asserted_exists_unique {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (a : BitModels n) :
    (∃! u : BitModels g, PrefixCNF.eval (C.asserted out) (Fin.append a u) = true) ↔
      C.run a out = true := by
  constructor
  · intro h
    exact (asserted_exists C out a).mp h.exists
  · intro h
    obtain ⟨u, hu⟩ := (asserted_exists C out a).mpr h
    refine ⟨u, hu, ?_⟩
    intro v hv
    exact (unique_auxiliaries C a).unique ((asserted_eval C out _).mp hv).1
      ((asserted_eval C out _).mp hu).1

/-- Projection bits and genuine witnesses remain primary inputs; only gate outputs are uniquely extended. -/
theorem projected_nested {q w g : ℕ} (C : Circuit (q + w) g)
    (out : Fin ((q + w) + g)) (a : BitModels q) :
    (∃ b : BitModels w, ∃ u : BitModels g,
      PrefixCNF.eval (C.asserted out) (Fin.append (Fin.append a b) u) = true) ↔
      ∃ b : BitModels w, C.run (Fin.append a b) out = true := by
  exact exists_congr (fun b => asserted_exists C out (Fin.append a b))

/-- Same variables in the order projection / witnesses / gate outputs, with only an index cast. -/
def projectedFormula {q w g : ℕ} (C : Circuit (q + w) g) (out : Fin ((q + w) + g)) :
    Formula (q + (w + g)) := rename (Fin.cast (Nat.add_assoc q w g)) (C.asserted out)

theorem projectedFormula_width {q w g : ℕ} (C : Circuit (q + w) g) (out : Fin ((q + w) + g)) :
    Width 3 (C.projectedFormula out) := width_rename _ _ (asserted_width C out)

theorem projectedFormula_length {q w g : ℕ} (C : Circuit (q + w) g) (out : Fin ((q + w) + g)) :
    (C.projectedFormula out).length ≤ 4 * g + 1 := by
  simpa only [projectedFormula, length_rename] using asserted_length C out

theorem projectedFormula_correct {q w g : ℕ} (C : Circuit (q + w) g)
    (out : Fin ((q + w) + g)) (a : BitModels q) :
    PrefixCNF.Projected (C.projectedFormula out) a ↔
      ∃ b : BitModels w, C.run (Fin.append a b) out = true := by
  rw [← projected_nested C out a]
  constructor
  · rintro ⟨t, ht⟩
    let b : BitModels w := fun i => t (Fin.castAdd g i)
    let u : BitModels g := fun i => t (Fin.natAdd w i)
    have he : Fin.append b u = t := Fin.append_castAdd_natAdd
    rw [← he, projectedFormula, eval_rename] at ht
    have hassoc := Fin.append_assoc a b u
    change Fin.append (Fin.append a b) u =
      (fun i => Fin.append a (Fin.append b u) (Fin.cast (Nat.add_assoc q w g) i)) at hassoc
    rw [← hassoc] at ht
    exact ⟨b, u, ht⟩
  · rintro ⟨b, u, h⟩
    refine ⟨Fin.append b u, ?_⟩
    rw [projectedFormula, eval_rename]
    have hassoc := Fin.append_assoc a b u
    change Fin.append (Fin.append a b) u =
      (fun i => Fin.append a (Fin.append b u) (Fin.cast (Nat.add_assoc q w g) i)) at hassoc
    rwa [← hassoc]

/-- A concrete width-three SAT callback yields exact prefix decision for the supplied shared DAG. -/
def compiledDecision {q w g : ℕ} (C : Circuit (q + w) g) (out : Fin ((q + w) + g))
    (solver : ExactSAT (q + (w + g)) 3) :
    PrefixEnumeration.ExactDecision (fun a : BitModels q =>
      ∃ b : BitModels w, C.run (Fin.append a b) out = true) where
  answer pre := solver.solve (PrefixCNF.restrict (C.projectedFormula out) pre)
  correct pre := by
    rw [solver.correct _ (PrefixCNF.restrict_width (projectedFormula_width C out) (by omega) pre),
      PrefixCNF.restrict_sat]
    simp only [PrefixEnumeration.PrefixSat, projectedFormula_correct]

/-- Complete supplied-DAG compiler contract: shared edges, linear CNF size, unique
gate auxiliaries for each accepted full input, and existential projection semantics. -/
theorem projected_compiler_contract {q w g : ℕ} (C : Circuit (q + w) g)
    (out : Fin ((q + w) + g)) :
    Width 3 (C.projectedFormula out) ∧
      (C.projectedFormula out).length ≤ 4 * g + 1 ∧
      literalCount (C.projectedFormula out) ≤ 12 * g + 1 ∧
      C.edges ≤ 2 * g ∧
      (∀ a : BitModels (q + w),
        (∃! u : BitModels g, PrefixCNF.eval (C.asserted out) (Fin.append a u) = true) ↔
          C.run a out = true) ∧
      ∀ a : BitModels q, PrefixCNF.Projected (C.projectedFormula out) a ↔
        ∃ b : BitModels w, C.run (Fin.append a b) out = true := by
  refine ⟨projectedFormula_width C out, projectedFormula_length C out, ?_, edges_le C,
    asserted_exists_unique C out, projectedFormula_correct C out⟩
  simpa only [projectedFormula, literalCount_rename] using asserted_literalCount C out

end Circuit
end QecReliability.SharedCircuit
