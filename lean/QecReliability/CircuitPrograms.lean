import QecReliability.CircuitComposition

/-! Constructive shared-DAG programs with explicit input/output wiring. -/
namespace QecReliability.SharedCircuit

structure Program (n k : ℕ) where
  gates : ℕ
  circuit : Circuit n gates
  output : Fin k → Fin (n + gates)

namespace Program

def eval {n k : ℕ} (P : Program n k) (a : BitModels n) : BitModels k :=
  fun i => P.circuit.run a (P.output i)

def pure {n k : ℕ} (f : Fin k → Fin n) : Program n k := ⟨0, .nil, f⟩

@[simp] theorem pure_eval {n k : ℕ} (f : Fin k → Fin n) (a : BitModels n) :
    (pure f).eval a = a ∘ f := rfl

def rewire {n m k : ℕ} (P : Program n k) (f : Fin n → Fin m) : Program m k :=
  ⟨P.gates, P.circuit.rewire f, fun i => Circuit.liftWire f P.gates (P.output i)⟩

@[simp] theorem rewire_eval {n m k : ℕ} (P : Program n k) (f : Fin n → Fin m) (a : BitModels m) :
    (P.rewire f).eval a = P.eval (a ∘ f) := by
  funext i
  exact Circuit.rewire_run _ _ _ _

def compose {n m k : ℕ} (P : Program n m) (Q : Program m k) : Program n k where
  gates := P.gates + Q.gates
  circuit := P.circuit.extend (Q.circuit.rewire P.output)
  output i := Fin.cast (Nat.add_assoc n P.gates Q.gates)
    (Circuit.liftWire P.output Q.gates (Q.output i))

@[simp] theorem compose_eval {n m k : ℕ} (P : Program n m) (Q : Program m k) (a : BitModels n) :
    (P.compose Q).eval a = Q.eval (P.eval a) := by
  funext i
  exact (Circuit.extend_run _ _ _ _).trans (Circuit.rewire_run _ _ _ _)

def parallel {n k l : ℕ} (P : Program n k) (Q : Program n l) : Program n (k + l) where
  gates := P.gates + Q.gates
  circuit := P.circuit.extend (Q.circuit.rewire (Fin.castAdd P.gates))
  output := Fin.addCases
    (fun i => Fin.cast (Nat.add_assoc n P.gates Q.gates)
      (Fin.castAdd Q.gates (P.output i)))
    (fun i => Fin.cast (Nat.add_assoc n P.gates Q.gates)
      (Circuit.liftWire (Fin.castAdd P.gates) Q.gates (Q.output i)))

@[simp] theorem parallel_eval {n k l : ℕ} (P : Program n k) (Q : Program n l) (a : BitModels n) :
    (P.parallel Q).eval a = Fin.append (P.eval a) (Q.eval a) := by
  have hp : P.circuit.run a ∘ Fin.castAdd P.gates = a := by
    funext i; exact Circuit.run_primary _ _ _
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [eval, parallel, Fin.addCases_left, Fin.append_left]
    change (P.circuit.extend (Q.circuit.rewire (Fin.castAdd P.gates))).run a
      (Fin.cast _ (Fin.castAdd Q.gates (P.output j))) = P.eval a j
    rw [Circuit.extend_run, Circuit.run_primary]
    rfl
  · simp only [eval, parallel, Fin.addCases_right, Fin.append_right]
    change (P.circuit.extend (Q.circuit.rewire (Fin.castAdd P.gates))).run a
      (Fin.cast _ (Circuit.liftWire (Fin.castAdd P.gates) Q.gates (Q.output j))) = Q.eval a j
    rw [Circuit.extend_run, Circuit.rewire_run]
    rw [hp]
    rfl

def constant (n : ℕ) (b : Bool) : Program n 1 :=
  ⟨1, Circuit.nil.snoc (.constGate b), fun _ => Fin.last n⟩

@[simp] theorem constant_eval (n : ℕ) (b : Bool) (a : BitModels n) :
    (constant n b).eval a = fun _ => b := by
  funext i
  exact Circuit.snoc_output Circuit.nil (.constGate b) a

def follow {n k l : ℕ} (P : Program n k) (Q : Program (n + P.gates) l) : Program n l where
  gates := P.gates + Q.gates
  circuit := P.circuit.extend Q.circuit
  output i := Fin.cast (Nat.add_assoc n P.gates Q.gates) (Q.output i)

@[simp] theorem follow_eval {n k l : ℕ} (P : Program n k) (Q : Program (n + P.gates) l)
    (a : BitModels n) : (P.follow Q).eval a = Q.eval (P.circuit.run a) := by
  funext i
  exact Circuit.extend_run _ _ _ _

def outputCast {n k l : ℕ} (P : Program n k) (h : k = l) : Program n l :=
  ⟨P.gates, P.circuit, fun i => P.output (Fin.cast h.symm i)⟩

end Program
end QecReliability.SharedCircuit
