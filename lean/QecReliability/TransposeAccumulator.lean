import QecReliability.CodeDistance
import QecReliability.CodePadding

/-! Shared-wire accumulators used by the constructive XOR-DAG transpose. Every
addition is a concrete XOR gate; repeated targets are accumulated, never dropped. -/
namespace QecReliability.SharedCircuit
open CodeHash
open scoped BigOperators

def bitsVector {v : ℕ} (a : BitModels v) : Word v := fun i => boolBit (a i)
def pair {v : ℕ} (a b : Word v) : F := ∑ i, a i * b i

theorem pair_add_left {v : ℕ} (a b c : Word v) : pair (a + b) c = pair a c + pair b c := by
  simp [pair, add_mul, Finset.sum_add_distrib]

theorem pair_single_left {v : ℕ} (i : Fin v) (a : F) (b : Word v) :
    pair (Pi.single i a) b = a * b i := by simp [pair, Pi.single_apply]

theorem pair_single_right {v : ℕ} (a : Word v) (i : Fin v) :
    pair a (Pi.single i 1) = a i := by simp [pair, Pi.single_apply]

def Program.select {n v k : ℕ} (P : Program n v) (f : Fin k → Fin v) : Program n k :=
  ⟨P.gates, P.circuit, P.output ∘ f⟩

@[simp] theorem Program.select_eval {n v k : ℕ} (P : Program n v) (f : Fin k → Fin v) (a : BitModels n) :
    (P.select f).eval a = P.eval a ∘ f := rfl

def Program.addWire {n v : ℕ} (P : Program n v) (target : Fin v)
    (source : Fin (n + P.gates)) : Program n v where
  gates := P.gates + 1
  circuit := P.circuit.snoc (.xorGate (P.output target) source)
  output i := if i = target then Fin.last (n + P.gates) else (P.output i).castSucc

theorem Program.addWire_value {n v : ℕ} (P : Program n v) (target : Fin v)
    (source : Fin (n + P.gates)) (a : BitModels n) :
    bitsVector ((P.addWire target source).eval a) = bitsVector (P.eval a) +
      Pi.single target (boolBit (P.circuit.run a source)) := by
  funext i
  by_cases hi : i = target
  · subst i
    change boolBit ((P.circuit.snoc _).run a (if target = target then _ else _)) = _
    simp only [↓reduceIte, Pi.add_apply, Pi.single_eq_same]
    have h := Circuit.snoc_output P.circuit (.xorGate (P.output target) source) a
    exact (congrArg boolBit h).trans (boolBit_xor _ _)
  · change boolBit ((P.circuit.snoc _).run a (if i = target then _ else _)) = _
    simp only [hi, ↓reduceIte, Pi.add_apply, Pi.single_eq_of_ne hi, add_zero]
    exact congrArg boolBit (Circuit.snoc_old P.circuit _ a (P.output i))

def Program.addInput {n v : ℕ} (P : Program n v) (target : Fin v) (source : Fin n) : Program n v :=
  P.addWire target (Fin.castAdd P.gates source)

theorem Program.addInput_value {n v : ℕ} (P : Program n v) (target : Fin v) (source : Fin n)
    (a : BitModels n) : bitsVector ((P.addInput target source).eval a) =
      bitsVector (P.eval a) + Pi.single target (boolBit (a source)) := by
  rw [Program.addInput, Program.addWire_value, Circuit.run_primary]

def Program.addOutput {n v : ℕ} (P : Program n v) (target source : Fin v) : Program n v :=
  P.addWire target (P.output source)

theorem Program.addOutput_value {n v : ℕ} (P : Program n v) (target source : Fin v)
    (a : BitModels n) : bitsVector ((P.addOutput target source).eval a) =
      bitsVector (P.eval a) + Pi.single target (bitsVector (P.eval a) source) :=
  P.addWire_value target (P.output source) a

def zeroAccumulator (n v : ℕ) : Program n v :=
  ⟨1, Circuit.nil.snoc (.constGate false), fun _ => Fin.last n⟩

theorem zeroAccumulator_value (n v : ℕ) (a : BitModels n) :
    bitsVector ((zeroAccumulator n v).eval a) = 0 := by
  funext i
  exact (congrArg boolBit (Circuit.snoc_output Circuit.nil (.constGate false) a)).trans rfl

def scatterList {n v : ℕ} (P : Program n v) : List (Fin v × Fin n) → Program n v
  | [] => P
  | (target, source) :: xs => (scatterList P xs).addInput target source

theorem scatterList_gates {n v : ℕ} (P : Program n v) (xs : List (Fin v × Fin n)) :
    (scatterList P xs).gates = P.gates + xs.length := by
  induction xs with
  | nil => simp [scatterList]
  | cons x xs ih => simp [scatterList, Program.addInput, Program.addWire, ih, Nat.add_assoc]

theorem scatterList_edges {n v : ℕ} (P : Program n v) (xs : List (Fin v × Fin n)) :
    (scatterList P xs).circuit.edges = P.circuit.edges + 2 * xs.length := by
  induction xs with
  | nil => simp [scatterList]
  | cons x xs ih =>
    simp [scatterList, Program.addInput, Program.addWire, Circuit.edges, Gate.arity, ih]
    omega

theorem scatterList_pair {n v : ℕ} (P : Program n v) (xs : List (Fin v × Fin n))
    (a : BitModels n) (b : Word v) :
    pair (bitsVector ((scatterList P xs).eval a)) b = pair (bitsVector (P.eval a)) b +
      (xs.map (fun x => boolBit (a x.2) * b x.1)).sum := by
  induction xs with
  | nil => simp [scatterList]
  | cons x xs ih =>
    rw [scatterList, Program.addInput_value, pair_add_left, pair_single_left, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

def scatter {n v : ℕ} (out : Fin n → Fin v) : Program n v :=
  scatterList (zeroAccumulator n v) (List.ofFn (fun i => (out i, i)))

theorem scatter_gates {n v : ℕ} (out : Fin n → Fin v) : (scatter out).gates = 1 + n := by
  simp [scatter, scatterList_gates, zeroAccumulator]

theorem scatter_edges {n v : ℕ} (out : Fin n → Fin v) : (scatter out).circuit.edges = 2 * n := by
  simp [scatter, scatterList_edges, zeroAccumulator, Circuit.edges, Gate.arity]

theorem scatter_pair {n v : ℕ} (out : Fin n → Fin v) (a : BitModels n) (b : Word v) :
    pair (bitsVector ((scatter out).eval a)) b = ∑ i, boolBit (a i) * b (out i) := by
  rw [scatter, scatterList_pair, zeroAccumulator_value]
  simp [pair, List.map_ofFn, List.sum_ofFn]

end QecReliability.SharedCircuit
