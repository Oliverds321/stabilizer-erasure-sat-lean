import QecReliability.XorCircuitInput
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!


Written against the exact Program/Circuit/XorCircuit definitions.



The supplied amplifier programs below are genuinely lower-level parameters:
their construction and distance theorem are NOT asserted by this file.
-/

namespace QecReliability.SharedCircuit

inductive RawGate where
  | zero
  | xor (left right : Nat)
  deriving DecidableEq, Repr

namespace RawGate

def Valid (available : Nat) : RawGate → Prop
  | .zero => True
  | .xor x y => x < available ∧ y < available

def map (f : Nat → Nat) : RawGate → RawGate
  | .zero => .zero
  | .xor x y => .xor (f x) (f y)

def eval (values : Nat → Bool) : RawGate → Bool
  | .zero => false
  | .xor x y => Bool.xor (values x) (values y)

end RawGate

/-- The gate at position `j` may read only identifiers below `n+j`.
The snoc formulation mirrors the supplied circuit datatype; it is not a
semantic or distance premise. -/
inductive Topological (n : Nat) : List RawGate → Prop where
  | nil : Topological n []
  | snoc {xs : List RawGate} {gate : RawGate} :
      Topological n xs → gate.Valid (n + xs.length) →
      Topological n (xs ++ [gate])

/-- Append lifting: local inputs use the supplied references; local gate `j`
becomes global wire `start+j`. `start` counts *all* wires already emitted. -/
def liftRef (inputCount start : Nat) (inputRefs : Fin inputCount → Nat)
    (v : Nat) : Nat :=
  if hv : v < inputCount then inputRefs ⟨v, hv⟩
  else start + (v - inputCount)

theorem liftRef_input {n start : Nat} (refs : Fin n → Nat) (i : Fin n) :
    liftRef n start refs i.val = refs i := by
  simp [liftRef, i.isLt]

theorem liftRef_gate {n start : Nat} (refs : Fin n → Nat) (j : Nat) :
    liftRef n start refs (n + j) = start + j := by
  have hn : ¬n + j < n := by omega
  simp [liftRef, hn]

theorem liftRef_lt {n start g : Nat} (refs : Fin n → Nat)
    (hrefs : ∀ i, refs i < start) {v : Nat} (hv : v < n + g) :
    liftRef n start refs v < start + g := by
  unfold liftRef
  split_ifs with h
  · have hi := hrefs ⟨v, h⟩
    omega
  · omega

theorem liftRef_valid {n start g : Nat} (refs : Fin n → Nat)
    (hrefs : ∀ i, refs i < start) {gate : RawGate}
    (hg : gate.Valid (n + g)) :
    (gate.map (liftRef n start refs)).Valid (start + g) := by
  cases gate with
  | zero => trivial
  | xor x y =>
    exact ⟨liftRef_lt refs hrefs hg.1, liftRef_lt refs hrefs hg.2⟩

theorem Topological.lift {n start : Nat} {xs : List RawGate}
    (hx : Topological n xs) (refs : Fin n → Nat)
    (hrefs : ∀ i, refs i < start) :
    Topological start (xs.map (RawGate.map (liftRef n start refs))) := by
  induction hx with
  | nil => exact .nil
  | snoc hx hg ih =>
    simp only [List.map_append, List.map_cons, List.map_nil]
    apply Topological.snoc ih
    simpa only [List.length_map] using liftRef_valid refs hrefs hg

theorem Topological.append {n : Nat} {xs ys : List RawGate}
    (hx : Topological n xs) (hy : Topological (n + xs.length) ys) :
    Topological n (xs ++ ys) := by
  induction hy with
  | nil => simpa only [List.append_nil] using hx
  | snoc hy hg ih =>
    rw [← List.append_assoc]
    apply Topological.snoc ih
    simpa only [List.length_append, Nat.add_assoc] using hg

theorem liftWire_val {n m g : Nat} (f : Fin n → Fin m) (i : Fin (n + g)) :
    (Circuit.liftWire f g i).val =
      liftRef n m (fun j => (f j).val) i.val := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Circuit.liftWire, Fin.addCases_left]
    exact (liftRef_input (fun k => (f k).val) j).symm
  · simp only [Circuit.liftWire, Fin.addCases_right]
    exact (liftRef_gate (fun k => (f k).val) j.val).symm

namespace XorCircuit

def rewire {n m : Nat} (f : Fin n → Fin m) :
    {g : Nat} → XorCircuit n g → XorCircuit m g
  | _, .nil => .nil
  | _, .zero C => .zero (rewire f C)
  | _, .xor C x y =>
      .xor (rewire f C) (Circuit.liftWire f _ x) (Circuit.liftWire f _ y)

@[simp] theorem rewire_toCircuit {n m g : Nat} (f : Fin n → Fin m)
    (C : XorCircuit n g) :
    (C.rewire f).toCircuit = C.toCircuit.rewire f := by
  induction C with
  | nil => rfl
  | zero C ih => simp [rewire, toCircuit, Circuit.rewire, Gate.map, ih]
  | xor C x y ih => simp [rewire, toCircuit, Circuit.rewire, Gate.map, ih]

def extend {n g : Nat} (C : XorCircuit n g) :
    {h : Nat} → XorCircuit (n + g) h → XorCircuit n (g + h)
  | _, .nil => C
  | _, .zero D => .zero (extend C D)
  | _, .xor D x y => .xor (extend C D)
      (Fin.cast (Nat.add_assoc n g _) x)
      (Fin.cast (Nat.add_assoc n g _) y)

@[simp] theorem extend_toCircuit {n g h : Nat} (C : XorCircuit n g)
    (D : XorCircuit (n + g) h) :
    (C.extend D).toCircuit = C.toCircuit.extend D.toCircuit := by
  induction D with
  | nil => rfl
  | zero D ih => simp [extend, toCircuit, Circuit.extend, Gate.map, ih]
  | xor D x y ih => simp [extend, toCircuit, Circuit.extend, Gate.map, ih]

/-- A literal finite zero/xor gate list, in topological emission order. -/
def erase {n : Nat} : {g : Nat} → XorCircuit n g → List RawGate
  | _, .nil => []
  | _, .zero C => C.erase ++ [.zero]
  | _, .xor C x y => C.erase ++ [.xor x.val y.val]

@[simp] theorem erase_length {n g : Nat} (C : XorCircuit n g) :
    C.erase.length = g := by
  induction C <;> simp_all [erase]

theorem erase_topological {n g : Nat} (C : XorCircuit n g) :
    Topological n C.erase := by
  induction C with
  | nil => exact .nil
  | zero C ih =>
    exact .snoc ih trivial
  | xor C x y ih =>
    apply Topological.snoc ih
    simpa only [RawGate.Valid, erase_length] using And.intro x.isLt y.isLt

@[simp] theorem erase_extend {n g h : Nat} (C : XorCircuit n g)
    (D : XorCircuit (n + g) h) :
    (C.extend D).erase = C.erase ++ D.erase := by
  induction D with
  | nil => simp [extend, erase]
  | zero D ih => simp [extend, erase, ih, List.append_assoc]
  | xor D x y ih => simp [extend, erase, ih, List.append_assoc]

@[simp] theorem erase_rewire {n m g : Nat} (f : Fin n → Fin m)
    (C : XorCircuit n g) :
    (C.rewire f).erase =
      C.erase.map (RawGate.map (liftRef n m (fun i => (f i).val))) := by
  induction C with
  | nil => rfl
  | zero C ih => simp [rewire, erase, ih, RawGate.map]
  | xor C x y ih => simp [rewire, erase, ih, RawGate.map, liftWire_val]

@[simp] theorem toCircuit_xorOnly {n g : Nat} (C : XorCircuit n g) :
    C.toCircuit.xorOnly = true := by
  induction C <;> simp_all [toCircuit, Circuit.xorOnly]

end XorCircuit

/-- An unbounded-address mathematical executor for the finite raw gate list.
This is a semantic definition, NOT a unit-cost or bit-cost time model. -/
def runRaw (next : Nat) (values : Nat → Bool) : List RawGate → Nat → Bool
  | [] => values
  | gate :: gates =>
      runRaw (next + 1) (Function.update values next (gate.eval values)) gates

theorem runRaw_append (next : Nat) (values : Nat → Bool)
    (xs ys : List RawGate) :
    runRaw next values (xs ++ ys) =
      runRaw (next + xs.length) (runRaw next values xs) ys := by
  induction xs generalizing next values with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.cons_append, runRaw, List.length_cons, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      ih (next + 1) (Function.update values next (x.eval values))

/-- Strong refinement: arbitrary initial memory is permitted outside primary
inputs. Every circuit wire agrees with the exact supplied `Circuit.run`. -/
theorem runRaw_refines {n g : Nat} (C : XorCircuit n g)
    (a : BitModels n) (values : Nat → Bool)
    (hvalues : ∀ i : Fin n, values i.val = a i) :
    ∀ i : Fin (n + g), runRaw n values C.erase i.val = C.toCircuit.run a i := by
  induction C with
  | nil => exact hvalues
  | @zero g C ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [XorCircuit.erase, runRaw_append, XorCircuit.erase_length]
      change Function.update (runRaw n values C.erase) (n + g) false (n + g) = _
      rw [Function.update_self]
      exact (Circuit.snoc_output C.toCircuit (.constGate false) a).symm
    · have hj : j.val ≠ n + g := Nat.ne_of_lt j.isLt
      rw [XorCircuit.erase, runRaw_append, XorCircuit.erase_length]
      change Function.update (runRaw n values C.erase) (n + g) false j.val = _
      rw [Function.update_of_ne hj]
      exact (ih j).trans (Circuit.snoc_old C.toCircuit (.constGate false) a j).symm
  | @xor g C x y ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [XorCircuit.erase, runRaw_append, XorCircuit.erase_length]
      change Function.update (runRaw n values C.erase) (n + g)
        (Bool.xor (runRaw n values C.erase x.val) (runRaw n values C.erase y.val))
        (n + g) = _
      rw [Function.update_self, ih x, ih y]
      exact (Circuit.snoc_output C.toCircuit (.xorGate x y) a).symm
    · have hj : j.val ≠ n + g := Nat.ne_of_lt j.isLt
      rw [XorCircuit.erase, runRaw_append, XorCircuit.erase_length]
      change Function.update (runRaw n values C.erase) (n + g)
        (Bool.xor (runRaw n values C.erase x.val) (runRaw n values C.erase y.val))
        j.val = _
      rw [Function.update_of_ne hj]
      exact (ih j).trans (Circuit.snoc_old C.toCircuit (.xorGate x y) a j).symm

namespace XorProgram

def rewire {n m k : Nat} (P : XorProgram n k) (f : Fin n → Fin m) : XorProgram m k :=
  ⟨P.gates, P.circuit.rewire f,
    fun i => Circuit.liftWire f P.gates (P.output i)⟩

@[simp] theorem rewire_toProgram {n m k : Nat} (P : XorProgram n k)
    (f : Fin n → Fin m) :
    (P.rewire f).toProgram = P.toProgram.rewire f := by
  cases P
  simp only [rewire, toProgram, Program.rewire, XorCircuit.rewire_toCircuit]

def follow {n k l : Nat} (P : XorProgram n k)
    (Q : XorProgram (n + P.gates) l) : XorProgram n l :=
  ⟨P.gates + Q.gates, P.circuit.extend Q.circuit,
    fun i => Fin.cast (Nat.add_assoc n P.gates Q.gates) (Q.output i)⟩

@[simp] theorem follow_toProgram {n k l : Nat} (P : XorProgram n k)
    (Q : XorProgram (n + P.gates) l) :
    (P.follow Q).toProgram = P.toProgram.follow Q.toProgram := by
  cases P
  cases Q
  simp only [follow, toProgram, Program.follow, XorCircuit.extend_toCircuit]

/-- Append the new gates once while retaining the old outputs as references. -/
def keepFollow {n k l : Nat} (P : XorProgram n k)
    (Q : XorProgram (n + P.gates) l) : XorProgram n (k + l) where
  gates := P.gates + Q.gates
  circuit := P.circuit.extend Q.circuit
  output := Fin.addCases
    (fun i => Fin.cast (Nat.add_assoc n P.gates Q.gates)
      (Fin.castAdd Q.gates (P.output i)))
    (fun i => Fin.cast (Nat.add_assoc n P.gates Q.gates) (Q.output i))

theorem keepFollow_eval {n k l : Nat} (P : XorProgram n k)
    (Q : XorProgram (n + P.gates) l) (a : BitModels n) :
    (P.keepFollow Q).toProgram.eval a =
      Fin.append (P.toProgram.eval a) (Q.toProgram.eval (P.circuit.toCircuit.run a)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [keepFollow, toProgram, Program.eval, Fin.addCases_left,
      Fin.append_left, XorCircuit.extend_toCircuit]
    rw [Circuit.extend_run, Circuit.run_primary]
  · simp only [keepFollow, toProgram, Program.eval, Fin.addCases_right,
      Fin.append_right, XorCircuit.extend_toCircuit]
    exact Circuit.extend_run _ _ _ _

def keepInputs {n k : Nat} (P : XorProgram n k) : XorProgram n (n + k) :=
  ⟨P.gates, P.circuit, Fin.addCases (Fin.castAdd P.gates) P.output⟩

theorem keepInputs_eval {n k : Nat} (P : XorProgram n k) (a : BitModels n) :
    P.keepInputs.toProgram.eval a = Fin.append a (P.toProgram.eval a) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [keepInputs, toProgram, Program.eval, Fin.addCases_left,
      Fin.append_left] using (Circuit.run_primary P.circuit.toCircuit a j)
  · simp only [keepInputs, toProgram, Program.eval, Fin.addCases_right,
      Fin.append_right]

def outputCast {n k l : Nat} (P : XorProgram n k) (h : k = l) : XorProgram n l :=
  ⟨P.gates, P.circuit, fun i => P.output (Fin.cast h.symm i)⟩

def inputCast {n m k : Nat} (P : XorProgram n k) (h : n = m) : XorProgram m k :=
  h ▸ P

@[simp] theorem inputCast_gates {n m k : Nat} (P : XorProgram n k) (h : n = m) :
    (P.inputCast h).gates = P.gates := by
  cases h
  rfl

@[simp] theorem inputCast_erase {n m k : Nat} (P : XorProgram n k) (h : n = m) :
    (P.inputCast h).circuit.erase = P.circuit.erase := by
  cases h
  rfl

@[simp] theorem outputCast_erase {n k l : Nat} (P : XorProgram n k) (h : k = l) :
    (P.outputCast h).circuit.erase = P.circuit.erase := rfl

@[simp] theorem outputCast_eval {n k l : Nat} (P : XorProgram n k)
    (h : k = l) (a : BitModels n) (i : Fin l) :
    (P.outputCast h).toProgram.eval a i =
      P.toProgram.eval a (Fin.cast h.symm i) := rfl

/-- `R₁`, then one copy of `H`, then `R₂` on H's existing output wires.
The output layout is exactly `(x, H(R₁(x)), R₂(H(R₁(x))))`.
There is deliberately no `parallel H (H.compose R₂)` call. -/
def oneCopy {n a h d : Nat} (R₁ : XorProgram n a)
    (H : XorProgram a h) (R₂ : XorProgram h d) : XorProgram n (n + (h + d)) :=
  let RH := R₁.follow (H.rewire R₁.output)
  (RH.keepFollow (R₂.rewire RH.output)).keepInputs

@[simp] theorem oneCopy_gates {n a h d : Nat} (R₁ : XorProgram n a)
    (H : XorProgram a h) (R₂ : XorProgram h d) :
    (oneCopy R₁ H R₂).gates = R₁.gates + H.gates + R₂.gates := rfl

theorem oneCopy_eval {n a h d : Nat} (R₁ : XorProgram n a)
    (H : XorProgram a h) (R₂ : XorProgram h d) (x : BitModels n) :
    (oneCopy R₁ H R₂).toProgram.eval x =
      Fin.append x (Fin.append
        (H.toProgram.eval (R₁.toProgram.eval x))
        (R₂.toProgram.eval (H.toProgram.eval (R₁.toProgram.eval x)))) := by
  let RH := R₁.follow (H.rewire R₁.output)
  have hRH : RH.toProgram.eval x = H.toProgram.eval (R₁.toProgram.eval x) := by
    simp only [RH, follow_toProgram, rewire_toProgram]
    exact (Program.follow_eval R₁.toProgram (H.toProgram.rewire R₁.output) x).trans
      (Program.rewire_eval H.toProgram R₁.output (R₁.toProgram.circuit.run x))
  change (RH.keepFollow (R₂.rewire RH.output)).keepInputs.toProgram.eval x = _
  rw [keepInputs_eval, keepFollow_eval, rewire_toProgram, Program.rewire_eval]
  change Fin.append x (Fin.append (RH.toProgram.eval x)
      (R₂.toProgram.eval (RH.toProgram.eval x))) = _
  rw [hRH]

theorem oneCopy_erased_blocks {n a h d : Nat} (R₁ : XorProgram n a)
    (H : XorProgram a h) (R₂ : XorProgram h d) :
    (oneCopy R₁ H R₂).circuit.erase =
      (R₁.circuit.erase ++
        H.circuit.erase.map
          (RawGate.map (liftRef a (n + R₁.gates) (fun i => (R₁.output i).val)))) ++
        R₂.circuit.erase.map
          (RawGate.map (liftRef h (n + (R₁.gates + H.gates))
            (fun i => ((R₁.follow (H.rewire R₁.output)).output i).val))) := by
  simp only [oneCopy, keepInputs, keepFollow, follow, rewire,
    XorCircuit.erase_extend, XorCircuit.erase_rewire]

/-- The retained H references are all below the R₂ block's first wire.
They are unchanged by the cast used to retain them after R₂ is appended. -/
theorem retained_output_reference {n k l : Nat} (P : XorProgram n k)
    (Q : XorProgram (n + P.gates) l) (i : Fin k) :
    ((P.keepFollow Q).output (Fin.castAdd l i)).val = (P.output i).val ∧
      ((P.keepFollow Q).output (Fin.castAdd l i)).val < n + P.gates := by
  simpa only [keepFollow, Fin.addCases_left, Fin.coe_cast, Fin.coe_castAdd] using
    And.intro (Eq.refl (P.output i).val) (P.output i).isLt

theorem oneCopy_primary_reference {n a h d : Nat} (R₁ : XorProgram n a)
    (H : XorProgram a h) (R₂ : XorProgram h d) (i : Fin n) :
    ((oneCopy R₁ H R₂).output (Fin.castAdd (h + d) i)).val = i.val := by
  simp only [oneCopy, keepInputs, Fin.addCases_left, Fin.coe_castAdd]

theorem oneCopy_H_reference {n a h d : Nat} (R₁ : XorProgram n a)
    (H : XorProgram a h) (R₂ : XorProgram h d) (i : Fin h) :
    ((oneCopy R₁ H R₂).output (Fin.natAdd n (Fin.castAdd d i))).val =
      ((R₁.follow (H.rewire R₁.output)).output i).val ∧
    ((oneCopy R₁ H R₂).output (Fin.natAdd n (Fin.castAdd d i))).val <
      n + (R₁.gates + H.gates) := by
  simpa only [oneCopy, keepInputs, Fin.addCases_right, follow, rewire] using
    retained_output_reference (R₁.follow (H.rewire R₁.output))
      (R₂.rewire (R₁.follow (H.rewire R₁.output)).output) i

/-- Endpoint ordering of the three emitted gate blocks. H's block occurs
exactly once. Existing output aliases may lie before their own gate block. -/
theorem oneCopy_block_offsets {n a h d : Nat} (R₁ : XorProgram n a)
    (H : XorProgram a h) (R₂ : XorProgram h d) :
    n ≤ n + R₁.gates ∧
    n + R₁.gates ≤ n + (R₁.gates + H.gates) ∧
    n + (R₁.gates + H.gates) ≤
      n + (R₁.gates + H.gates + R₂.gates) ∧
    n + (oneCopy R₁ H R₂).gates =
      n + (R₁.gates + H.gates + R₂.gates) := by
  simp only [oneCopy_gates]
  exact ⟨Nat.le_add_right _ _, Nat.add_le_add_left (Nat.le_add_right _ _) _,
    Nat.add_le_add_left (Nat.le_add_right _ _) _, trivial⟩

end XorProgram

/-- Erased, finite data only: there is no function-valued output array in the
serialized artifact. Natural references have the exact bounds below. -/
structure RawProgram where
  inputs : Nat
  gates : List RawGate
  outputs : List Nat
  deriving Repr

namespace RawProgram

def Valid (P : RawProgram) : Prop :=
  Topological P.inputs P.gates ∧
    ∀ v ∈ P.outputs, v < P.inputs + P.gates.length

/-- A raw append constructor. `inputRefs` is a finite input-reference table;
the resulting payload contains only finite lists of natural references.
No source gates are duplicated: append is literal list concatenation. -/
def append (P Q : RawProgram) (inputRefs : Fin Q.inputs → Nat) : RawProgram :=
  let start := P.inputs + P.gates.length
  let rename := liftRef Q.inputs start inputRefs
  ⟨P.inputs, P.gates ++ Q.gates.map (RawGate.map rename), Q.outputs.map rename⟩

theorem append_valid (P Q : RawProgram) (refs : Fin Q.inputs → Nat)
    (hP : P.Valid) (hQ : Q.Valid)
    (hrefs : ∀ i, refs i < P.inputs + P.gates.length) :
    (P.append Q refs).Valid := by
  constructor
  · exact hP.1.append (hQ.1.lift refs hrefs)
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have h := liftRef_lt refs hrefs (hQ.2 w hw)
    simpa only [append, List.length_append, List.length_map, Nat.add_assoc] using h

@[simp] theorem append_gate_count (P Q : RawProgram) (refs : Fin Q.inputs → Nat) :
    (P.append Q refs).gates.length = P.gates.length + Q.gates.length := by
  simp [append]

end RawProgram

def XorProgram.serialize {n k : Nat} (P : XorProgram n k) : RawProgram :=
  ⟨n, P.circuit.erase, List.ofFn (fun i => (P.output i).val)⟩

theorem XorProgram.serialize_topological {n k : Nat} (P : XorProgram n k) :
    Topological P.serialize.inputs P.serialize.gates :=
  P.circuit.erase_topological

theorem XorProgram.serialize_lengths {n k : Nat} (P : XorProgram n k) :
    P.serialize.gates.length = P.gates ∧ P.serialize.outputs.length = k := by
  simp [XorProgram.serialize]

theorem XorProgram.serialize_output_bound {n k : Nat} (P : XorProgram n k)
    (v : Nat) (hv : v ∈ P.serialize.outputs) : v < n + P.gates := by
  simp only [XorProgram.serialize, List.mem_ofFn] at hv
  obtain ⟨i, rfl⟩ := hv
  exact (P.output i).isLt

theorem XorProgram.serialize_refines {n k : Nat} (P : XorProgram n k)
    (a : BitModels n) (values : Nat → Bool)
    (hvalues : ∀ i : Fin n, values i.val = a i) :
    P.serialize.outputs.map (runRaw n values P.serialize.gates) =
      List.ofFn (P.toProgram.eval a) := by
  simp only [XorProgram.serialize, List.map_ofFn]
  congr 1
  funext i
  exact runRaw_refines P.circuit a values hvalues (P.output i)

/-- Exact data refinement, not merely equality of truth tables: raw appending
is the erasure of the supplied `Program.follow (Program.rewire ...)` pattern. -/
theorem XorProgram.serialize_append {n k l : Nat} (P : XorProgram n k)
    (Q : XorProgram k l) :
    (P.follow (Q.rewire P.output)).serialize =
      P.serialize.append Q.serialize (fun i => (P.output i).val) := by
  simp [XorProgram.serialize, XorProgram.follow, XorProgram.rewire,
    XorCircuit.erase_extend, XorCircuit.erase_rewire, RawProgram.append,
    XorCircuit.erase_length, List.map_ofFn, liftWire_val, Function.comp_def]

namespace SerializedDyadicEncoder

/-- Input width; the code length is four times this value. The recurrence
avoids division casts in the actual constructor. -/
def messageWidth (D : Nat) : Nat → Nat
  | 0 => 16 * D
  | ell + 1 => 2 * messageWidth D ell

theorem messageWidth_formula (D ell : Nat) :
    messageWidth D ell = 16 * D * 2 ^ ell := by
  induction ell with
  | zero => simp [messageWidth]
  | succ ell ih => rw [messageWidth, ih, pow_succ]; ring

theorem codeLength_formula (D ell : Nat) :
    4 * messageWidth D ell = (64 * D) * 2 ^ ell := by
  rw [messageWidth_formula]
  ring

theorem messageWidth_div_four (D ell : Nat) :
    messageWidth D ell = ((64 * D) * 2 ^ ell) / 4 := by
  rw [← codeLength_formula D ell]
  omega

theorem messageWidth_pos {D : Nat} (hD : 0 < D) (ell : Nat) :
    0 < messageWidth D ell := by
  induction ell with
  | zero => simpa only [messageWidth] using Nat.mul_pos (by decide : 0 < 16) hD
  | succ ell ih => exact Nat.mul_pos (by decide : 0 < 2) ih

/-- The base and two amplifier streams are data. No distance theorem,
local-matrix existence theorem, or construction-runtime claim is assumed here.
At level `ell+1`, R₁ has N/4→N/8 wires and R₂ has N/2→N/4 wires. -/
def encoder {D : Nat}
    (base : XorProgram (messageWidth D 0) (4 * messageWidth D 0))
    (R₁ : (ell : Nat) → XorProgram (2 * messageWidth D ell) (messageWidth D ell))
    (R₂ : (ell : Nat) → XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell)) :
    (ell : Nat) → XorProgram (messageWidth D ell) (4 * messageWidth D ell)
  | 0 => base
  | ell + 1 =>
      (XorProgram.oneCopy (R₁ ell) (encoder base R₁ R₂ ell) (R₂ ell)).outputCast
        (by simp only [messageWidth]; omega)

/-- The exact dyadic input/output dimensions, using only transports.
These transports append no gate and do not change the raw wire identifiers. -/
def exactEncoder {D : Nat}
    (base : XorProgram (messageWidth D 0) (4 * messageWidth D 0))
    (R₁ : (ell : Nat) → XorProgram (2 * messageWidth D ell) (messageWidth D ell))
    (R₂ : (ell : Nat) → XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell))
    (ell : Nat) :
    XorProgram (((64 * D) * 2 ^ ell) / 4) ((64 * D) * 2 ^ ell) :=
  ((encoder base R₁ R₂ ell).inputCast (messageWidth_div_four D ell)).outputCast
    (codeLength_formula D ell)

@[simp] theorem exactEncoder_gates {D : Nat}
    (base : XorProgram (messageWidth D 0) (4 * messageWidth D 0))
    (R₁ : (ell : Nat) → XorProgram (2 * messageWidth D ell) (messageWidth D ell))
    (R₂ : (ell : Nat) → XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell))
    (ell : Nat) :
    (exactEncoder base R₁ R₂ ell).gates = (encoder base R₁ R₂ ell).gates := by
  simp [exactEncoder, XorProgram.outputCast]

@[simp] theorem exactEncoder_erase {D : Nat}
    (base : XorProgram (messageWidth D 0) (4 * messageWidth D 0))
    (R₁ : (ell : Nat) → XorProgram (2 * messageWidth D ell) (messageWidth D ell))
    (R₂ : (ell : Nat) → XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell))
    (ell : Nat) :
    (exactEncoder base R₁ R₂ ell).circuit.erase =
      (encoder base R₁ R₂ ell).circuit.erase := by
  simp [exactEncoder]

theorem encoder_step_gates {D : Nat}
    (base : XorProgram (messageWidth D 0) (4 * messageWidth D 0))
    (R₁ : (ell : Nat) → XorProgram (2 * messageWidth D ell) (messageWidth D ell))
    (R₂ : (ell : Nat) → XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell))
    (ell : Nat) :
    (encoder base R₁ R₂ (ell + 1)).gates =
      (R₁ ell).gates + (encoder base R₁ R₂ ell).gates + (R₂ ell).gates := rfl

/-- Conditional gate-count closure for the *actual one-copy constructor*.
The hypotheses are separately named local/base bounds, not the desired final
linear encoder bound. All quantities stay symbolic, including D=16^384. -/
theorem encoder_gates_le {D : Nat} (hD : 0 < D)
    (base : XorProgram (messageWidth D 0) (4 * messageWidth D 0))
    (R₁ : (ell : Nat) → XorProgram (2 * messageWidth D ell) (messageWidth D ell))
    (R₂ : (ell : Nat) → XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell))
    (hbase : base.gates ≤ 4 * D * D + 1)
    (hR₁ : ∀ ell, (R₁ ell).gates ≤ D * (2 * messageWidth D ell) + 1)
    (hR₂ : ∀ ell, (R₂ ell).gates ≤ D * (4 * messageWidth D ell) + 1)
    (ell : Nat) :
    (encoder base R₁ R₂ ell).gates ≤ 2 * D * (4 * messageWidth D ell) := by
  induction ell with
  | zero =>
    change base.gates ≤ 2 * D * (4 * (16 * D))
    have hDD : 1 ≤ D * D := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    nlinarith
  | succ ell ih =>
    rw [encoder_step_gates]
    have h1 := hR₁ ell
    have h2 := hR₂ ell
    have hw := messageWidth_pos hD ell
    have hDw : 1 ≤ D * messageWidth D ell :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    simp only [messageWidth]
    nlinarith

theorem serialized_encoder_gate_bound {D : Nat} (hD : 0 < D)
    (base : XorProgram (messageWidth D 0) (4 * messageWidth D 0))
    (R₁ : (ell : Nat) → XorProgram (2 * messageWidth D ell) (messageWidth D ell))
    (R₂ : (ell : Nat) → XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell))
    (hbase : base.gates ≤ 4 * D * D + 1)
    (hR₁ : ∀ ell, (R₁ ell).gates ≤ D * (2 * messageWidth D ell) + 1)
    (hR₂ : ∀ ell, (R₂ ell).gates ≤ D * (4 * messageWidth D ell) + 1)
    (ell : Nat) :
    (encoder base R₁ R₂ ell).serialize.gates.length ≤
      2 * D * ((64 * D) * 2 ^ ell) := by
  simpa only [XorProgram.serialize, XorCircuit.erase_length, codeLength_formula]
    using encoder_gates_le hD base R₁ R₂ hbase hR₁ hR₂ ell

end SerializedDyadicEncoder
end QecReliability.SharedCircuit
