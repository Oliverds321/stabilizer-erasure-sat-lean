import QecReliability.XorCircuitCore

/-! A concrete validator/conversion for supplied shared Boolean DAGs. Only XOR
and false-constant gates are accepted; arbitrary wire reuse is unrestricted. -/
namespace QecReliability.SharedCircuit

def Circuit.xorOnly {n : ℕ} : {g : ℕ} → Circuit n g → Bool
  | _, .nil => true
  | _, .snoc C (.xorGate _ _) => C.xorOnly
  | _, .snoc C (.constGate false) => C.xorOnly
  | _, .snoc _ _ => false

def Circuit.asXor {n : ℕ} : {g : ℕ} → (C : Circuit n g) → C.xorOnly = true → XorCircuit n g
  | _, .nil, _ => .nil
  | _, .snoc C (.xorGate x y), h => .xor (C.asXor h) x y
  | _, .snoc C (.constGate false), h => .zero (C.asXor h)
  | _, .snoc _ (.andGate _ _), h => by contradiction
  | _, .snoc _ (.notGate _), h => by contradiction
  | _, .snoc _ (.constGate true), h => by contradiction

theorem Circuit.asXor_toCircuit {n g : ℕ} (C : Circuit n g) (h : C.xorOnly = true) :
    (C.asXor h).toCircuit = C := by
  induction C with
  | nil => rfl
  | snoc C gate ih =>
    cases gate with
    | xorGate x y => exact congrArg (fun c => c.snoc (.xorGate x y)) (ih h)
    | constGate b =>
      cases b
      · exact congrArg (fun c => c.snoc (.constGate false)) (ih h)
      · contradiction
    | andGate x y => contradiction
    | notGate x => contradiction

def Program.asXor {n m : ℕ} (P : Program n m) (h : P.circuit.xorOnly = true) : XorProgram n m :=
  ⟨P.gates, P.circuit.asXor h, P.output⟩

theorem Program.asXor_toProgram {n m : ℕ} (P : Program n m) (h : P.circuit.xorOnly = true) :
    (P.asXor h).toProgram = P := by
  cases P with
  | mk gates circuit output =>
    simp only [Program.asXor, XorProgram.toProgram, Circuit.asXor_toCircuit]

end QecReliability.SharedCircuit
