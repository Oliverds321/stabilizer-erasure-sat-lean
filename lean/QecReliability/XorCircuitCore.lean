import QecReliability.CircuitPrograms

namespace QecReliability.SharedCircuit

inductive XorCircuit (n : ℕ) : ℕ → Type where
  | nil : XorCircuit n 0
  | zero {g : ℕ} : XorCircuit n g → XorCircuit n (g + 1)
  | xor {g : ℕ} : XorCircuit n g → Fin (n + g) → Fin (n + g) → XorCircuit n (g + 1)

namespace XorCircuit

def toCircuit {n : ℕ} : {g : ℕ} → XorCircuit n g → Circuit n g
  | _, nil => .nil
  | _, zero C => C.toCircuit.snoc (.constGate false)
  | _, xor C x y => C.toCircuit.snoc (.xorGate x y)

end XorCircuit

structure XorProgram (n m : ℕ) where
  gates : ℕ
  circuit : XorCircuit n gates
  output : Fin m → Fin (n + gates)

namespace XorProgram

def toProgram {n m : ℕ} (P : XorProgram n m) : Program n m :=
  ⟨P.gates, P.circuit.toCircuit, P.output⟩

end XorProgram
end QecReliability.SharedCircuit
