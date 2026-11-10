import QecReliability.CNFBlocks
import QecReliability.CircuitPrograms
import Mathlib.Tactic.FinCases

/-! A five-gate full adder and a constructive ripple adder on supplied wires. -/
namespace QecReliability.SharedCircuit
open scoped BigOperators

def wordValue {k : ℕ} (a : BitModels k) : ℕ := ∑ i, (a i).toNat * 2 ^ i.val

theorem wordValue_cons {k : ℕ} (b : Bool) (a : BitModels k) :
    wordValue (Fin.cons b a) = b.toNat + 2 * wordValue a := by
  simp only [wordValue, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    pow_zero, mul_one, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem wordValue_single (a : BitModels 1) : wordValue a = (a 0).toNat := by
  simp [wordValue]

def fullAdder : Program 3 2 where
  gates := 5
  circuit := ((((Circuit.nil.snoc (.xorGate 0 1)).snoc (.xorGate 3 2)).snoc
    (.andGate 0 1)).snoc (.andGate 3 2)).snoc (.xorGate 5 6)
  output := ![4, 7]

theorem fullAdder_correct (a : BitModels 3) :
    (fullAdder.eval a 0).toNat + 2 * (fullAdder.eval a 1).toNat =
      (a 0).toNat + (a 1).toNat + (a 2).toNat := by
  have he : a = ![a 0, a 1, a 2] := by funext i; fin_cases i <;> rfl
  rw [he]
  generalize a 0 = x, a 1 = y, a 2 = c
  cases x <;> cases y <;> cases c <;> decide

def ripple {v : ℕ} : (k : ℕ) → (Fin k → Fin v) → (Fin k → Fin v) → Fin v → Program v (k + 1)
  | 0, _, _, c => Program.pure (fun _ => c)
  | k + 1, x, y, c =>
      let F := fullAdder.rewire ![x 0, y 0, c]
      let R := ripple k (fun i => Fin.castAdd F.gates (x i.succ))
        (fun i => Fin.castAdd F.gates (y i.succ)) (F.output 1)
      F.follow (((Program.pure (fun _ : Fin 1 => F.output 0)).parallel R).outputCast (by omega))

theorem ripple_gates {v : ℕ} (k : ℕ) (x y : Fin k → Fin v) (c : Fin v) :
    (ripple k x y c).gates = 5 * k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    simp only [ripple, Program.follow, Program.outputCast, Program.parallel, Program.pure,
      Program.rewire, fullAdder, Nat.zero_add]
    rw [ih]
    omega

theorem ripple_eval_succ {v k : ℕ} (x y : Fin (k + 1) → Fin v) (c : Fin v) (a : BitModels v) :
    (ripple (k + 1) x y c).eval a =
      let F := fullAdder.rewire ![x 0, y 0, c]
      let R := ripple k (fun i => Fin.castAdd F.gates (x i.succ))
        (fun i => Fin.castAdd F.gates (y i.succ)) (F.output 1)
      Fin.cons (F.eval a 0) (R.eval (F.circuit.run a)) := by
  simp only [ripple, Program.follow_eval]
  change (fun i => ((Program.pure _).parallel _).eval _ (Fin.cast _ i)) = _
  rw [Program.parallel_eval, Program.pure_eval]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hj : Fin.cast (show 1 + (k + 1) = k + 1 + 1 by omega).symm j.succ = Fin.natAdd 1 j := by
      apply Fin.ext; simp; omega
    rw [hj]
    rw [Fin.append_right]
    rfl

theorem ripple_correct {v : ℕ} (k : ℕ) (x y : Fin k → Fin v) (c : Fin v) (a : BitModels v) :
    wordValue ((ripple k x y c).eval a) = wordValue (a ∘ x) + wordValue (a ∘ y) + (a c).toNat := by
  induction k generalizing v with
  | zero => simp [ripple, Program.pure_eval, wordValue]
  | succ k ih =>
    rw [ripple_eval_succ, wordValue_cons]
    rw [ih]
    have hx : ((fullAdder.rewire ![x 0, y 0, c]).circuit.run a ∘
        fun i : Fin k => Fin.castAdd (fullAdder.rewire ![x 0, y 0, c]).gates (x i.succ)) =
        fun i => a (x i.succ) := by funext i; exact Circuit.run_primary _ _ _
    have hy : ((fullAdder.rewire ![x 0, y 0, c]).circuit.run a ∘
        fun i : Fin k => Fin.castAdd (fullAdder.rewire ![x 0, y 0, c]).gates (y i.succ)) =
        fun i => a (y i.succ) := by funext i; exact Circuit.run_primary _ _ _
    have hf := fullAdder_correct (a ∘ ![x 0, y 0, c])
    have he : (fullAdder.rewire ![x 0, y 0, c]).eval a = fullAdder.eval (a ∘ ![x 0, y 0, c]) :=
      Program.rewire_eval _ _ _
    change _ + 2 * (wordValue _ + wordValue _ +
      ((fullAdder.rewire ![x 0, y 0, c]).eval a 1).toNat) = _
    rw [hx, hy, he]
    have ex : a ∘ x = Fin.cons (a (x 0)) (fun i => a (x i.succ)) := by funext i; refine Fin.cases rfl (fun _ => rfl) i
    have ey : a ∘ y = Fin.cons (a (y 0)) (fun i => a (y i.succ)) := by funext i; refine Fin.cases rfl (fun _ => rfl) i
    rw [ex, ey, wordValue_cons, wordValue_cons]
    change (fullAdder.eval (a ∘ ![x 0, y 0, c]) 0).toNat +
      2 * (fullAdder.eval (a ∘ ![x 0, y 0, c]) 1).toNat =
      (a (x 0)).toNat + (a (y 0)).toNat + (a c).toNat at hf
    omega

end QecReliability.SharedCircuit
