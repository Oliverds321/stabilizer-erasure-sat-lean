import QecReliability.BinaryAdder
import Mathlib.Data.Nat.Log

/-! A balanced binary-adder tree, zero padding, and a linear-size population counter. -/
namespace QecReliability.SharedCircuit
open scoped BigOperators

def leaves : ℕ → ℕ
  | 0 => 1
  | k + 1 => leaves k + leaves k

theorem leaves_pow (k : ℕ) : leaves k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [leaves, ih, pow_succ, Nat.mul_two]

def countTree {v : ℕ} : (k : ℕ) → (Fin (leaves k) → Fin v) → Fin v → Program v (k + 1)
  | 0, xs, _ => Program.pure xs
  | k + 1, xs, zero =>
      let P := (countTree k (fun i => xs (Fin.castAdd (leaves k) i)) zero).parallel
        (countTree k (fun i => xs (Fin.natAdd (leaves k) i)) zero)
      P.follow (ripple (k + 1) (fun i => P.output (Fin.castAdd (k + 1) i))
        (fun i => P.output (Fin.natAdd (k + 1) i)) (Fin.castAdd P.gates zero))

theorem countTree_gates {v : ℕ} (k : ℕ) (xs : Fin (leaves k) → Fin v) (zero : Fin v) :
    (countTree k xs zero).gates + 5 * (k + 2) = 10 * leaves k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    have hl := ih (fun i => xs (Fin.castAdd (leaves k) i)) zero
    have hr := ih (fun i => xs (Fin.natAdd (leaves k) i)) zero
    simp only [countTree, Program.follow, Program.parallel]
    rw [ripple_gates]
    simp only [leaves]
    omega

theorem countTree_correct {v : ℕ} (k : ℕ) (xs : Fin (leaves k) → Fin v) (zero : Fin v)
    (a : BitModels v) (hz : a zero = false) :
    wordValue ((countTree k xs zero).eval a) = ∑ i, (a (xs i)).toNat := by
  induction k generalizing v with
  | zero =>
    simp [countTree, Program.eval, Program.pure, Circuit.run, wordValue, leaves]
  | succ k ih =>
    let L := countTree k (fun i => xs (Fin.castAdd (leaves k) i)) zero
    let R := countTree k (fun i => xs (Fin.natAdd (leaves k) i)) zero
    let P := L.parallel R
    change wordValue ((P.follow _).eval a) = _
    rw [Program.follow_eval, ripple_correct, Circuit.run_primary, hz]
    have hl : (P.circuit.run a ∘ fun i => P.output (Fin.castAdd (k + 1) i)) = L.eval a := by
      funext i
      exact (congrFun (Program.parallel_eval L R a) (Fin.castAdd (k + 1) i)).trans (Fin.append_left _ _ i)
    have hr : (P.circuit.run a ∘ fun i => P.output (Fin.natAdd (k + 1) i)) = R.eval a := by
      funext i
      exact (congrFun (Program.parallel_eval L R a) (Fin.natAdd (k + 1) i)).trans (Fin.append_right _ _ i)
    rw [hl, hr]
    change wordValue ((countTree k _ _).eval a) + wordValue ((countTree k _ _).eval a) + 0 = _
    rw [ih _ _ a hz, ih _ _ a hz]
    simp only [Nat.add_zero]
    exact (Fin.sum_univ_add (fun i : Fin (leaves k + leaves k) => (a (xs i)).toNat)).symm

def counterDepth (n : ℕ) : ℕ := Nat.log2 (max 1 n) + 1

theorem counterDepth_bounds (n : ℕ) :
    n ≤ leaves (counterDepth n) ∧ leaves (counterDepth n) ≤ 2 * max 1 n := by
  rw [leaves_pow]
  have hp : 0 < max 1 n := by omega
  have hlo := Nat.log2_self_le (Nat.ne_of_gt hp)
  have hhi := Nat.lt_log2_self (n := max 1 n)
  constructor
  · unfold counterDepth
    omega
  · unfold counterDepth
    rw [pow_succ]
    omega

def paddedWire (n : ℕ) (i : Fin (leaves (counterDepth n))) : Fin (n + 1) :=
  if h : i.val < n then (⟨i.val, h⟩ : Fin n).castSucc else Fin.last n

def population (n : ℕ) : Program n (counterDepth n + 1) :=
  (Program.constant n false).follow (countTree (counterDepth n) (paddedWire n) (Fin.last n))

theorem population_gates (n : ℕ) : (population n).gates ≤ 20 * n + 11 := by
  have ht := countTree_gates (counterDepth n) (paddedWire n) (Fin.last n)
  have hb := (counterDepth_bounds n).2
  change 1 + (countTree (counterDepth n) (paddedWire n) (Fin.last n)).gates ≤ _
  have hp : 1 ≤ counterDepth n := by unfold counterDepth; omega
  omega

set_option backward.isDefEq.respectTransparency false in
theorem population_correct (n : ℕ) (a : BitModels n) :
    wordValue ((population n).eval a) = ∑ i, (a i).toNat := by
  rw [population, Program.follow_eval, countTree_correct]
  · have hb := (counterDepth_bounds n).1
    let d := leaves (counterDepth n) - n
    have he : n + d = leaves (counterDepth n) := Nat.add_sub_of_le hb
    have hsum : (∑ i : Fin (n + d),
        ((Program.constant n false).circuit.run a (paddedWire n (Fin.cast he i))).toNat) =
        ∑ i, ((Program.constant n false).circuit.run a (paddedWire n i)).toNat :=
      Equiv.sum_comp (finCongr he) (fun i =>
        ((Program.constant n false).circuit.run a (paddedWire n i)).toNat)
    rw [← hsum, Fin.sum_univ_add]
    have hl : (∑ i : Fin n, ((Program.constant n false).circuit.run a
        (paddedWire n (Fin.cast he (Fin.castAdd d i)))).toNat) = ∑ i, (a i).toNat := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [paddedWire, Fin.coe_cast, Fin.coe_castAdd, i.isLt, ↓reduceDIte]
      change ((Program.constant n false).circuit.run a (Fin.castAdd 1 i)).toNat = _
      exact congrArg Bool.toNat (Circuit.run_primary (Program.constant n false).circuit a i)
    have hr : (∑ i : Fin d, ((Program.constant n false).circuit.run a
        (paddedWire n (Fin.cast he (Fin.natAdd n i)))).toNat) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬ (Fin.cast he (Fin.natAdd n i)).val < n := by simp
      simp only [paddedWire, hn, ↓reduceDIte]
      have hz := Program.constant_eval n false a
      exact congrArg Bool.toNat (congrFun hz 0)
    rw [hl, hr, Nat.add_zero]
  · exact congrFun (Program.constant_eval n false a) 0

end QecReliability.SharedCircuit
