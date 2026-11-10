import QecReliability.WalkAvoidance
import QecReliability.TransposeQuantumBridge
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Distance amplification by every fixed-length port walk. The symbol circuit
only reuses outputs of the supplied binary encoder, with all sinks counted. -/
noncomputable section
namespace QecReliability.ExpanderWalk
open scoped BigOperators
open Classical CodeHash SharedCircuit

/-- Explicit mixed-radix labeling, not a cardinality-choice bijection. -/
def walkLabel (m d k : ℕ) : Fin (m * d^k) ≃ Fin m × (Fin k → Fin d) :=
  ((Equiv.prodCongr (Equiv.refl (Fin m)) finFunctionFinEquiv).trans finProdFinEquiv).symm

namespace PortGraph
variable {m d : ℕ} (G : PortGraph m d)

def symbols {A : Type*} (encode : A → Word m) (k : ℕ) : A → Fin (m*d^k) → Word (k+1) :=
  fun a i j => encode a (G.visits (walkLabel m d k i).1 (walkLabel m d k i).2 j)

def agreementSet (x y : Word m) : Finset (Fin m) := Finset.univ.filter (fun i => x i = y i)

theorem agreement_weight (x y : Word m) :
    (agreementSet x y).card + weight (x-y) = m := by
  unfold agreementSet weight
  simp only [Pi.sub_apply, sub_ne_zero]
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin m, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x i = y i <;> simp [hi]
    _ = m := by simp

theorem symbols_eq_iff {A : Type*} (encode : A → Word m) (k : ℕ) (a b : A)
    (i : Fin (m*d^k)) :
    G.symbols encode k a i = G.symbols encode k b i ↔
      G.stays (agreementSet (encode a) (encode b)) (walkLabel m d k i).1 (walkLabel m d k i).2 := by
  simp [symbols, stays, agreementSet, funext_iff]

theorem symbols_agreements {A : Type*} (encode : A → Word m) (k : ℕ) (a b : A) :
    agreements (G.symbols encode k a) (G.symbols encode k b) =
      (Finset.univ.filter (fun p : Fin m × (Fin k → Fin d) =>
        G.stays (agreementSet (encode a) (encode b)) p.1 p.2)).card := by
  simp only [agreements, Finset.card_filter, G.symbols_eq_iff]
  exact (walkLabel m d k).sum_comp (fun p =>
    if G.stays (agreementSet (encode a) (encode b)) p.1 p.2 then (1 : ℕ) else 0)

/-- Pairwise binary Hamming distance supplies the agreement-set density. -/
theorem symbol_agreement_bound {A : Type*} (encode : A → Word m)
    {g δ : ℝ} (hg : G.PositiveGap g) (hβ : 0 < 1-g*δ)
    (hd : ∀ a b, a ≠ b → δ*m ≤ (weight (encode a - encode b) : ℝ))
    (k : ℕ) (a b : A) (hab : a ≠ b) :
    (agreements (G.symbols encode k a) (G.symbols encode k b) : ℝ) ≤
      ((m*d^k : ℕ) : ℝ)*(1-g*δ)^k := by
  rw [G.symbols_agreements]
  apply G.avoidance_count hg _ _ hβ
  have hc := agreement_weight (encode a) (encode b)
  have hc' : ((agreementSet (encode a) (encode b)).card : ℝ) +
      (weight (encode a - encode b) : ℝ) = m := by exact_mod_cast hc
  linarith [hd a b hab]

/-- The exact strict threshold required by the existing symbol/hash interface. -/
theorem symbol_separation {A : Type*} (encode : A → Word m)
    {α g : ℝ} (hg : G.PositiveGap g) (hβ : 0 < 1-g*(α/2))
    (hd : ∀ a b, a ≠ b → (α/2)*m ≤ (weight (encode a - encode b) : ℝ))
    (k : ℕ) (hk : (1-g*(α/2))^k < α/4) (a b : A) (hab : a ≠ b) :
    (agreements (G.symbols encode k a) (G.symbols encode k b) : ℝ) <
      α * (m*d^k) / 4 := by
  have hM : (0 : ℝ) < (m*d^k : ℕ) := by
    exact_mod_cast Nat.mul_pos G.vertices_pos (pow_pos G.degree_pos k)
  have h := (G.symbol_agreement_bound encode hg hβ hd k a b hab).trans_lt
    (mul_lt_mul_of_pos_left hk hM)
  convert h using 1
  push_cast
  ring

/-- A fixed walk length exists for every positive fixed gap and 0<alpha<=1. -/
theorem walk_length_exists {α g : ℝ} (hg : G.PositiveGap g)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    0 < 1-g*(α/2) ∧ ∃ k : ℕ, (1-g*(α/2))^k < α/4 := by
  have hmul := mul_le_mul hg.gap_le_one (show α/2 ≤ (1:ℝ)/2 by linarith)
    (by positivity : 0 ≤ α/2) (by norm_num : (0:ℝ) ≤ 1)
  have hβ : 0 < 1-g*(α/2) := by nlinarith
  refine ⟨hβ, exists_pow_lt_of_lt_one (by positivity) ?_⟩
  nlinarith [mul_pos hg.gap_pos (show 0 < α/2 by positivity)]

def symbolProgram {q : ℕ} (P : Program q m) (k : ℕ) : Program q ((m*d^k)*(k+1)) :=
  P.compose (Program.pure (fun i =>
    let ij := finProdFinEquiv.symm i
    let walk := walkLabel m d k ij.1
    G.visits walk.1 walk.2 ij.2))

theorem symbolProgram_correct {A : Type*} {q : ℕ} (encode : A → Word m)
    (e : A ≃ BitModels q) (P : Program q m)
    (hP : ∀ a i, boolBit (P.eval (e a) i) = encode a i)
    (k : ℕ) (a : A) (i : Fin (m*d^k)) (j : Fin (k+1)) :
    boolBit ((G.symbolProgram P k).eval (e a) (finProdFinEquiv (i,j))) =
      G.symbols encode k a i j := by
  simp only [symbolProgram, Program.compose_eval, Program.pure_eval,
    Function.comp_apply, Equiv.symm_apply_apply]
  exact hP a _

theorem symbolProgram_gates {q : ℕ} (P : Program q m) (k : ℕ) :
    (G.symbolProgram P k).gates = P.gates := by rfl

theorem symbolProgram_size {q : ℕ} (P : Program q m) (k : ℕ) :
    q + (G.symbolProgram P k).gates + 2*(G.symbolProgram P k).gates + (m*d^k)*(k+1) =
      q + 3*P.gates + (d^k*(k+1))*m := by rw [G.symbolProgram_gates]; ring

/-- Incoming gate edges and every output sink are included, even under fan-out. -/
theorem symbolProgram_total_size {q : ℕ} (P : Program q m) (k : ℕ) :
    q + (G.symbolProgram P k).gates + (G.symbolProgram P k).circuit.edges + (m*d^k)*(k+1) ≤
      q + 3*P.gates + (d^k*(k+1))*m := by
  have he := (G.symbolProgram P k).circuit.edges_le
  calc
    _ ≤ q + (G.symbolProgram P k).gates + 2*(G.symbolProgram P k).gates + (m*d^k)*(k+1) := by omega
    _ = _ := G.symbolProgram_size P k

end PortGraph
end QecReliability.ExpanderWalk
