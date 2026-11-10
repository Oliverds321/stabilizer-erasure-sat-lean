import QecReliability.WalkSymbols
import QecReliability.DyadicCodeFamily

/-! Ordinary binary code distance and an explicit spectral graph construct the
symbol separation premise, then the hash family and concrete quantum queries. -/
noncomputable section
namespace QecReliability.ExpanderWalk
open CodeHash SharedCircuit

/-- These inputs contain neither symbol separation nor hash probability. -/
structure WalkCode (q : ℕ) where
  m : ℕ
  d : ℕ
  L : ℕ
  c : ℕ
  steps : ℕ
  graph : PortGraph m d
  α : ℝ
  g : ℝ
  alpha_pos : 0 < α
  alpha_le_one : α ≤ 1
  spectral : graph.PositiveGap g
  binary : Word q →ₗ[F] Word m
  binary_distance : ∀ a, a ≠ 0 → (α/2)*m ≤ (weight (binary a) : ℝ)
  walk_small : (1-g*(α/2))^steps < α/4
  length_ge : m*d^steps ≤ L
  length_le : L ≤ 2*(m*d^steps)
  capacity : q ≤ c
  code : Word c →ₗ[F] Word L
  distance : ∀ a, a ≠ 0 → α*L ≤ (weight (code a) : ℝ)

theorem bitsVector_injective {q : ℕ} : Function.Injective (@bitsVector q) := by
  intro a b h
  funext i
  exact SharedCircuit.boolBit_injective (congrFun h i)

namespace WalkCode
variable {q : ℕ} (W : WalkCode q)

def binaryEncode {A : Type*} (e : A ≃ BitModels q) : A → Word W.m :=
  fun a => W.binary (bitsVector (e a))

theorem binary_pair_distance {A : Type*} (e : A ≃ BitModels q) (a b : A) (hab : a ≠ b) :
    (W.α/2)*W.m ≤ (weight (W.binaryEncode e a - W.binaryEncode e b) : ℝ) := by
  have hne : bitsVector (e a) - bitsVector (e b) ≠ 0 := by
    intro h
    exact hab (e.injective (bitsVector_injective (sub_eq_zero.mp h)))
  simpa only [binaryEncode, map_sub] using W.binary_distance _ hne

theorem beta_pos : 0 < 1-W.g*(W.α/2) :=
  (W.graph.walk_length_exists W.spectral W.alpha_pos W.alpha_le_one).1

def codingData {A : Type*} (e : A ≃ BitModels q) : CodingData A q where
  M := W.m*W.d^W.steps
  L := W.L
  t := W.steps+1
  k := W.c
  positive := Nat.mul_pos W.graph.vertices_pos (pow_pos W.graph.degree_pos _)
  length_ge := W.length_ge
  length_le := W.length_le
  capacity := W.capacity
  α := W.α
  alpha_pos := W.alpha_pos
  encode := W.graph.symbols (W.binaryEncode e) W.steps
  separation := by
    intro a b hab
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      W.graph.symbol_separation (W.binaryEncode e) W.spectral W.beta_pos
        (W.binary_pair_distance e) W.steps W.walk_small a b hab
  code := W.code
  distance := W.distance

/-- The two supplied forward encoders; the symbol DAG and transpose are generated. -/
structure Circuits where
  binary : Program q W.m
  binary_correct : ∀ b i, boolBit (binary.eval b i) = W.binary (bitsVector b) i
  code : Program W.c W.L
  code_xor : code.circuit.xorOnly = true
  code_correct : ∀ b i, boolBit (code.eval b i) = W.code (bitsVector b) i

variable {W}

def Circuits.forward {A : Type*} (K : W.Circuits) (e : A ≃ BitModels q) :
    ForwardCodingCircuits (W.codingData e) e where
  symbols := W.graph.symbolProgram K.binary W.steps
  symbols_correct := W.graph.symbolProgram_correct (W.binaryEncode e) e K.binary
    (fun a i => K.binary_correct (e a) i) W.steps
  code := K.code
  code_xor := K.code_xor
  code_correct := K.code_correct

def Circuits.gateBudget (K : W.Circuits) : ℕ :=
  K.binary.gates + W.L*(W.steps+2) + (1+W.L+2*K.code.gates)

theorem Circuits.forward_budget {A : Type*} (K : W.Circuits) (e : A ≃ BitModels q) :
    (K.forward e).hashGateBudget = K.gateBudget := by rfl

/-- Explicit constants when graph order and the two encoders are linear in q.
The additive b handles finitely many small lengths, including q=0. -/
theorem Circuits.linear_budget (K : W.Circuits) (a b u v : ℕ)
    (hm : W.m ≤ a*q+b) (hB : K.binary.gates ≤ u*q+v)
    (hC : K.code.gates ≤ u*W.L+v) :
    K.gateBudget ≤ (u+2*a*W.d^W.steps*(W.steps+3+2*u))*q +
      (3*v+1+2*b*W.d^W.steps*(W.steps+3+2*u)) := by
  have hL : W.L ≤ 2*((a*q+b)*W.d^W.steps) :=
    W.length_le.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hm))
  unfold Circuits.gateBudget
  nlinarith

/-- The already checked dyadic selector chooses the second code at every input
length; the base code at graph order and graph itself remain supplied. -/
def fromDyadic (FAM : DyadicCodeFamily) (hα1 : FAM.α ≤ 1)
    {m d : ℕ} (G : PortGraph m d) {g : ℝ} (hg : G.PositiveGap g)
    (B : Word q →ₗ[F] Word m)
    (hB : ∀ a, a ≠ 0 → (FAM.α/2)*m ≤ (weight (B a) : ℝ))
    (hM : dyadicLength FAM.base (4*q) FAM.base_pos ≤ m)
    (steps : ℕ) (hs : (1-g*(FAM.α/2))^steps < FAM.α/4) : WalkCode q := by
  have hm : m ≤ m*d^steps := by
    simpa using Nat.mul_le_mul_left m (show 1 ≤ d^steps from pow_pos G.degree_pos _)
  have hlarge := hM.trans hm
  have hc := second_padding_contract FAM.base q (m*d^steps) FAM.base_pos FAM.base_four hlarge
  exact {
    m := m, d := d, steps := steps, graph := G
    L := dyadicLength FAM.base (m*d^steps) FAM.base_pos
    c := dyadicLength FAM.base (m*d^steps) FAM.base_pos / 4
    α := FAM.α, g := g, alpha_pos := FAM.alpha_pos, alpha_le_one := hα1
    spectral := hg, binary := B, binary_distance := hB, walk_small := hs
    length_ge := hc.1, length_le := hc.2.1, capacity := hc.2.2.1
    code := FAM.encoder (dyadicIndex FAM.base (m*d^steps) FAM.base_pos)
    distance := by
      intro a ha
      simpa only [dyadicLength, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
        FAM.distance (dyadicIndex FAM.base (m*d^steps) FAM.base_pos) a ha }

end WalkCode

/-- Padding the base binary code to at most twice its length loses at most a
factor two of relative distance, with no symbol-separation hypothesis. -/
def appendZeros {q N : ℕ} (B : Word q →ₗ[F] Word N) (z : ℕ) : Word q →ₗ[F] Word (N+z) where
  toFun a := Fin.append (B a) 0
  map_add' a b := by ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' c a := by ext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem appendZeros_distance {q N z : ℕ} (B : Word q →ₗ[F] Word N)
    {α : ℝ} (hα : 0 ≤ α) (hz : z ≤ N)
    (hB : ∀ a, a ≠ 0 → α*N ≤ (weight (B a) : ℝ)) (a : Word q) (ha : a ≠ 0) :
    (α/2)*(N+z) ≤ (weight (appendZeros B z a) : ℝ) := by
  change _ ≤ (weight (Fin.append (B a) (0 : Word z)) : ℝ)
  rw [weight_append_zero]
  have hz' : (z : ℝ) ≤ N := by exact_mod_cast hz
  nlinarith [mul_le_mul_of_nonneg_left hz' hα, hB a ha]

open SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- Direct concrete query-size conclusion with spectral/code inputs. -/
theorem walk_quantum_query_size {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (W : WalkCode (keySize n r)) (K : W.Circuits)
    (i : Binary.CoefficientIndex r) (s : Fin (keySize n r+1))
    (ω : Seed W.L (W.steps+1)) (pre : List Bool) :
    PrefixCNF.Width 3 (PrefixCNF.restrict
      (quantumCell rows C i ((K.forward (keyBits n r)).compiled.implementation.program s ω)
        (fun _ => false)).projectedFormula pre) ∧
    (PrefixCNF.restrict (quantumCell rows C i
      ((K.forward (keyBits n r)).compiled.implementation.program s ω)
      (fun _ => false)).projectedFormula pre).length ≤
      18*rowIncidences rows+22*n+83*r+4*C.gates+4*K.gateBudget+53 ∧
    keySize n r + (quantumWitness rows i.1 + (quantumCell rows C i
      ((K.forward (keyBits n r)).compiled.implementation.program s ω) (fun _ => false)).aux) ≤
      21*r+8*n+4*rowIncidences rows+C.gates+K.gateBudget+12 := by
  exact transposed_quantum_query_size rows C (W.codingData (keyBits n r))
    (K.forward (keyBits n r)) i s ω pre

/-- No assumed separation, surjectivity or confidence field: both forward binary
encoders, their distances, a spectral graph, and exact SAT suffice. -/
theorem walk_coding_quantum_confidence {n r : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows))
    (C : Program r n) (W : WalkCode (keySize n r)) (K : W.Circuits)
    (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    1-δ ≤ (repeatedLaw (uniformLaw (Seed W.L (W.steps+1)))
      (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ)).prob
      (fun ω =>
        let T := prepare rows C (W.codingData (keyBits n r)).system.stages
          (K.forward (keyBits n r)).compiled.implementation.supplied solver (cellBudget (ε/3))
          (repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ) ω
        T.calls ≤ 2*(r+1)*(2*repetitionBudget (Fintype.card (Binary.CoefficientIndex r)) δ hδ+1)*
          (1+(keySize n r+1)*(1+2*keySize n r*(4*cellBudget (ε/3)+1))) ∧
        ∀ p ∈ Set.Icc (0 : ℝ) 1,
          RelPair ε (latentCurve (circuitMap C) (Binary.score (rowSpace rows)) p) (T.curve p) ∧
          0 ≤ T.curve p ∧ T.curve p ≤ 1) := by
  exact transposed_coding_quantum_confidence rows hS C (W.codingData (keyBits n r))
    (K.forward (keyBits n r)) solver hε hε1 hδ

end QecReliability.ExpanderWalk
