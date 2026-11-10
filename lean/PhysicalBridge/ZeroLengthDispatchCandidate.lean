import PhysicalBridge.LinearRepairEdges

/-!

Uses the existing declarations, not a final headline axiom.
The zero branch is on physical input n, before any counting/budget/factory call.
Generator rows are actual input and may contain arbitrarily many empty rows.
-/

namespace QecReliability.ZeroLengthDispatch
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput QecPhysical QecPhysical.Stabilizer

def iidProgram (n : ℕ) : Program n n := Program.pure id

@[simp] theorem iidProgram_map (n : ℕ) : circuitMap (iidProgram n) = id := by
  funext b
  simp [circuitMap, iidProgram, Program.pure_eval, Function.comp_def]

@[simp] theorem iidProgram_gates (n : ℕ) : (iidProgram n).gates = 0 := rfl

theorem zeroRow_eq_nil (row : List (PauliCoord 0)) : row = [] := by
  cases row with
  | nil => rfl
  | cons x xs =>
    cases x with
    | inl i => exact Fin.elim0 i
    | inr i => exact Fin.elim0 i

theorem zeroRows_incidences (rows : List (List (PauliCoord 0))) :
    rowIncidences rows = 0 := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simpa [rowIncidences, zeroRow_eq_nil row] using ih

theorem zeroErasure_eq_empty (E : Finset (Fin 0)) : E = ∅ := by
  ext i
  exact Fin.elim0 i

theorem zeroScore (rows : List (List (PauliCoord 0))) (E : Finset (Fin 0)) :
    score (rowSpace rows) E = 1 := by
  rw [zeroErasure_eq_empty E, score_empty]

def unitRatio : Ratio := ⟨1, 1, by omega, le_rfl⟩

def zeroVector : Vector 0 := Vector.build (fun _ => unitRatio)

@[simp] theorem unitRatio_value : unitRatio.value = 1 := by
  norm_num [unitRatio, Ratio.value]

@[simp] theorem zeroVector_pair (j : Fin 1) :
    ((zeroVector.get j).num, (zeroVector.get j).den) = (1, 1) := by
  simp [zeroVector, unitRatio]

@[simp] theorem zeroVector_size : zeroVector.entries.size = 1 :=
  zeroVector.length_eq

@[simp] theorem zeroVector_curve (p : ℝ) : zeroVector.curve p = 1 := by
  simp [Vector.curve, zeroVector, bernsteinCurve, average, bernsteinWeight]

/-- The existing rational evaluator itself has a degree-zero shortcut. There is
no division in this computation, and even invalid evaluation arguments are not
used. Interpretation of u/d as an input probability still requires d>0,u≤d. -/
@[simp] theorem zeroVector_evaluate (u d : ℕ) :
    zeroVector.evaluate u d = (1, 1) := by
  simp [Vector.evaluate, evaluateRationalCurve, zeroVector, unitRatio]

theorem zeroVector_antitone : Antitone zeroVector.curve := by
  intro p q hpq
  simp

theorem zeroVector_structure (rows : List (List (PauliCoord 0)))
    (C : Causes 0 → Finset (Fin 0)) :
    ShapeStructure (rowSpace rows) C zeroVector.curve := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    simp
  · simp [zeroScore]
  · simp [zeroScore]
  · intro p hp
    simp [zeroScore]

noncomputable section

theorem zeroLatentCurve (rows : List (List (PauliCoord 0)))
    (C : Causes 0 → Finset (Fin 0)) (p : ℝ) :
    latentCurve C (score (rowSpace rows)) p = 1 := by
  have hz : (default : Finset (Fin 0)) = ∅ := by
    ext i
    exact Fin.elim0 i
  simp [latentCurve, zeroScore, hz]

/-- The physical premise is exactly the source's Lift of the actual input row space.
No validity predicate, nonempty-row assumption, or n>0 premise is invented. -/
theorem zeroPhysicalFidelity (rows : List (List (PauliCoord 0)))
    (L : Lift (rowSpace rows)) (C : Causes 0 → Finset (Fin 0))
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure C p hp.1 hp.2)).map = 1 := by
  rw [L.physical_fidelity_eq_latentCurve C p hp.1 hp.2]
  exact zeroLatentCurve rows C p

theorem zeroPhysicalOptimum (rows : List (List (PauliCoord 0)))
    (L : Lift (rowSpace rows)) (C : Causes 0 → Finset (Fin 0))
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure C p hp.1 hp.2)).map = 1 ∧
    ∀ Q : Channel (ErasureFlagOutput 0) L.LogicalIndex,
      entanglementFidelity (Q.comp (L.iidLatentErasure C p hp.1 hp.2)).map ≤ 1 := by
  have he := zeroPhysicalFidelity rows L C p hp
  refine ⟨he, ?_⟩
  intro Q
  simpa only [he] using (L.cached_target_optimality C p hp).2 Q

theorem zeroPhysicalAccuracy (rows : List (List (PauliCoord 0)))
    (L : Lift (rowSpace rows)) (C : Causes 0 → Finset (Fin 0))
    (ε : ℝ) (hε : 0 ≤ ε) : L.PhysicalAccuracy C ε zeroVector.curve := by
  intro p hp
  rw [zeroPhysicalFidelity rows L C p hp, zeroVector_curve]
  exact relPair_refl hε (by norm_num) le_rfl

theorem zeroPhysicalTails (rows : List (List (PauliCoord 0)))
    (L : Lift (rowSpace rows)) (C : Causes 0 → Finset (Fin 0))
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    TailExact (entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure C p hp.1 hp.2)).map) (zeroVector.curve p) := by
  rw [zeroPhysicalFidelity rows L C p hp, zeroVector_curve]
  simp [TailExact]

/-- Comparison with the actual old prepared output is ONLY semantic. The new
stored pair is (1,1); no equality of unreduced old/new pairs is asserted. -/
theorem zeroVector_eq_prepared_curve {Ω : Type*} [Fintype Ω]
    (rows : List (List (PauliCoord 0))) (C : Program 0 0)
    (H : HashStages Ω (CoefficientKey 0 0) (keySize 0 0))
    (K : SuppliedHashCircuits H (keyBits 0 0)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget 2 c d+1) → Ω)
    (p : ℝ) :
    zeroVector.curve p =
      (LinearRepair.prepare true rows C H K solver a b c d ω).coefficients.curve p := by
  rw [LinearRepair.prepare_coefficients]
  simp only [↓reduceIte]
  rw [shapeVector_zero_latents, zeroScore, zeroVector_curve]

theorem zeroVector_eq_prepared_value {Ω : Type*} [Fintype Ω]
    (rows : List (List (PauliCoord 0))) (C : Program 0 0)
    (H : HashStages Ω (CoefficientKey 0 0) (keySize 0 0))
    (K : SuppliedHashCircuits H (keyBits 0 0)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (a b c d : ℕ) (ω : Fin (2*rationalRepetitionBudget 2 c d+1) → Ω)
    (j : Fin 1) :
    (zeroVector.get j).value =
      ((LinearRepair.prepare true rows C H K solver a b c d ω).coefficients.get j).value := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  have h := zeroVector_eq_prepared_curve rows C H K solver a b c d ω 0
  simp only [Vector.curve, bernsteinCurve_zero] at h
  exact h

end

/-- Positive-only seed families. The zero case contains no repetition budget. -/
def Seed (Ω : ℕ → Type) (c d : ℕ) : ℕ → Type
  | 0 => Unit
  | k+1 => Fin (2*rationalRepetitionBudget (2*((k+1)+1)) c d+1) → Ω k

instance seedFintype (Ω : ℕ → Type) [∀ k, Fintype (Ω k)]
    (c d n : ℕ) : Fintype (Seed Ω c d n) := by
  cases n <;> dsimp [Seed] <;> infer_instance

section Dispatcher
variable {Ω : ℕ → Type} [∀ k, Fintype (Ω k)]
    (H : ∀ k, HashStages (Ω k) (CoefficientKey (k+1) (k+1)) (keySize (k+1) (k+1)))
    (K : ∀ k, SuppliedHashCircuits (H k) (keyBits (k+1) (k+1)))
    (solver : ∀ v, PrefixCNF.ExactSAT v 3) (a b c d : ℕ)

/-- H and K are positive-indexed functions, not factory outputs computed at
n=0. Operational callers must keep factory/budget acquisition inside the succ
branch; merely selecting an empty hash after eager preparation is insufficient.
This wrapper intentionally exposes the same coefficient-vector API; it does
not manufacture a bogus raw-cache/report object for the zero branch. -/
def run : (n : ℕ) → List (List (PauliCoord n)) → Seed Ω c d n → Vector n
  | 0, _, _ => zeroVector
  | k+1, rows, ω =>
    (LinearRepair.prepare true rows (iidProgram (k+1)) (H k) (K k)
      solver a b c d ω).coefficients

@[simp] theorem run_zero (rows : List (List (PauliCoord 0))) (ω : Seed Ω c d 0) :
    run H K solver a b c d 0 rows ω = zeroVector := rfl

/-- Literal positive-branch equality: here, unlike zero vs old output, the
entire stored coefficient vector really is the same source value. -/
@[simp] theorem run_positive (k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (ω : Seed Ω c d (k+1)) :
    run H K solver a b c d (k+1) rows ω =
      (LinearRepair.prepare true rows (iidProgram (k+1)) (H k) (K k)
        solver a b c d ω).coefficients := rfl

end Dispatcher

noncomputable section

def unitLaw : FiniteProbability Unit where
  mass _ := 1
  nonneg _ := by norm_num
  total := by simp

theorem unitLaw_prob_all (P : Unit → Prop) (h : ∀ u, P u) : unitLaw.prob P = 1 := by
  classical
  simp [FiniteProbability.prob, FiniteProbability.expect, average, indicator, unitLaw, h]

theorem zeroPhysical_success_probability (rows : List (List (PauliCoord 0)))
    (L : Lift (rowSpace rows)) (C : Causes 0 → Finset (Fin 0))
    (ε : ℝ) (hε : 0 ≤ ε) :
    unitLaw.prob (fun _ => L.PhysicalAccuracy C ε zeroVector.curve) = 1 :=
  unitLaw_prob_all _ (fun _ => zeroPhysicalAccuracy rows L C ε hε)

section Confidence
variable {Ω : ℕ → Type} [∀ k, Fintype (Ω k)]
    (H : ∀ k, HashStages (Ω k) (CoefficientKey (k+1) (k+1)) (keySize (k+1) (k+1)))
    (K : ∀ k, SuppliedHashCircuits (H k) (keyBits (k+1) (k+1)))
    (solver : ∀ v, PrefixCNF.ExactSAT v 3) (a b c d : ℕ)

def law : (n : ℕ) → FiniteProbability (Seed Ω c d n)
  | 0 => unitLaw
  | k+1 => repeatedLaw (H k).law (rationalRepetitionBudget (2*((k+1)+1)) c d)

theorem iid_layers_antitone {n : ℕ} (rows : List (List (PauliCoord n)))
    (L : Lift (rowSpace rows)) :
    Antitone (layerAverage (circuitMap (iidProgram n)) (score (rowSpace rows))) := by
  apply latent_score_layers_antitone (rowSpace rows) L.isotropic
  intro E E' h
  simpa only [iidProgram_map, id_eq] using h

/-- Deterministic zero branch, existing source confidence in the positive branch.
The common event controls both fidelity and infidelity for all p at once.
Denominator positivity and the existing a≤b hypothesis are preserved.
The source does not need c≤d; adding it restricts to nonvacuous δ≤1. -/
theorem run_confidence (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (hab : a≤b)
    (n : ℕ) (rows : List (List (PauliCoord n))) (L : Lift (rowSpace rows)) :
    1-(c:ℝ)/d ≤ (law H c d n).prob (fun ω =>
      L.PhysicalAccuracy (circuitMap (iidProgram n)) ((a:ℝ)/b)
        (run H K solver a b c d n rows ω).curve) := by
  cases n with
  | zero =>
    change 1-(c:ℝ)/d ≤ unitLaw.prob (fun _ =>
      L.PhysicalAccuracy (circuitMap (iidProgram 0)) ((a:ℝ)/b) zeroVector.curve)
    rw [unitLaw_prob_all _ (fun _ => zeroPhysicalAccuracy rows L _ _
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))]
    exact sub_le_self _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  | succ k =>
    exact (QecPhysical.Stabilizer.Lift.linear_shape_confidence rows L (iidProgram (k+1))
        (H k) (K k) solver a b c d ha hb hc hd hab (iid_layers_antitone rows L)).2

/-- Structural properties are outside the confidence event and require no
epsilon/delta assumptions. The physical Lift supplies isotropy. -/
theorem run_structure (n : ℕ) (rows : List (List (PauliCoord n)))
    (L : Lift (rowSpace rows)) (ω : Seed Ω c d n) :
    ShapeStructure (rowSpace rows) (circuitMap (iidProgram n))
      (run H K solver a b c d n rows ω).curve := by
  cases n with
  | zero => exact zeroVector_structure rows _
  | succ k =>
    simp only [run, LinearRepair.prepare_coefficients, ↓reduceIte, shapeVector_curve]
    apply cachedShape_structural
    apply score_antitone (rowSpace rows) L.isotropic
    simp only [iidProgram_map, id_eq]
    exact Finset.empty_subset _

theorem run_tails (n : ℕ) (rows : List (List (PauliCoord n)))
    (L : Lift (rowSpace rows)) (ω : Seed Ω c d n)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    TailExact (entanglementFidelity (L.erasureFlagDecoder.comp
      (L.iidLatentErasure (circuitMap (iidProgram n)) p hp.1 hp.2)).map)
      ((run H K solver a b c d n rows ω).curve p) := by
  cases n with
  | zero => exact zeroPhysicalTails rows L _ p hp
  | succ k =>
    exact QecPhysical.Stabilizer.Lift.linear_shape_tails rows L (iidProgram (k+1))
      (H k) (K k) solver a b c d ω (iid_layers_antitone rows L) p hp

end Confidence
end

/-- Exact old cap: it is not zero at n=0, even with a zero-bit hash factory. -/
def genericCallCap (n B t : ℕ) : ℕ :=
  2*(n+1)*t*(1+(keySize n n+1)*(1+2*keySize n n*(4*B+1)))

@[simp] theorem genericCallCap_zero (B t : ℕ) : genericCallCap 0 B t = 4*t := by
  simp [genericCallCap, keySize] <;> omega

/-- This is the branchwise advertised cap, not a substitute for a tape-cost
refinement. Input validation and literal output writes must be charged apart. -/
def dispatchedCallCap (B t : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => genericCallCap (n+1) B t

@[simp] theorem dispatchedCallCap_zero (B t : ℕ) : dispatchedCallCap B t 0 = 0 := rfl

end QecReliability.ZeroLengthDispatch
