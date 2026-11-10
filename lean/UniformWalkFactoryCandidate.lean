import EffectiveSelectorsCandidate
import DyadicEncoderDataCandidate

/-!


Conditional semantic/circuit adapter from encoder family data and graph family
data. Intended instantiations are one fixed certified encoder generator and the
actual concrete MGG construction. Uniformity/no-advice require their separate
realizations; these bare family-valued input structures do not enforce them.
No symbol separation, hash law, transpose, or final factory budget is assumed.
This file does NOT prove a generator runtime or an unconditional SAT-only result.
-/
namespace QecReliability.UniformAdapter
open CodeHash SharedCircuit ExpanderWalk

/-- Thin input boundary for the actual MGG construction. Not an existential graph search. -/
structure MGGInput where
  graph : (s : ℕ) → 3 ≤ s → PortGraph (s*s) 16
  gap : ∀ s hs, (graph s hs).PositiveGap (1/32)

namespace DyadicXorData

def firstIndex (X : DyadicXorData) (q : ℕ) : ℕ := dyadicUp X.base (4*q)
def firstLength (X : DyadicXorData) (q : ℕ) : ℕ := dyadicValue X.base (4*q)
def side (X : DyadicXorData) (q : ℕ) : ℕ := ceilSquare (X.firstLength q)
def order (X : DyadicXorData) (q : ℕ) : ℕ := X.side q * X.side q
def steps (X : DyadicXorData) : ℕ := walkClock X.den
def walkCount (X : DyadicXorData) (q : ℕ) : ℕ := X.order q * 16^X.steps
def secondIndex (X : DyadicXorData) (q : ℕ) : ℕ := dyadicUp X.base (X.walkCount q)
def secondLength (X : DyadicXorData) (q : ℕ) : ℕ := dyadicValue X.base (X.walkCount q)

theorem firstLength_eq (X : DyadicXorData) (q : ℕ) :
    X.firstLength q = dyadicLength X.base (4*q) X.base_pos :=
  dyadicValue_eq_length _ _ _

theorem firstLength_ge_base (X : DyadicXorData) (q : ℕ) : X.base ≤ X.firstLength q := by
  rw [firstLength_eq]
  exact dyadicLength_ge_base _ _ _

theorem firstLength_pos (X : DyadicXorData) (q : ℕ) : 0 < X.firstLength q :=
  X.base_pos.trans_le (X.firstLength_ge_base q)

theorem first_capacity (X : DyadicXorData) (q : ℕ) : q ≤ X.firstLength q / 4 := by
  rw [firstLength_eq]
  exact (initial_padding_capacity X.base q X.base_pos).1

theorem order_lower (X : DyadicXorData) (q : ℕ) : X.firstLength q ≤ X.order q :=
  ceilSquare_lower _ (X.firstLength_pos q)

theorem order_upper (X : DyadicXorData) (q : ℕ) : X.order q ≤ 2*X.firstLength q :=
  ceilSquare_upper _ (X.firstLength_pos q)

theorem side_ge_three (X : DyadicXorData) (hb : 8 ≤ X.base) (q : ℕ) : 3 ≤ X.side q :=
  ceilSquare_ge_three _ (hb.trans (X.firstLength_ge_base q))

/-- First supplied encoder, with the SAME one-zero gate for input/output padding. -/
def binaryProgram (X : DyadicXorData) (q : ℕ) : Program q (X.order q) :=
  padInputsAndOutputs (X.program (X.firstIndex q)) q (X.order q) (X.order_lower q)

noncomputable def binaryMap (X : DyadicXorData) (q : ℕ) : Word q →ₗ[F] Word (X.order q) :=
  padEncoderTo (X.encoder (X.firstIndex q)) (X.first_capacity q) (X.order_lower q)

theorem binaryProgram_correct (X : DyadicXorData) (q : ℕ) (x : BitModels q) (i : Fin (X.order q)) :
    boolBit ((X.binaryProgram q).eval x i) = X.binaryMap q (bitsVector x) i :=
  padEncoderTo_correct _ _ (X.correct (X.firstIndex q)) _ _ x i

theorem binaryMap_distance (X : DyadicXorData) (q : ℕ) (x : Word q) (hx : x ≠ 0) :
    (X.alpha/2)*X.order q ≤ (weight (X.binaryMap q x) : ℝ) := by
  have hE : ∀ y, y ≠ 0 → X.alpha*(X.firstLength q:ℝ) ≤
      (weight (X.encoder (X.firstIndex q) y) : ℝ) := by
    intro y hy
    simpa only [alpha, firstLength, dyadicValue, firstIndex,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using X.distance (X.firstIndex q) y hy
  exact padEncoderTo_distance _ (le_of_lt X.alpha_pos) hE
    _ _ (X.order_upper q) x hx

theorem binaryProgram_gates (X : DyadicXorData) (q : ℕ) :
    (X.binaryProgram q).gates ≤ 1 + X.gateConstant * X.firstLength q := by
  change 1 + (X.program (X.firstIndex q)).gates ≤ _
  exact Nat.add_le_add_left (X.gates_le (X.firstIndex q)) 1

/-- The second generator call uses the EXECUTABLE dyadic index. -/
def selectedProgram (X : DyadicXorData) (target : ℕ) :
    Program (dyadicLength X.base target X.base_pos / 4) (dyadicLength X.base target X.base_pos) :=
  castProgram (X.program (dyadicUp X.base target))
    (congrArg (fun n => n/4) (dyadicValue_eq_length X.base target X.base_pos))
    (dyadicValue_eq_length X.base target X.base_pos)

/-- Refinement to the exact unchanged selector. -/
theorem selectedProgram_eq (X : DyadicXorData) (target : ℕ) :
    X.selectedProgram target = X.program (dyadicIndex X.base target X.base_pos) := by
  have transport (i j : Nat) (hij : i = j)
      (ha : X.base * 2 ^ i / 4 = X.base * 2 ^ j / 4)
      (hb : X.base * 2 ^ i = X.base * 2 ^ j) :
      castProgram (X.program i) ha hb = X.program j := by
    cases hij
    rfl
  exact transport _ _ (dyadicUp_eq_index X.base target X.base_pos) _ _

noncomputable def walkCode (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    WalkCode q :=
  WalkCode.fromDyadic X.toFamily X.alpha_le_one
    (G.graph (X.side q) (X.side_ge_three hb q)) (G.gap _ _)
    (X.binaryMap q) (X.binaryMap_distance q)
    (by
      change dyadicLength X.base (4 * q) X.base_pos ≤ X.side q * X.side q
      rw [← X.firstLength_eq q]
      exact X.order_lower q)
    X.steps (rational_fixed_walk_small X.num X.den X.num_pos X.num_le_den)

/-- Both forward programs are explicitly assembled. The existing forward/compiled
methods then construct symbol-reference wiring, local affine hashing and transpose. -/
noncomputable def walkCircuits (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    (X.walkCode hb G q).Circuits where
  binary := X.binaryProgram q
  binary_correct := X.binaryProgram_correct q
  code := X.selectedProgram (X.walkCount q)
  code_xor := by
    rw [selectedProgram_eq]
    exact X.xorOnly _
  code_correct := by
    rw [selectedProgram_eq]
    exact X.correct _

@[simp] theorem walkCode_degree (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    (X.walkCode hb G q).d = 16 := rfl

@[simp] theorem walkCode_steps (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    (X.walkCode hb G q).steps = 256*X.den^2 := rfl

@[simp] theorem walkCode_order (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    (X.walkCode hb G q).m = X.order q := rfl

theorem walkCode_length (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    (X.walkCode hb G q).L = X.secondLength q :=
  (dyadicValue_eq_length _ _ _).symm

theorem code_gates (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    (X.walkCircuits hb G q).code.gates ≤ X.gateConstant*(X.walkCode hb G q).L := by
  change (X.selectedProgram (X.walkCount q)).gates ≤
    X.gateConstant*dyadicLength X.base (X.walkCount q) X.base_pos
  rw [selectedProgram_eq]
  exact X.gates_le _

/-- Global constants: none depends on q, r, confidence parameters, or seed values. -/
def A (X : DyadicXorData) : ℕ := max X.base 8
def B (X : DyadicXorData) : ℕ := 4*X.A*16^X.steps
def Cseed (X : DyadicXorData) : ℕ := X.B*(X.steps+2)
def Cfixed (X : DyadicXorData) : ℕ :=
  X.gateConstant*X.A + X.B*(X.steps+3+2*X.gateConstant) + 2
/-- Data inputs + gates + gate-input edges + final output edges + output sink nodes,
with optional storage
of the sampled seed bits. This is NOT a bounded-fan-out-two claim. -/
def Cwire (X : DyadicXorData) : ℕ := X.Cseed + 3*X.Cfixed + 3

/-- A single scale lemma yields BOTH q+1 bounds and sharper positive-q bounds. -/
theorem firstLength_scaled (X : DyadicXorData) (q s : ℕ) (hs : 1 ≤ s) (hqs : q ≤ s) :
    X.firstLength q ≤ X.A*s := by
  have hh : X.firstLength q ≤ max X.base (8*q) := by
    rw [X.firstLength_eq q]
    exact (initial_padding_capacity X.base q X.base_pos).2
  apply hh.trans
  apply max_le
  · calc
      X.base ≤ X.A := le_max_left _ _
      _ ≤ X.A*s := by simpa using Nat.mul_le_mul_left X.A hs
  · calc
      8*q ≤ 8*s := Nat.mul_le_mul_left 8 hqs
      _ ≤ X.A*s := Nat.mul_le_mul_right s (le_max_right _ _)

theorem length_scaled (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q s : ℕ) (hs : 1 ≤ s) (hqs : q ≤ s) :
    (X.walkCode hb G q).L ≤ X.B*s := by
  have hm : X.order q ≤ 2*(X.A*s) :=
    (X.order_upper q).trans (Nat.mul_le_mul_left 2 (X.firstLength_scaled q s hs hqs))
  have hL := (X.walkCode hb G q).length_le
  change (X.walkCode hb G q).L ≤ 2*(X.order q * 16^X.steps) at hL
  calc
    _ ≤ 2*(X.order q * 16^X.steps) := hL
    _ ≤ 2*((2*(X.A*s))*16^X.steps) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hm)
    _ = X.B*s := by unfold B; ring

theorem seed_scaled (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q s : ℕ) (hs : 1 ≤ s) (hqs : q ≤ s) :
    (X.walkCode hb G q).L*((X.walkCode hb G q).steps+2) ≤ X.Cseed*s := by
  have hh := Nat.mul_le_mul_right (X.steps+2) (X.length_scaled hb G q s hs hqs)
  change (X.walkCode hb G q).L*(X.steps+2) ≤ _
  calc
    _ ≤ (X.B*s)*(X.steps+2) := hh
    _ = X.Cseed*s := by unfold Cseed; ring

theorem gates_scaled (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q s : ℕ) (hs : 1 ≤ s) (hqs : q ≤ s) :
    (X.walkCircuits hb G q).gateBudget ≤ X.Cfixed*s := by
  have hN := X.firstLength_scaled q s hs hqs
  have hB := X.binaryProgram_gates q
  have hC := X.code_gates hb G q
  have hL := X.length_scaled hb G q s hs hqs
  have hNu := Nat.mul_le_mul_left X.gateConstant hN
  have hLbig := Nat.mul_le_mul_right (X.steps+3+2*X.gateConstant) hL
  change (X.binaryProgram q).gates +
    (X.walkCode hb G q).L*(X.steps+2) +
    (1+(X.walkCode hb G q).L+2*(X.walkCircuits hb G q).code.gates) ≤ _
  unfold Cfixed
  nlinarith

theorem seed_all_lengths (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    (X.walkCode hb G q).L*((X.walkCode hb G q).steps+2) ≤ X.Cseed*(q+1) :=
  X.seed_scaled hb G q (q+1) (by omega) (by omega)

theorem gates_all_lengths (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    (X.walkCircuits hb G q).gateBudget ≤ X.Cfixed*(q+1) :=
  X.gates_scaled hb G q (q+1) (by omega) (by omega)

theorem seed_positive (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q : ℕ) (hq : 0 < q) :
    (X.walkCode hb G q).L*((X.walkCode hb G q).steps+2) ≤ X.Cseed*q :=
  X.seed_scaled hb G q q hq le_rfl

theorem gates_positive (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q : ℕ) (hq : 0 < q) :
    (X.walkCircuits hb G q).gateBudget ≤ X.Cfixed*q :=
  X.gates_scaled hb G q q hq le_rfl

/-- Explicit endpoint for the existing fixed-seed compiler. Every repeated symbol
position has its own seed coordinate in the unchanged `Seed L (steps+1)` type. -/
noncomputable def hashProgram (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q : ℕ) (r : Fin (q+1))
    (seed : Seed (X.walkCode hb G q).L ((X.walkCode hb G q).steps+1)) : Program q r.val :=
  ((X.walkCircuits hb G q).forward (Equiv.refl (BitModels q))).compiled.implementation.program r seed

theorem hashProgram_gates (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q : ℕ) (r : Fin (q+1))
    (seed : Seed (X.walkCode hb G q).L ((X.walkCode hb G q).steps+1)) :
    (X.hashProgram hb G q r seed).gates ≤ (X.walkCircuits hb G q).gateBudget := by
  exact ((X.walkCircuits hb G q).forward (Equiv.refl (BitModels q))).hash_gates r seed

theorem hashProgram_resources_scaled (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q s : ℕ) (hs : 1 ≤ s) (hqs : q ≤ s) (r : Fin (q+1))
    (seed : Seed (X.walkCode hb G q).L ((X.walkCode hb G q).steps+1)) :
    (X.walkCode hb G q).L*((X.walkCode hb G q).steps+2) + q +
      (X.hashProgram hb G q r seed).gates + (X.hashProgram hb G q r seed).circuit.edges + 2*r.val ≤
      X.Cwire*s := by
  have hR := X.seed_scaled hb G q s hs hqs
  have hP := (X.hashProgram_gates hb G q r seed).trans (X.gates_scaled hb G q s hs hqs)
  have hE := (X.hashProgram hb G q r seed).circuit.edges_le
  have hr : r.val ≤ q := Nat.le_of_lt_succ r.isLt
  unfold Cwire
  nlinarith

end DyadicXorData

/-- Public unnormalized entrypoints always perform the base shift once. -/
noncomputable def buildWalkCode (F : DyadicXorData) (G : MGGInput) (q : ℕ) : WalkCode q :=
  F.shift.walkCode F.shift_base_ge_eight G q

noncomputable def buildWalkCircuits (F : DyadicXorData) (G : MGGInput) (q : ℕ) :
    (buildWalkCode F G q).Circuits :=
  F.shift.walkCircuits F.shift_base_ge_eight G q

/-- Zero-length evaluators can be genuinely empty, separately from WalkCode. -/
def emptyEvaluator : Program 0 0 := Program.pure Fin.elim0

@[simp] theorem emptyEvaluator_gates : emptyEvaluator.gates = 0 := rfl

/-- The positive-order WalkCode compiler CANNOT obey C*q at q=0.
This is why its all-length theorem has q+1, not an unstated q>0 hypothesis. -/
theorem zero_walk_budget_not_linear (W : WalkCode 0) (K : W.Circuits) (C : ℕ) :
    ¬ K.gateBudget ≤ C*0 := by
  unfold WalkCode.Circuits.gateBudget
  omega

end QecReliability.UniformAdapter
