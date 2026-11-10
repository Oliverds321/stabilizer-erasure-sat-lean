import UniformWalkFactoryCandidate

/-! Explicit zero-case dispatch; no empty WalkCode fiction. -/
namespace QecReliability.UniformAdapter
open CodeHash SharedCircuit ExpanderWalk
namespace DyadicXorData

/-- Zero input length uses the singleton seed space and no random bits. -/
def dispatchedSeed (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) : ℕ → Type
  | 0 => Unit
  | q+1 => Seed (X.walkCode hb G (q+1)).L ((X.walkCode hb G (q+1)).steps+1)

noncomputable instance dispatchedSeedFintype (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    Fintype (X.dispatchedSeed hb G q) := by
  cases q <;> dsimp [dispatchedSeed] <;> infer_instance

noncomputable def dispatchedSeedBits (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) : ℕ → ℕ
  | 0 => 0
  | q+1 => (X.walkCode hb G (q+1)).L*((X.walkCode hb G (q+1)).steps+2)

/-- The positive branch is literally the existing compiled fixed-seed program. -/
noncomputable def dispatchedProgram (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) :
    (q : ℕ) → (r : Fin (q+1)) → X.dispatchedSeed hb G q → Program q r.val
  | 0, r, _ => emptyEvaluator.outputCast (by have hr := r.isLt; omega)
  | q+1, r, seed => X.hashProgram hb G (q+1) r seed

@[simp] theorem dispatchedProgram_positive (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q : ℕ) (r : Fin ((q+1)+1)) (seed : X.dispatchedSeed hb G (q+1)) :
    X.dispatchedProgram hb G (q+1) r seed = X.hashProgram hb G (q+1) r seed := rfl

@[simp] theorem dispatchedProgram_zero_gates (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (r : Fin (0+1)) (seed : X.dispatchedSeed hb G 0) :
    (X.dispatchedProgram hb G 0 r seed).gates = 0 := rfl

theorem dispatchedSeed_card (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    Fintype.card (X.dispatchedSeed hb G q) = 2^X.dispatchedSeedBits hb G q := by
  cases q with
  | zero => simp [dispatchedSeed, dispatchedSeedBits]
  | succ q =>
    change Fintype.card (Seed (X.walkCode hb G (q+1)).L
      ((X.walkCode hb G (q+1)).steps+1)) = _
    rw [seed_card]
    simp only [dispatchedSeedBits, Nat.add_assoc]

theorem dispatchedSeedBits_bound (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    X.dispatchedSeedBits hb G q ≤ X.Cseed*q := by
  cases q with
  | zero => simp [dispatchedSeedBits]
  | succ q => exact X.seed_positive hb G (q+1) (by omega)

theorem dispatchedProgram_gates (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q : ℕ) (r : Fin (q+1)) (seed : X.dispatchedSeed hb G q) :
    (X.dispatchedProgram hb G q r seed).gates ≤ X.Cfixed*q := by
  cases q with
  | zero => simp only [dispatchedProgram_zero_gates, Nat.mul_zero, le_refl]
  | succ q =>
    exact (X.hashProgram_gates hb G (q+1) r seed).trans
      (X.gates_positive hb G (q+1) (by omega))

/-- Counts every gate-input occurrence, every final-output edge, and every final
output sink node, including duplicate references as separate edges. -/
theorem dispatchedProgram_resources (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q : ℕ) (r : Fin (q+1)) (seed : X.dispatchedSeed hb G q) :
    X.dispatchedSeedBits hb G q + q + (X.dispatchedProgram hb G q r seed).gates +
      (X.dispatchedProgram hb G q r seed).circuit.edges + 2*r.val ≤ X.Cwire*q := by
  cases q with
  | zero =>
    have hr : r.val = 0 := by have hh := r.isLt; omega
    simp [dispatchedSeedBits, dispatchedProgram, emptyEvaluator, Program.outputCast,
      Program.pure, Circuit.edges, hr]
  | succ q =>
    exact X.hashProgram_resources_scaled hb G (q+1) (q+1) (by omega) le_rfl r seed

end DyadicXorData
end QecReliability.UniformAdapter
