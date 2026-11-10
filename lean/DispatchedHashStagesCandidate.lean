import ZeroDispatchCandidate

/-!
Closes the missing hash-law/program pairing for the existing
all-length dispatcher. Positive lengths use the unchanged CodeHash system and
fixed-seed compiler. Length zero uses Unit, one trivial hash cell, and the same
empty zero-gate Program already returned by dispatchedProgram.
This generic reusable bridge is instantiated with actual data in the next file.
-/
set_option autoImplicit false
noncomputable section
namespace QecReliability.UniformAdapter
open CodeHash SharedCircuit ExpanderWalk

/-- The zero-dimensional input domain is a singleton; no seed is sampled. -/
def emptyStages : HashStages Unit (BitModels 0) 0 where
  law := uniformLaw Unit
  hash r _ _ := zeroCell r.val
  uniform r a c := by
    have hr : r = 0 := Fin.ext (by have h := r.isLt; omega)
    subst r
    have hc : c = zeroCell 0 := Fin.ext (by have h := c.isLt; norm_num at h ⊢ <;> omega)
    subst c
    simp
  pairwise r a b hab c d := False.elim (hab (Subsingleton.elim _ _))

namespace DyadicXorData

instance dispatchedSeedNonempty (X : DyadicXorData) (hb : 8 ≤ X.base)
    (G : MGGInput) (q : Nat) : Nonempty (X.dispatchedSeed hb G q) := by
  cases q <;> dsimp [dispatchedSeed] <;> infer_instance

/-- The law belongs to exactly the seed type dispatched by the programs. -/
def dispatchedStages (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) :
    (q : Nat) → HashStages (X.dispatchedSeed hb G q) (BitModels q) q
  | 0 => emptyStages
  | q + 1 => ((X.walkCode hb G (q + 1)).codingData (Equiv.refl (BitModels (q + 1)))).system.stages

@[simp] theorem dispatchedStages_law (X : DyadicXorData) (hb : 8 ≤ X.base)
    (G : MGGInput) (q : Nat) :
    (X.dispatchedStages hb G q).law = uniformLaw (X.dispatchedSeed hb G q) := by
  cases q <;> rfl

/-- This program field is LITERALLY the old dispatcher; no semantic substitute
or unused q=0 evaluator is introduced. -/
def dispatchedCircuits (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : Nat) :
    SuppliedHashCircuits (X.dispatchedStages hb G q) (Equiv.refl (BitModels q)) where
  program := X.dispatchedProgram hb G q
  correct r seed a := by
    cases q with
    | zero =>
      have hr : r = 0 := Fin.ext (by have h := r.isLt; omega)
      subst r
      simp [dispatchedProgram, emptyEvaluator, Program.outputCast, Program.pure,
        Program.eval, Circuit.run, wordValue, dispatchedStages, emptyStages, zeroCell]
    | succ q =>
      exact ((X.walkCircuits hb G (q + 1)).forward
        (Equiv.refl (BitModels (q + 1)))).compiled.implementation.supplied.correct r seed a

@[simp] theorem dispatchedCircuits_program (X : DyadicXorData) (hb : 8 ≤ X.base)
    (G : MGGInput) (q : Nat) (r : Fin (q + 1)) (seed : X.dispatchedSeed hb G q) :
    (X.dispatchedCircuits hb G q).program r seed = X.dispatchedProgram hb G q r seed := rfl

/-- Uniformity is derived for the *dispatched* interface, including q=0. -/
theorem dispatched_uniform (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q : Nat) (r : Fin (q + 1)) (a : BitModels q) (c : Fin (2 ^ r.val)) :
    (uniformLaw (X.dispatchedSeed hb G q)).prob
      (fun seed => (X.dispatchedStages hb G q).hash r seed a = c) = 1 / (2 : Real) ^ r.val := by
  rw [← X.dispatchedStages_law hb G q]
  exact (X.dispatchedStages hb G q).uniform r a c

theorem dispatched_pairwise (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput)
    (q : Nat) (r : Fin (q + 1)) (a b : BitModels q) (hab : a ≠ b)
    (c d : Fin (2 ^ r.val)) :
    (uniformLaw (X.dispatchedSeed hb G q)).prob
      (fun seed => (X.dispatchedStages hb G q).hash r seed a = c ∧
        (X.dispatchedStages hb G q).hash r seed b = d) = (1 / (2 : Real) ^ r.val) ^ 2 := by
  rw [← X.dispatchedStages_law hb G q]
  exact (X.dispatchedStages hb G q).pairwise r a b hab c d

end DyadicXorData

/-- Re-index the concrete bit input domain to the quantum key equivalence.
This changes neither seed space/law nor the emitted circuit program. -/
def stagesOn {Ω B : Type} [Fintype Ω] {q : Nat}
    (H : HashStages Ω (BitModels q) q) (e : B ≃ BitModels q) : HashStages Ω B q where
  law := H.law
  hash r seed a := H.hash r seed (e a)
  uniform r a c := H.uniform r (e a) c
  pairwise r a b hab c d := H.pairwise r (e a) (e b) (fun he => hab (e.injective he)) c d

def circuitsOn {Ω B : Type} [Fintype Ω] {q : Nat}
    {H : HashStages Ω (BitModels q) q}
    (K : SuppliedHashCircuits H (Equiv.refl (BitModels q))) (e : B ≃ BitModels q) :
    SuppliedHashCircuits (stagesOn H e) e where
  program := K.program
  correct r seed a := K.correct r seed (e a)

@[simp] theorem circuitsOn_program {Ω B : Type} [Fintype Ω] {q : Nat}
    {H : HashStages Ω (BitModels q) q}
    (K : SuppliedHashCircuits H (Equiv.refl (BitModels q))) (e : B ≃ BitModels q)
    (r : Fin (q + 1)) (seed : Ω) : (circuitsOn K e).program r seed = K.program r seed := rfl

end QecReliability.UniformAdapter
