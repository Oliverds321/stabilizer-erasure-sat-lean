import QecReliability.CodeHashCircuits

/-! A nonvacuous reference instance: a dense affine matrix with independent offset.
Its circuit budget is quadratic. It does not establish the manuscript's linear-size family. -/
noncomputable section
namespace QecReliability.CodeHash
open SharedCircuit

theorem boolBit_injective : Function.Injective boolBit := by
  intro a b h
  simpa only [bitBool_boolBit] using congrArg Binary.bitBool h

def dense {A : Type*} {q : ℕ} (e : A ≃ BitModels q) : System A q q q where
  encode a _ j := boolBit (e a j)
  extract := LinearMap.id
  onto := Function.surjective_id
  separating x y hxy := by
    have h : (fun j => boolBit (e x j)) ≠ (fun j => boolBit (e y j)) := by
      intro he
      apply hxy
      apply e.injective
      funext j
      exact boolBit_injective (congrFun he j)
    intro a
    refine ⟨a, ?_⟩
    ext i
    simp [mask, h]

def denseImplementation {A : Type*} {q : ℕ} (e : A ≃ BitModels q) :
    Implementation (dense e) e where
  encoder := Program.pure (fun i => (finProdFinEquiv.symm i).2)
  encoder_correct a i j := by
    change boolBit (e a (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = boolBit (e a j)
    rw [Equiv.symm_apply_apply]
  extractor := Program.pure id
  extractor_correct a j := rfl

theorem dense_program_gates {A : Type*} {q : ℕ} (e : A ≃ BitModels q)
    (r : Fin (q + 1)) (s : Seed q q) :
    ((denseImplementation e).program r s).gates ≤ q * (q + 1) := by
  simpa [denseImplementation, Program.pure] using (denseImplementation e).program_gates r s

theorem dense_program_resources {A : Type*} {q : ℕ} (e : A ≃ BitModels q)
    (r : Fin (q + 1)) (s : Seed q q) :
    q + ((denseImplementation e).program r s).circuit.edges + r.val ≤
      2 * q + 2 * (q * (q + 1)) := by
  simpa [denseImplementation, Program.pure] using (denseImplementation e).program_resources r s

end QecReliability.CodeHash
