import QecReliability.AffineCircuits
import QecReliability.CachedEvaluator

/-! From supplied encoder/extractor DAGs and erasure-surjectivity to actual hash
circuits and the cached quantum confidence theorem. Size is parameterized, not assumed. -/
noncomputable section
namespace QecReliability.CodeHash
open SharedCircuit

structure Implementation {A : Type*} {m t q : ℕ} (D : System A m t q) (e : A ≃ BitModels q) where
  encoder : Program q (m * t)
  encoder_correct : ∀ a i j,
    boolBit (encoder.eval (e a) (finProdFinEquiv (i, j))) = D.encode a i j
  extractor : Program m q
  extractor_correct : ∀ a j,
    boolBit (extractor.eval a j) = D.extract (fun i => boolBit (a i)) j

def Implementation.full {A : Type*} {m t q : ℕ} {D : System A m t q} {e : A ≃ BitModels q}
    (K : Implementation D e) (s : Seed m t) : Program q q :=
  (K.encoder.compose (localAffine s)).compose K.extractor

theorem Implementation.full_correct {A : Type*} {m t q : ℕ} {D : System A m t q}
    {e : A ≃ BitModels q} (K : Implementation D e) (s : Seed m t) (a : A) (j : Fin q) :
    boolBit ((K.full s).eval (e a) j) = D.eval a s j := by
  simp only [Implementation.full, Program.compose_eval, K.extractor_correct]
  simp_rw [localAffine_correct, K.encoder_correct]
  rfl

def Implementation.program {A : Type*} {m t q : ℕ} {D : System A m t q}
    {e : A ≃ BitModels q} (K : Implementation D e) (r : Fin (q + 1)) (s : Seed m t) :
    Program q r.val :=
  (K.full s).compose (Program.pure (Fin.castLE (Nat.le_of_lt_succ r.isLt)))

theorem bitBool_boolBit (b : Bool) : Binary.bitBool (boolBit b) = b := by cases b <;> decide

def Implementation.supplied {A : Type*} {m t q : ℕ} {D : System A m t q}
    {e : A ≃ BitModels q} (K : Implementation D e) : SuppliedHashCircuits D.stages e where
  program := K.program
  correct r s a := by
    have he : (K.program r s).eval (e a) =
        wordBits r.val ((D.prefix (Nat.le_of_lt_succ r.isLt)).eval a s) := by
      funext i
      have h := congrArg Binary.bitBool (K.full_correct s a (Fin.castLE (Nat.le_of_lt_succ r.isLt) i))
      rw [bitBool_boolBit] at h
      simpa [Implementation.program, wordBits, System.prefix, System.eval, System.local, truncate] using h
    rw [he]
    rfl

theorem Implementation.program_gates {A : Type*} {m t q : ℕ} {D : System A m t q}
    {e : A ≃ BitModels q} (K : Implementation D e) (r : Fin (q + 1)) (s : Seed m t) :
    (K.program r s).gates ≤ K.encoder.gates + m * (t + 1) + K.extractor.gates := by
  change K.encoder.gates + (localAffine s).gates + K.extractor.gates + 0 ≤ _
  have h := localAffine_gates s
  omega

/-- Includes output sinks and primary input sources; intermediate program outputs
are wired references, not tree-expanded computations. -/
theorem Implementation.program_resources {A : Type*} {m t q : ℕ} {D : System A m t q}
    {e : A ≃ BitModels q} (K : Implementation D e) (r : Fin (q + 1)) (s : Seed m t) :
    q + (K.program r s).circuit.edges + r.val ≤
      2 * q + 2 * (K.encoder.gates + m * (t + 1) + K.extractor.gates) := by
  have hg := K.program_gates r s
  have he := (K.program r s).circuit.edges_le
  have hr := r.isLt
  omega

end QecReliability.CodeHash
