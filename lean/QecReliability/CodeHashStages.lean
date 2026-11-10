import QecReliability.CodeCore
import QecReliability.CodeHash
import QecReliability.ConcreteQuantumConfidence

/-! Binary output encoding, truncation, and instantiation of all hash stages. -/
namespace QecReliability
namespace SharedCircuit

theorem wordValue_lt {k : ℕ} (a : BitModels k) : wordValue a < 2 ^ k := by
  induction k with
  | zero => simp [wordValue]
  | succ k ih =>
    have he : a = Fin.cons (a 0) (fun i => a i.succ) := by funext i; exact (Fin.cases rfl (fun _ => rfl) i)
    rw [he, wordValue_cons, pow_succ]
    have h := ih (fun i => a i.succ)
    cases a 0 <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

def wordFin (k : ℕ) : BitModels k ≃ Fin (2 ^ k) where
  toFun a := ⟨wordValue a, wordValue_lt a⟩
  invFun j := targetBits k j.val
  left_inv a := wordValue_injective k (by exact targetBits_value k (wordValue a) (wordValue_lt a))
  right_inv j := Fin.ext (targetBits_value k j.val j.isLt)

end SharedCircuit
namespace CodeHash
noncomputable section

def wordBits (k : ℕ) : Word k ≃ BitModels k := Equiv.piCongrRight (fun _ => Binary.bitBool)
def wordCell (k : ℕ) : Word k ≃ Fin (2 ^ k) := (wordBits k).trans (SharedCircuit.wordFin k)


theorem truncate_surjective {q r : ℕ} (h : r ≤ q) : Function.Surjective (truncate h) := by
  intro a
  refine ⟨fun i => if hi : i.val < r then a ⟨i.val, hi⟩ else 0, ?_⟩
  ext i
  simp [truncate, i.isLt]

def System.prefix {A : Type*} {m t q r : ℕ} (D : System A m t q) (h : r ≤ q) :
    System A m t r where
  encode := D.encode
  extract := (truncate h).comp D.extract
  onto := (truncate_surjective h).comp D.onto
  separating x y hxy := (truncate_surjective h).comp (D.separating x y hxy)

def System.stages {A : Type*} {m t q : ℕ} (D : System A m t q) :
    HashStages (Seed m t) A q where
  law := uniformLaw (Seed m t)
  hash r s a := wordCell r.val ((D.prefix (Nat.le_of_lt_succ r.isLt)).eval a s)
  uniform r a c := by
    have he : (fun s => wordCell r.val ((D.prefix (Nat.le_of_lt_succ r.isLt)).eval a s) = c) =
        (fun s => (D.prefix (Nat.le_of_lt_succ r.isLt)).eval a s = (wordCell r.val).symm c) := by
      funext s
      exact propext (Equiv.apply_eq_iff_eq_symm_apply _)
    rw [he]
    exact (D.prefix _).uniform _ _
  pairwise r a b hab c d := by
    have he : (fun s => wordCell r.val ((D.prefix (Nat.le_of_lt_succ r.isLt)).eval a s) = c ∧
        wordCell r.val ((D.prefix (Nat.le_of_lt_succ r.isLt)).eval b s) = d) =
        (fun s => (D.prefix (Nat.le_of_lt_succ r.isLt)).eval a s = (wordCell r.val).symm c ∧
          (D.prefix (Nat.le_of_lt_succ r.isLt)).eval b s = (wordCell r.val).symm d) := by
      funext s
      simp only [Equiv.apply_eq_iff_eq_symm_apply]
    rw [he]
    exact (D.prefix _).pairwise hab _ _

end
end CodeHash
end QecReliability
