import LatentFactorySeeds
import QecReliability.TensorCountingConfidence

/-! The existing all-length hash factory on the multiclass cause/Pauli key.
Class grouping changes the key equivalence, not its bit length, hash circuit,
seed extent, or runtime random-word slicing. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.Factory
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

abbrev length (n : ℕ) (ds : List ℕ) := LatentMachine.Factory.length hD hd A n ds.sum
abbrev width (n : ℕ) (ds : List ℕ) := LatentMachine.Factory.width hD hd A n ds.sum

def system (n : ℕ) (ds : List ℕ) : CodeHash.System (TensorCoefficientCounting.Key n ds)
    (length hD hd A n ds) (width hD hd A n ds) (keySize n ds.sum) :=
  ((LatentMachine.Factory.walk hD hd A n ds.sum).codingData
    (TensorCoefficientCounting.keyBits n ds)).system

def circuits (n : ℕ) (ds : List ℕ) :
    SuppliedHashCircuits (system hD hd A n ds).stages
      (TensorCoefficientCounting.keyBits n ds) :=
  (((data hD hd A).walkCircuits (base_ge_eight hD hd A) actualMGG
    (keySize n ds.sum)).forward (TensorCoefficientCounting.keyBits n ds)).compiled.implementation.supplied

theorem seed_length (n : ℕ) (ds : List ℕ) :
    Trans.Wire.seedB (data hD hd A).base (data hD hd A).den (keySize n ds.sum) =
      CodeHash.seedBits (length hD hd A n ds) (width hD hd A n ds) :=
  LatentMachine.Factory.seed_length hD hd A n ds.sum

theorem hash_program (n : ℕ) (ds : List ℕ) (scale : Fin (keySize n ds.sum+1))
    (bits : List Bool)
    (hbits : bits.length = CodeHash.seedBits (length hD hd A n ds) (width hD hd A n ds)) :
    Trans.Query.encProg ((circuits hD hd A n ds).program scale
      (Trans.Hash.seedOfBits (length hD hd A n ds) (width hD hd A n ds) bits)) =
      Trans.Hash.hashPlain (data hD hd A).base (data hD hd A).den (keySize n ds.sum)
        (fun ell => Trans.Query.encProg ((data hD hd A).program ell))
        (Trans.Hash.gNbr actualMGG) scale.val bits :=
  Trans.Hash.encProg_hashProgram (data hD hd A) (base_ge_eight hD hd A)
    actualMGG _ _ scale bits hbits

end QecReliability.TensorMachine.Factory
