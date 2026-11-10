import LatentMachineCoins
import Trans.Wire.Agree

/-! Runtime latent dimensions for the actual one-certificate all-length hash
factory. This connects the stored decoder's exact tuple to the slices consumed
by the installed hash wrapper; no iid dimension or replacement distribution. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Factory
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost.StoredCodeHashConfidence CodeHash.FiniteRandomTape

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

def walk (n r : ℕ) :=
  (data hD hd A).walkCode (base_ge_eight hD hd A) actualMGG (keySize n r)
def length (n r : ℕ) : ℕ := (walk hD hd A n r).L
def width (n r : ℕ) : ℕ := (walk hD hd A n r).steps+1

def system (n r : ℕ) : CodeHash.System (Binary.CoefficientKey n r)
    (length hD hd A n r) (width hD hd A n r) (keySize n r) :=
  ((walk hD hd A n r).codingData (keyBits n r)).system

def circuits (n r : ℕ) : SuppliedHashCircuits (actualCodeHash (system hD hd A n r)) (keyBits n r) :=
  (((data hD hd A).walkCircuits (base_ge_eight hD hd A) actualMGG
    (keySize n r)).forward (keyBits n r)).compiled.implementation.supplied

theorem seed_length (n r : ℕ) :
    Trans.Wire.seedB (data hD hd A).base (data hD hd A).den (keySize n r) =
      CodeHash.seedBits (length hD hd A n r) (width hD hd A n r) :=
  Trans.Wire.seedB_walk (data hD hd A) (base_ge_eight hD hd A) actualMGG _

theorem hash_program (n r : ℕ) (scale : Fin (keySize n r+1)) (bits : List Bool)
    (hbits : bits.length = CodeHash.seedBits (length hD hd A n r) (width hD hd A n r)) :
    Trans.Query.encProg ((QecReliability.LatentMachine.Factory.circuits hD hd A n r).program scale
      (Trans.Hash.seedOfBits (length hD hd A n r) (width hD hd A n r) bits)) =
      Trans.Hash.hashPlain (data hD hd A).base (data hD hd A).den (keySize n r)
        (fun ell => Trans.Query.encProg ((data hD hd A).program ell))
        (Trans.Hash.gNbr actualMGG) scale.val bits :=
  Trans.Hash.encProg_hashProgram (data hD hd A) (base_ge_eight hD hd A)
    actualMGG _ _ scale bits hbits

/-- The explicit bit list consumed by the actual installed parser/hash slices. -/
theorem cells_ofTape (N : ℕ) (coins : Fin N → Bool) :
    (InputWord.ofTape N coins).cells = List.ofFn coins := by
  induction N with
  | zero => rfl
  | succ N ih => simp [InputWord.ofTape,InputWord.cells,List.ofFn_succ,ih]

theorem decode_slice (L w m : ℕ) (coins : Fin (CodeHash.repeatBits L w m) → Bool)
    (rep : Fin (2*m+1)) :
    decodeCoins L w m coins rep = Trans.Hash.seedOfBits L w
      (((List.ofFn coins).drop (rep.val * CodeHash.seedBits L w)).take (CodeHash.seedBits L w)) := by
  unfold decodeCoins actualCodeHashSeedTuple
  rw [sample_exact]
  simp only
  rw [cells_ofTape,Trans.Hash.outputSeeds_slice]

theorem slice_length (L w m : ℕ) (coins : Fin (CodeHash.repeatBits L w m) → Bool)
    (rep : ℕ) (hr : rep < 2*m+1) :
    (((List.ofFn coins).drop (rep * CodeHash.seedBits L w)).take (CodeHash.seedBits L w)).length =
      CodeHash.seedBits L w := by
  have hlen : (List.ofFn coins).length = (2*m+1)*CodeHash.seedBits L w := by
    rw [List.length_ofFn]
    rfl
  have hle : (rep+1)*CodeHash.seedBits L w ≤ (2*m+1)*CodeHash.seedBits L w :=
    Nat.mul_le_mul_right _ hr
  rw [List.length_take,List.length_drop,hlen]
  have hsum : rep*CodeHash.seedBits L w + CodeHash.seedBits L w ≤
      (2*m+1)*CodeHash.seedBits L w := by
    rw [Nat.succ_mul] at hle
    exact hle
  omega

end QecReliability.LatentMachine.Factory
