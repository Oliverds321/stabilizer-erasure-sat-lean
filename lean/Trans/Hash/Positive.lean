import Trans.Hash.Corr
import WholeWrapperFixedProbability

/-!
# Trans.Hash.Positive: the hash program used by the algorithm, on plain data

`(positiveCircuits hD hd A k).program scale seed` with `q = keySize (k+1) (k+1)` is
`hashPlain` of the constants `X = data hD hd A`, `G = actualMGG` (kept symbolic: nothing about
`16^384` or `2^1528` is evaluated).
-/

set_option autoImplicit false

namespace QecReliability.Trans.Hash
open QecReliability.SharedCircuit QecReliability.Trans.Query QecReliability.CodeHash
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength

theorem encProg_positiveProgram {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (k : ℕ)
    (scale : Fin (keySize (k + 1) (k + 1) + 1)) (bits : List Bool)
    (hbits : bits.length = seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k)) :
    encProg ((positiveCircuits hD hd A k).program scale
        (seedOfBits (positiveLength hD hd A k) (positiveWidth hD hd A k) bits)) =
      hashPlain (data hD hd A).base (data hD hd A).den (keySize (k + 1) (k + 1))
        (fun ell => encProg ((data hD hd A).program ell)) (gNbr actualMGG) scale.val bits :=
  encProg_hashProgram (data hD hd A) (base_ge_eight hD hd A) actualMGG _ _ scale bits hbits

/-- Every seed of the algorithm is the decoding of its bit string. -/
theorem encProg_positiveProgram' {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (k : ℕ)
    (scale : Fin (keySize (k + 1) (k + 1) + 1))
    (seed : Seed (positiveLength hD hd A k) (positiveWidth hD hd A k)) :
    encProg ((positiveCircuits hD hd A k).program scale seed) =
      hashPlain (data hD hd A).base (data hD hd A).den (keySize (k + 1) (k + 1))
        (fun ell => encProg ((data hD hd A).program ell)) (gNbr actualMGG) scale.val
        (seedBitsOf seed) := by
  have h := encProg_positiveProgram hD hd A k scale (seedBitsOf seed) (seedBitsOf_length seed)
  rwa [seedOfBits_seedBitsOf] at h

end QecReliability.Trans.Hash
