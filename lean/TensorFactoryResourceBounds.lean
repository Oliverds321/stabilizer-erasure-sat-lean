import TensorFactorySeeds
import TensorCountingSpace
import ResourceSATOracle

/-! All-length hash and dimension-aware SAT resource bounds for the tensor
machine, including the empty key. The additive constant is retained at q=0. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate

namespace Factory
private theorem forward_gates_all (X : DyadicXorData) (hb : 8 ≤ X.base)
    (G : MGGInput) (n : ℕ) (ds : List ℕ) (scale : Fin (keySize n ds.sum+1))
    (seed : CodeHash.Seed (X.walkCode hb G (keySize n ds.sum)).L
      ((X.walkCode hb G (keySize n ds.sum)).steps+1)) :
    (((X.walkCircuits hb G (keySize n ds.sum)).forward
      (TensorCoefficientCounting.keyBits n ds)).compiled.implementation.supplied.program scale seed).gates ≤
        X.Cfixed * (keySize n ds.sum+1) :=
  (((X.walkCircuits hb G (keySize n ds.sum)).forward
    (TensorCoefficientCounting.keyBits n ds)).hash_gates scale seed).trans
      (X.gates_all_lengths hb G (keySize n ds.sum))

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

theorem gates_all (n : ℕ) (ds : List ℕ) (scale : Fin (keySize n ds.sum+1))
    (seed : CodeHash.Seed (length hD hd A n ds) (width hD hd A n ds)) :
    ((circuits hD hd A n ds).program scale seed).gates ≤
      (data hD hd A).Cfixed * (keySize n ds.sum+1) :=
  forward_gates_all (data hD hd A) (base_ge_eight hD hd A) actualMGG n ds scale seed

theorem seed_all (n : ℕ) (ds : List ℕ) :
    CodeHash.seedBits (length hD hd A n ds) (width hD hd A n ds) ≤
      (data hD hd A).Cseed * (keySize n ds.sum+1) :=
  (data hD hd A).seed_all_lengths (base_ge_eight hD hd A) actualMGG (keySize n ds.sum)
end Factory

namespace Boundary
variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (TensorCoefficientCounting.Key n ds) (keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))

def extentCap (density g : ℕ) : ℕ :=
  let V := max (TensorQuery.Service.variableBound rows C g)
    (density*TensorQuery.Service.clauseBound rows C g)
  V + QueryCodec.sizeBound V (TensorQuery.Service.clauseBound rows C g)

theorem query_resource_qok {kE : ℕ} {ΓE ΛE : Type}
    [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE] (E : Machine kE ΓE ΛE)
    (m : ℕ) (ω : Fin (2*m+1) → Ω) (density g : ℕ)
    (hg : ∀ scale seed, (K.program scale seed).gates ≤ g)
    (key : RequestKey) (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key) :
    (RegMachine.resourceSatOracle E density requestExtent (extentCap rows C density g)).qok
      (query rows C H K m ω density key) := by
  have hdim : (resolve rows C H K m ω key valid).varCount ≤
      TensorQuery.Service.variableBound rows C g ∧
      (resolve rows C H K m ω key valid).formula.length ≤
        TensorQuery.Service.clauseBound rows C g := by
    cases key with
    | base side j rep => exact TensorQuery.Service.base_dimensions rows C g _ []
    | cell side j rep scale pre =>
      exact TensorQuery.Service.cell_dimensions rows C H K g _ _ _ pre (hg _ _)
  refine ⟨padRequest density (resolve rows C H K m ω key valid),
    padRequest_density density _,query_valid rows C H K m ω density key valid,?_⟩
  exact padRequest_extent_le _ _ _ hdim.1 hdim.2

theorem extentCap_polynomial (density g N : ℕ) (hr : ds.sum ≤ N) (hk : ds.length ≤ N)
    (hn : n ≤ N) (hrows : rowIncidences rows ≤ N) (hC : C.gates ≤ N) (hg : g ≤ N) :
    extentCap rows C density g ≤
      (46+178*density)*N+6*density+1+TensorQuery.Service.bitBound density N := by
  have hd := TensorQuery.Service.linear_dimensions rows C g N hr hk hn hrows hC hg
  have hb := TensorQuery.Service.sizeBound_le_bitBound rows C density g N hr hk hn hrows hC hg
  have hv : max (TensorQuery.Service.variableBound rows C g)
      (density*TensorQuery.Service.clauseBound rows C g) ≤ (46+178*density)*N+6*density+1 := by
    apply max_le
    · nlinarith [Nat.zero_le (178*density*N), Nat.zero_le (6*density)]
    · have hh := Nat.mul_le_mul_left density hd.2
      nlinarith
  exact Nat.add_le_add hv hb

end Boundary
end QecReliability.TensorMachine
