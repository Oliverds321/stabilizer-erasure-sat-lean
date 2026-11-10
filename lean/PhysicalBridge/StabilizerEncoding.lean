import PhysicalBridge.CSSStabilizer
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A genuine isometric encoding into the stabilizer codespace, obtained from
an orthonormal basis of its Hilbert realization. -/
noncomputable section
namespace QecPhysical.Stabilizer.Lift
open scoped BigOperators ComplexOrder
open Matrix
open QecReliability.Binary
open QecPhysical.BinaryPauli
variable {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)

def hilbertCodeSpace : Submodule ℂ (EuclideanSpace ℂ (Word n)) :=
  L.codeSpace.comap (WithLp.linearEquiv 2 ℂ (Word n → ℂ)).toLinearMap

def hilbertCodeEquiv : L.hilbertCodeSpace ≃ₗ[ℂ] L.codeSpace :=
  (WithLp.linearEquiv 2 ℂ (Word n → ℂ)).ofSubmodule' L.codeSpace

theorem hilbertCode_finrank :
    Module.finrank ℂ L.hilbertCodeSpace = 2 ^ (n - Module.finrank Bit S) := by
  rw [L.hilbertCodeEquiv.finrank_eq, L.codeSpace_finrank_exact]

def codeBasis : OrthonormalBasis (Fin (Module.finrank ℂ L.hilbertCodeSpace)) ℂ L.hilbertCodeSpace :=
  stdOrthonormalBasis ℂ L.hilbertCodeSpace

def encoding : Matrix (Word n) (Fin (Module.finrank ℂ L.hilbertCodeSpace)) ℂ :=
  fun j i => (L.codeBasis i).val j

theorem encoding_isometry : L.encodingᴴ * L.encoding = 1 := by
  ext i j
  have h := orthonormal_iff_ite.mp L.codeBasis.orthonormal i j
  simp only [Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply'] at h
  simpa only [encoding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Complex.star_def] using h

theorem encoding_intertwines (s : S) : L.op s * L.encoding = L.encoding := by
  ext j i
  have h : L.op s *ᵥ (fun j => (L.codeBasis i).val j) = (fun j => (L.codeBasis i).val j) :=
    (L.codeBasis i).property s
  exact congrFun h j

theorem encoding_mem (x : Fin (Module.finrank ℂ L.hilbertCodeSpace) → ℂ) :
    L.encoding *ᵥ x ∈ L.codeSpace := by
  intro s
  rw [Matrix.mulVec_mulVec, L.encoding_intertwines]

theorem encoding_surjective (v : Word n → ℂ) (hv : v ∈ L.codeSpace) :
    ∃ x, L.encoding *ᵥ x = v := by
  let w : L.hilbertCodeSpace := L.hilbertCodeEquiv.symm ⟨v, hv⟩
  refine ⟨fun i => L.codeBasis.repr w i, ?_⟩
  have h := congrArg L.hilbertCodeEquiv (L.codeBasis.sum_repr w)
  simp only [map_sum, map_smul, w, LinearEquiv.apply_symm_apply] at h
  ext j
  have hj := congrArg (fun u : L.codeSpace => u.val j) h
  have hcoeff (i : Fin (Module.finrank ℂ L.hilbertCodeSpace)) :
      (L.hilbertCodeEquiv (L.codeBasis i)).val j = (L.codeBasis i).val j := rfl
  simpa [encoding, Matrix.mulVec, dotProduct, hcoeff, mul_comm, w] using hj

theorem encoding_range : LinearMap.range L.encoding.toLin' = L.codeSpace := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact L.encoding_mem x
  · exact L.encoding_surjective v

theorem encoding_projector : L.encoding * L.encodingᴴ = L.projector := by
  have hpv : L.projector * L.encoding = L.encoding := by
    ext j i
    exact congrFun (L.projector_fixes (fun j => (L.codeBasis i).val j)
      ((L.codeBasis i).property)) j
  have hvp : L.encodingᴴ * L.projector = L.encodingᴴ := by
    have h := congrArg Matrix.conjTranspose hpv
    simpa only [Matrix.conjTranspose_mul, L.projector_hermitian.eq] using h
  have hfix (v : Word n → ℂ) (hv : v ∈ L.codeSpace) :
      (L.encoding * L.encodingᴴ) *ᵥ v = v := by
    obtain ⟨x, rfl⟩ := L.encoding_surjective v hv
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, L.encoding_isometry, Matrix.mul_one]
  have h : (L.encoding * L.encodingᴴ) * L.projector = L.projector := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec]
    exact hfix _ (L.projector_mem _)
  rwa [Matrix.mul_assoc, hvp] at h

/-- This is an actual CPTP encoder; its matrix image lies in the proved codespace. -/
def encodingChannel : Channel (Fin (Module.finrank ℂ L.hilbertCodeSpace)) (Word n) :=
  isometryChannel L.encoding L.encoding_isometry

theorem logical_dimension : Fintype.card (Fin (Module.finrank ℂ L.hilbertCodeSpace)) =
    2 ^ (n - Module.finrank Bit S) := by
  rw [Fintype.card_fin, L.hilbertCode_finrank]

end QecPhysical.Stabilizer.Lift
