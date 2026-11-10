import QecReliability.SelectedSparseAmplifier

/-!


A supplied packed certificate, rather than the least-table scanner, drives the
same padded-amplifier formula. The graph-only theorems are reused unchanged.
No selector is called by a declaration below.
The final existential has ONE certificate outside ALL length quantifiers.
This is a semantic amplifier theorem, NOT a finite-generator theorem.
-/

set_option autoImplicit false

namespace QecReliability.ExpanderWalk.FixedWitnessSparseAmplifier
open scoped BigOperators
open CodeHash SparseAmplifierCandidate
open FiniteLocalSelectorCandidate

/-- Package supplied finite data. The checker proof is erased; no checker is run. -/
def certificateOfPacked {k h r : Nat}
    (a : PackedSemanticBridgeCandidate.Packed (h * k))
    (ha : checkMatrix k h r a.val = true) : CertifiedParity k h r where
  code := a
  distance := (checkMatrix_spec k h r a.val).mp ha

@[simp] theorem certificateOfPacked_code {k h r : Nat}
    (a : PackedSemanticBridgeCandidate.Packed (h * k))
    (ha : checkMatrix k h r a.val = true) :
    (certificateOfPacked a ha).code = a := rfl

/-- Existence is eliminated only into Prop. This does not name or evaluate data. -/
theorem exists_certificate (t : Nat) (ht : 0 < t) :
    Nonempty (CertifiedParity (512 * t) (64 * t) t) := by
  obtain ⟨a, ha, hgood⟩ := PackedSemanticBridgeCandidate.local_packed_exists t ht
  exact ⟨certificateOfPacked ⟨a, ha⟩ hgood⟩

noncomputable section

/-- Parity of this supplied table. No search and no fresh semantic witness. -/
def parity {k h r : Nat} (A : CertifiedParity k h r) :
    Word k →ₗ[F] Word h :=
  FiniteLocalCountingCandidate.parityLinear
    (PackedSemanticBridgeCandidate.certifiedMatrix A)

theorem parity_distance {k h r : Nat} (A : CertifiedParity k h r)
    (z : Word k) (hz : z ≠ 0) :
    r ≤ weight z + weight (parity A z) :=
  PackedSemanticBridgeCandidate.certifiedMatrix_good A z hz

/-- Bit-for-bit row-major refinement to the SAME finite packed certificate. -/
theorem parity_packed {k h r : Nat} (A : CertifiedParity k h r)
    (x : PackedSemanticBridgeCandidate.Packed k) (i : Fin h) :
    parity A (PackedSemanticBridgeCandidate.wordDecode x) i =
      PackedSemanticBridgeCandidate.bitF
        (rowPrefix k A.code.val x.val i.val k) :=
  PackedSemanticBridgeCandidate.certifiedLinear_right A x i

/-- Only dimensions are transported; all coefficients remain those of A.code. -/
def parityForDegree {d t : Nat} (hd : d = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) :
    Word (d + d) →ₗ[F] Word (d / 4) :=
  SelectedSparseAmplifier.castParity
    (by omega : 512 * t = d + d) (by omega : 64 * t = d / 4) (parity A)

theorem parityForDegree_local {d t : Nat} (hd : d = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t)
    (z : Word (d + d)) (hz : z ≠ 0) :
    (d : ℝ) / 256 ≤ (weight z : ℝ) + (weight (parityForDegree hd A z) : ℝ) := by
  have h := SelectedSparseAmplifier.castParity_distance
    (by omega : 512 * t = d + d) (by omega : 64 * t = d / 4)
    (parity A) (parity_distance A) z hz
  change t ≤ weight z + weight (parityForDegree hd A z) at h
  have hr : (t : ℝ) ≤ (weight z : ℝ) + (weight (parityForDegree hd A z) : ℝ) := by
    exact_mod_cast h
  have hd' : (d : ℝ) = 256 * (t : ℝ) := by exact_mod_cast hd
  rw [hd']
  linarith

/-- The generic padded formula, using the same supplied certificate for every T.
The degree remains an argument, avoiding a closed astronomical data initializer. -/
def amplifier (d t : Nat) (hDegree : d = 16 ^ 384) (hd : d = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t)
    (T : Nat) (hdiv : d ∣ T) (hlarge : 8 * d ≤ T) :
    Word T →ₗ[F] Word (T / 2) :=
  paddedAmplifier (SelectedSparseAmplifier.graph d hDegree T hdiv hlarge)
    (SelectedSparseAmplifier.graph_capacity d hDegree T hdiv hlarge).1
    (SelectedSparseAmplifier.graph_capacity d hDegree T hdiv hlarge).2
    (parityForDegree hd A)

theorem amplifier_strict (d t : Nat) (hDegree : d = 16 ^ 384) (hd : d = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t)
    (T : Nat) (hdiv : d ∣ T) (hlarge : 8 * d ≤ T)
    (x : Word T) (hx : 0 < weight x)
    (hsparse : (weight x : ℝ) ≤ (T : ℝ) / 2359296) :
    weight x < weight (amplifier d t hDegree hd A T hdiv hlarge x) := by
  apply padded_sparse_amplification
    (SelectedSparseAmplifier.graph d hDegree T hdiv hlarge)
    (SelectedSparseAmplifier.graph_capacity d hDegree T hdiv hlarge).1
    (SelectedSparseAmplifier.graph_capacity d hDegree T hdiv hlarge).2
    (parityForDegree hd A) (parityForDegree_local hd A)
    (lam := 1 / 4096) (by norm_num) (le_refl _)
    (SelectedSparseAmplifier.graph_centered d hDegree T hdiv hlarge) x hx
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using hsparse

/-- Symbolic specialization keeps finite packed dimensions abstract during elaboration. -/
theorem exists_one_certificate_all_amplifiers (d t : Nat)
    (hDegree : d = 16 ^ 384) (hd : d = 256 * t) (ht : 0 < t) :
    ∃ A : CertifiedParity (512 * t) (64 * t) t,
      trueEntryCount A ≤ (64 * t) * (512 * t) ∧
      ∀ (T : Nat) (hdiv : d ∣ T) (hlarge : 8 * d ≤ T) (x : Word T),
        0 < weight x → (weight x : ℝ) ≤ (T : ℝ) / 2359296 →
        weight x < weight (amplifier d t hDegree hd A T hdiv hlarge x) := by
  obtain ⟨A⟩ := exists_certificate t ht
  refine ⟨A, trueEntryCount_le A, ?_⟩
  intro T hdiv hlarge x hx hsparse
  exact amplifier_strict d t hDegree hd A T hdiv hlarge x hx hsparse

/-- Unconditional ONE-table/all-length semantic closure. The huge table is
neither searched for nor materialized. This is not an executable name. -/
theorem exists_one_fixed_certificate_all_amplifiers :
    ∃ A : CertifiedParity (512 * 2 ^ 1528) (64 * 2 ^ 1528) (2 ^ 1528),
      trueEntryCount A ≤ (64 * 2 ^ 1528) * (512 * 2 ^ 1528) ∧
      ∀ (T : Nat) (hdiv : (16 : Nat) ^ 384 ∣ T)
        (hlarge : 8 * (16 : Nat) ^ 384 ≤ T) (x : Word T),
        0 < weight x → (weight x : ℝ) ≤ (T : ℝ) / 2359296 →
        weight x < weight
          (amplifier (16 ^ 384) (2 ^ 1528) rfl
            FiniteLocalCountingCandidate.fixed_degree_reparametrization
            A T hdiv hlarge x) := by
  exact exists_one_certificate_all_amplifiers (16 ^ 384) (2 ^ 1528) rfl
    FiniteLocalCountingCandidate.fixed_degree_reparametrization
    (pow_pos (by decide : 0 < (2 : Nat)) _)

end
end QecReliability.ExpanderWalk.FixedWitnessSparseAmplifier
