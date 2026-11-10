/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
Concrete semantic sparse amplifier from the SAME selected packed local matrix
and the actual powered MGG graph. No circuit or machine-cost bound is claimed.
The selector scale is an explicit runtime argument; never evaluate the fixed search.
-/
import QecReliability.PaddedSparseCandidate
import QecReliability.PoweredMGGPortGraph
import QecReliability.PackedSemanticBridgeCandidate

noncomputable section
namespace QecReliability.ExpanderWalk.SelectedSparseAmplifier
open scoped BigOperators
open CodeHash SparseAmplifierCandidate

/-- Parity of the actual selected table, not another existential witness. -/
def selectedParity (t : ℕ) (ht : 0 < t) : Word (512 * t) →ₗ[F] Word (64 * t) :=
  FiniteLocalCountingCandidate.parityLinear
    (PackedSemanticBridgeCandidate.certifiedMatrix
      (PackedSemanticBridgeCandidate.localCertified t ht))

theorem selectedParity_distance (t : ℕ) (ht : 0 < t)
    (z : Word (512 * t)) (hz : z ≠ 0) :
    t ≤ weight z + weight (selectedParity t ht z) :=
  PackedSemanticBridgeCandidate.certifiedMatrix_good
    (PackedSemanticBridgeCandidate.localCertified t ht) z hz

/-- Pointwise refinement to the exact selected A.code used by the packed checker. -/
theorem selectedParity_packed (t : ℕ) (ht : 0 < t)
    (x : PackedSemanticBridgeCandidate.Packed (512 * t)) (i : Fin (64 * t)) :
    selectedParity t ht (PackedSemanticBridgeCandidate.wordDecode x) i =
      PackedSemanticBridgeCandidate.bitF
        (FiniteLocalSelectorCandidate.rowPrefix (512 * t)
          (PackedSemanticBridgeCandidate.localCertified t ht).code.val x.val i.val (512 * t)) :=
  PackedSemanticBridgeCandidate.certifiedLinear_right
    (PackedSemanticBridgeCandidate.localCertified t ht) x i

/-- Only dimension equalities are transported; the matrix entries stay the same. -/
def castParity {k h k' h' : ℕ} (hk : k = k') (hh : h = h')
    (A : Word k →ₗ[F] Word h) : Word k' →ₗ[F] Word h' :=
  hk ▸ hh ▸ A

theorem castParity_distance {k h k' h' r : ℕ} (hk : k = k') (hh : h = h')
    (A : Word k →ₗ[F] Word h)
    (hA : ∀ z : Word k, z ≠ 0 → r ≤ weight z + weight (A z))
    (z : Word k') (hz : z ≠ 0) :
    r ≤ weight z + weight (castParity hk hh A z) := by
  cases hk
  cases hh
  exact hA z hz

def selectedParityForDegree {d t : ℕ} (hd : d = 256 * t) (ht : 0 < t) :
    Word (d + d) →ₗ[F] Word (d / 4) :=
  castParity (by omega : 512 * t = d + d) (by omega : 64 * t = d / 4)
    (selectedParity t ht)

theorem selectedParityForDegree_local {d t : ℕ} (hd : d = 256 * t) (ht : 0 < t)
    (z : Word (d + d)) (hz : z ≠ 0) :
    (d : ℝ) / 256 ≤ (weight z : ℝ) + (weight (selectedParityForDegree hd ht z) : ℝ) := by
  have h := castParity_distance (by omega : 512 * t = d + d)
    (by omega : 64 * t = d / 4) (selectedParity t ht) (selectedParity_distance t ht) z hz
  change t ≤ weight z + weight (selectedParityForDegree hd ht z) at h
  have h' : (t : ℝ) ≤ (weight z : ℝ) + (weight (selectedParityForDegree hd ht z) : ℝ) := by
    exact_mod_cast h
  have hd' : (d : ℝ) = 256 * (t : ℝ) := by exact_mod_cast hd
  rw [hd']
  linarith

/-- Symbolic reparameterization only; the large powers are never normalized. -/
theorem fixed_degree_eq (runtimeT : ℕ) (hT : runtimeT = 2 ^ 1528) :
    (16 : ℕ) ^ 384 = 256 * runtimeT := by
  rw [hT]
  exact FiniteLocalCountingCandidate.fixed_degree_reparametrization

theorem fixed_degree_pos : 0 < (16 : ℕ) ^ 384 := pow_pos (by decide) _

theorem fixed_degree_four_dvd : 4 ∣ (16 : ℕ) ^ 384 := by
  rw [FiniteLocalCountingCandidate.fixed_degree_reparametrization]
  exact dvd_mul_of_dvd_left (by decide : (4 : ℕ) ∣ 256) _

/-- Exact quotient admissibility; no floor approximation is used. -/
theorem quotient_large {d T : ℕ} (hd : 0 < d) (hdiv : d ∣ T) (hlarge : 8 * d ≤ T) :
    8 ≤ T / d := by
  have hT : T = d * (T / d) := by
    simpa only [Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
  by_contra h
  have hle : T / d ≤ 7 := by omega
  have hm := Nat.mul_le_mul_left d hle
  rw [← hT] at hm
  nlinarith

/-- A degree equality only transports the rotation's index type. -/
def castGraphDegree {n d e : ℕ} (h : d = e) (G : PortGraph n d) : PortGraph n e :=
  h ▸ G

/-- The actual square-order graph; degree and quotient remain runtime inputs. -/
def graph (runtimeD : ℕ) (hDegree : runtimeD = 16 ^ 384) (T : ℕ)
    (hdiv : runtimeD ∣ T) (hlarge : 8 * runtimeD ≤ T) :
    PortGraph (QuantumExpander.squareSide (T / runtimeD) * QuantumExpander.squareSide (T / runtimeD))
      runtimeD :=
  castGraphDegree hDegree.symm
    (poweredSquarePortGraph (T / runtimeD)
      (quotient_large (hDegree.symm ▸ fixed_degree_pos) hdiv hlarge))

theorem graph_capacity (runtimeD : ℕ) (hDegree : runtimeD = 16 ^ 384) (T : ℕ)
    (hdiv : runtimeD ∣ T) (hlarge : 8 * runtimeD ≤ T) :
    T ≤ (QuantumExpander.squareSide (T / runtimeD) *
      QuantumExpander.squareSide (T / runtimeD)) * runtimeD ∧
    (QuantumExpander.squareSide (T / runtimeD) *
      QuantumExpander.squareSide (T / runtimeD)) * (runtimeD / 4) ≤ T / 2 := by
  have hd : 0 < runtimeD := hDegree.symm ▸ fixed_degree_pos
  have hd4 : 4 ∣ runtimeD := hDegree.symm ▸ fixed_degree_four_dvd
  have hL := quotient_large hd hdiv hlarge
  have hb := square_padding_bounds hd hdiv hlarge
    (QuantumExpander.squareSide_covers (T / runtimeD) (by omega))
    (by simpa only [pow_two] using
      QuantumExpander.squareSide_predecessor_sq_lt (T / runtimeD) (by omega))
  have hm : (QuantumExpander.squareSide (T / runtimeD) *
      QuantumExpander.squareSide (T / runtimeD)) * runtimeD ≤ 2 * T := by
    simpa only [Nat.mul_comm] using hb.2.2
  exact ⟨by simpa only [Nat.mul_comm] using hb.2.1, (parity_capacity hd4 hm).2⟩

theorem graph_centered (runtimeD : ℕ) (hDegree : runtimeD = 16 ^ 384) (T : ℕ)
    (hdiv : runtimeD ∣ T) (hlarge : 8 * runtimeD ≤ T)
    (f : RVec (QuantumExpander.squareSide (T / runtimeD) *
      QuantumExpander.squareSide (T / runtimeD))) (hf : (∑ i, f i) = 0) :
    dot f ((graph runtimeD hDegree T hdiv hlarge).transition f) ≤
      (1 / 4096 : ℝ) * energy f := by
  subst runtimeD
  have hg := (poweredSquarePortGraph_spec (T / (16 ^ 384))
    (quotient_large fixed_degree_pos hdiv hlarge)).2.2
  have h := hg.rayleigh f
  change dot f ((graph (16 ^ 384) rfl T hdiv hlarge).transition f) ≤ _ at h
  have hc : (1 - 4095 / 4096 : ℝ) = 1 / 4096 := by norm_num
  simpa only [hf, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, hc] using h

/-- Semantic constructor with all data dimensions passed at runtime. -/
def amplifierForDegree (d t : ℕ) (hDegree : d = 16 ^ 384)
    (hd : d = 256 * t) (ht : 0 < t) (T : ℕ) (hdiv : d ∣ T) (hlarge : 8 * d ≤ T) :
    Word T →ₗ[F] Word (T / 2) :=
  paddedAmplifier (graph d hDegree T hdiv hlarge)
    (graph_capacity d hDegree T hdiv hlarge).1 (graph_capacity d hDegree T hdiv hlarge).2
    (selectedParityForDegree hd ht)

theorem amplifierForDegree_strict (d t : ℕ) (hDegree : d = 16 ^ 384)
    (hd : d = 256 * t) (ht : 0 < t) (T : ℕ) (hdiv : d ∣ T) (hlarge : 8 * d ≤ T)
    (x : Word T) (hx : 0 < weight x)
    (hsparse : (weight x : ℝ) ≤ (T : ℝ) / 2359296) :
    weight x < weight (amplifierForDegree d t hDegree hd ht T hdiv hlarge x) := by
  apply padded_sparse_amplification (graph d hDegree T hdiv hlarge)
    (graph_capacity d hDegree T hdiv hlarge).1 (graph_capacity d hDegree T hdiv hlarge).2
    (selectedParityForDegree hd ht) (selectedParityForDegree_local hd ht)
    (lam := 1 / 4096) (by norm_num) (le_refl _) (graph_centered d hDegree T hdiv hlarge) x hx
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using hsparse

/-- A finite linear T-to-floor(T/2) map built from the selected packed table.
`runtimeT` is a genuine input to both the selector and runtime degree calculation.
There is no closed selected-data value and no native power/search at module import. -/
def amplifier (runtimeT : ℕ) (hRuntime : runtimeT = 2 ^ 1528)
    (T : ℕ) (hdiv : (16 : ℕ) ^ 384 ∣ T) (hlarge : 8 * (16 : ℕ) ^ 384 ≤ T) :
    Word T →ₗ[F] Word (T / 2) :=
  amplifierForDegree (256 * runtimeT) runtimeT (fixed_degree_eq runtimeT hRuntime).symm rfl
    (hRuntime.symm ▸ pow_pos (by decide : (0 : ℕ) < 2) 1528) T
    (by rw [← fixed_degree_eq runtimeT hRuntime]; exact hdiv)
    (by rw [← fixed_degree_eq runtimeT hRuntime]; exact hlarge)

/-- No caller-supplied spectral or local-distance premise remains. -/
theorem amplifier_strict (runtimeT : ℕ) (hRuntime : runtimeT = 2 ^ 1528)
    (T : ℕ) (hdiv : (16 : ℕ) ^ 384 ∣ T) (hlarge : 8 * (16 : ℕ) ^ 384 ≤ T)
    (x : Word T) (hx : 0 < weight x)
    (hsparse : (weight x : ℝ) ≤ (T : ℝ) / 2359296) :
    weight x < weight (amplifier runtimeT hRuntime T hdiv hlarge x) :=
  amplifierForDegree_strict (256 * runtimeT) runtimeT
    (fixed_degree_eq runtimeT hRuntime).symm rfl
    (hRuntime.symm ▸ pow_pos (by decide : (0 : ℕ) < 2) 1528) T
    (by rw [← fixed_degree_eq runtimeT hRuntime]; exact hdiv)
    (by rw [← fixed_degree_eq runtimeT hRuntime]; exact hlarge) x hx hsparse

/-- Closed proposition-level specialization. No closed data definition or initializer
is generated by this theorem, and the selected-code search is never evaluated. -/
theorem exists_amplifier (T : ℕ) (hdiv : (16 : ℕ) ^ 384 ∣ T)
    (hlarge : 8 * (16 : ℕ) ^ 384 ≤ T) :
    ∃ A : Word T →ₗ[F] Word (T / 2), ∀ x : Word T, 0 < weight x →
      (weight x : ℝ) ≤ (T : ℝ) / 2359296 → weight x < weight (A x) := by
  refine ⟨amplifier (2 ^ 1528) rfl T hdiv hlarge, ?_⟩
  exact amplifier_strict (2 ^ 1528) rfl T hdiv hlarge

end QecReliability.ExpanderWalk.SelectedSparseAmplifier
