import QecReliability.DirectedPortSparseCandidate

/-!


This is the semantic map and weight proof, NOT a circuit or machine-cost proof.
-/

noncomputable section
namespace QecReliability.ExpanderWalk.SparseAmplifierCandidate
open scoped BigOperators
open CodeHash

variable {n d : ℕ} (G : PortGraph n d)

theorem localWord_add (x y : Arc n d → F) (v : Fin n) :
    (localWord G) (x + y) v = (localWord G) x v + (localWord G) y v := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [localWord, Pi.add_apply, Fin.append_left, Fin.append_right]

theorem localWord_smul (c : F) (x : Arc n d → F) (v : Fin n) :
    (localWord G) (c • x) v = c • (localWord G) x v := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [localWord, Pi.smul_apply, Fin.append_left, Fin.append_right]

/-- Flattening uses the existing explicit mixed-radix Fin-product equivalence. -/
def rawAmplifier (A : Word (d + d) →ₗ[F] Word (d / 4)) :
    Word (n * d) →ₗ[F] Word (n * (d / 4)) where
  toFun x j :=
    A ((localWord G) (fun p => x (finProdFinEquiv p)) (finProdFinEquiv.symm j).1)
      (finProdFinEquiv.symm j).2
  map_add' x y := by
    ext j
    have hh : (fun p : Arc n d => (x + y) (finProdFinEquiv p)) =
        (fun p => x (finProdFinEquiv p)) + (fun p => y (finProdFinEquiv p)) := rfl
    change A ((localWord G) (fun p => (x + y) (finProdFinEquiv p)) _) _ = _
    rw [hh, (localWord_add G), map_add]
    rfl
  map_smul' c x := by
    ext j
    have hh : (fun p : Arc n d => (c • x) (finProdFinEquiv p)) =
        c • (fun p => x (finProdFinEquiv p)) := rfl
    change A ((localWord G) (fun p => (c • x) (finProdFinEquiv p)) _) _ = _
    rw [hh, (localWord_smul G), map_smul]
    rfl

theorem flat_input_weight (x : Word (n * d)) :
    supportWeight (fun p : Arc n d => x (finProdFinEquiv p)) = weight x :=
  (supportWeight_equiv finProdFinEquiv x).trans (supportWeight_fin x)

theorem rawAmplifier_weight (A : Word (d + d) →ₗ[F] Word (d / 4))
    (x : Word (n * d)) :
    weight ((rawAmplifier G) A x) =
      (parityWeight G) A (fun p => x (finProdFinEquiv p)) := by
  change supportWeight ((rawAmplifier G) A x) = _
  rw [← supportWeight_equiv
    (finProdFinEquiv : (Fin n × Fin (d / 4)) ≃ Fin (n * (d / 4))) ((rawAmplifier G) A x)]
  simp only [rawAmplifier, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]
  rw [supportWeight_prod]
  rfl

/-- Existing CodeHash.pad preserves exact Hamming weight, not merely nonzeroness. -/
theorem weight_pad {q k : ℕ} (h : q ≤ k) (x : Word q) : weight (pad h x) = weight x := by
  classical
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le h
  have hp : pad h x = Fin.append x (0 : Word z) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [pad, j.isLt]
    · have hj : ¬ q + j.val < q := by omega
      simp [pad, hj]
  rw [hp, weight_append_zero]

/-- Both padding maps are literal zero padding. Input/output references and
linear-circuit realization are separate from this semantic construction. -/
def paddedAmplifier {T : ℕ} (hIn : T ≤ n * d) (hOut : n * (d / 4) ≤ T / 2)
    (A : Word (d + d) →ₗ[F] Word (d / 4)) : Word T →ₗ[F] Word (T / 2) :=
  (pad hOut).comp (((rawAmplifier G) A).comp (pad hIn))

/-- Exact T-to-T/2 sparse amplification, after input and output zero padding. -/
theorem padded_sparse_amplification {T : ℕ}
    (hIn : T ≤ n * d) (hOut : n * (d / 4) ≤ T / 2)
    (A : Word (d + d) →ₗ[F] Word (d / 4))
    (hlocal : ∀ z : Word (d + d), z ≠ 0 →
      (d : ℝ) / 256 ≤ (weight z : ℝ) + (weight (A z) : ℝ))
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 4096)
    (hupper : ∀ f : RVec n, (∑ v, f v) = 0 →
      dot f (G.transition f) ≤ lam * energy f)
    (x : Word T) (hx : 0 < weight x)
    (hsparse : (weight x : ℝ) ≤ (1 / 2359296 : ℝ) * (T : ℝ)) :
    weight x < weight ((paddedAmplifier G) hIn hOut A x) := by
  let xp : Arc n d → F := fun p => pad hIn x (finProdFinEquiv p)
  have hxp : supportWeight xp = weight x := by
    dsimp [xp]
    rw [flat_input_weight, weight_pad]
  have hpos : 0 < supportWeight xp := by rw [hxp]; exact hx
  have hT : (T : ℝ) ≤ ((n * d : ℕ) : ℝ) := by exact_mod_cast hIn
  have hsmall : (supportWeight xp : ℝ) ≤
      (1 / 2359296 : ℝ) * ((n * d : ℕ) : ℝ) := by
    rw [hxp]
    exact hsparse.trans (mul_le_mul_of_nonneg_left hT (by norm_num))
  have hresult := (directed_sparse_amplification G) A hlocal hlam0 hlam hupper xp hpos hsmall
  rw [hxp] at hresult
  change weight x < weight (pad hOut ((rawAmplifier G) A (pad hIn x)))
  rw [weight_pad, (rawAmplifier_weight G)]
  exact hresult

/-- Exact parity-output multiplicity and capacity. Four-divisibility is kept
explicit; it is supplied by 256 | D in the concrete construction. -/
theorem parity_capacity {T : ℕ} (hd4 : 4 ∣ d) (hM : n * d ≤ 2 * T) :
    4 * (n * (d / 4)) = n * d ∧ n * (d / 4) ≤ T / 2 := by
  have hd : d / 4 * 4 = d := Nat.div_mul_cancel hd4
  have he : 4 * (n * (d / 4)) = n * d := by
    calc
      4 * (n * (d / 4)) = n * (d / 4 * 4) := by ring
      _ = n * d := by rw [hd]
  refine ⟨he, ?_⟩
  rw [← he] at hM
  omega

/-- Arithmetic square-rounding contract, stated on the exact quotient L.
No spectral graph test, graph choice, or per-length code search is hidden here. -/
theorem square_padding_bounds_exact {T L s : ℕ}
    (hT : T = d * L) (hL : 8 ≤ L)
    (hcover : L ≤ s * s) (hminimal : (s - 1) * (s - 1) < L) :
    3 ≤ s ∧ T ≤ d * (s * s) ∧ d * (s * s) ≤ 2 * T := by
  have hs3 : 3 ≤ s := by
    by_contra h
    have hs2 : s ≤ 2 := by omega
    have hsq : s * s ≤ 2 * 2 := Nat.mul_le_mul hs2 hs2
    omega
  have hpred : s - 1 = (s - 2) + 1 := by omega
  have hs : s = (s - 2) + 2 := by omega
  have hsq : s * s ≤ 2 * L := by
    rw [hpred] at hminimal
    rw [hs]
    nlinarith [Nat.zero_le ((s - 2) * (s - 2))]
  refine ⟨hs3, ?_, ?_⟩
  · rw [hT]
    exact Nat.mul_le_mul_left d hcover
  · calc
      d * (s * s) ≤ d * (2 * L) := Nat.mul_le_mul_left d hsq
      _ = 2 * T := by rw [hT]; ring

/-- Divisibility is essential: this recovers the exact quotient, not a
floor-rounded approximation that could invalidate the factor-two bound. -/
theorem square_padding_bounds {T s : ℕ} (hd : 0 < d) (hdiv : d ∣ T)
    (hlarge : 8 * d ≤ T) (hcover : T / d ≤ s * s)
    (hminimal : (s - 1) * (s - 1) < T / d) :
    3 ≤ s ∧ T ≤ d * (s * s) ∧ d * (s * s) ≤ 2 * T := by
  have hT : T = d * (T / d) := by
    simpa only [Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
  have hL : 8 ≤ T / d := by
    by_contra h
    have hle : T / d ≤ 7 := by omega
    have hm := Nat.mul_le_mul_left d hle
    rw [← hT] at hm
    nlinarith
  exact square_padding_bounds_exact hT hL hcover hminimal

end QecReliability.ExpanderWalk.SparseAmplifierCandidate
