/- Adapted from Geoffrey Irving, girving/aks, commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f.
   Apache-2.0; see LICENSE. Modified 2026-10-28 for Lean 4.24.0/mathlib f897ebc. -/

import AKS.MGG.Defs
import AKS.MGG.DFT
import AKS.MGG.WalkExpansion
import AKS.MGG.YoungAssembly

open Matrix BigOperators Finset Real
open scoped Real

/-- DFT bridge: the walkCLM inner product is bounded by the Fourier bilinear form.

    For mean-zero `f` and `g(x,y) = f(x·n + y)`, `G(α) = ‖dft2d n g α‖`:

    `|⟨f, Wf⟩| · 2n² ≤ ∑_α G(α)·[G(S₂α)·|cos(πα₁/n)| + G(S₁α)·|cos(πα₂/n)|]`

    Proof: chain `mgg_walkCLM_inner_eq_corr` → `corr_pair1/2` → triangle inequality
    → `norm_one_add_ω_inv`. -/
theorem mgg_dft_bridge (n : ℕ) (hn : 3 ≤ n)
    (f : EuclideanSpace ℝ (Fin (n * n)))
    :
    let g : Fin n → Fin n → ℝ := fun x y =>
      f ⟨x.val * n + y.val, by nlinarith [x.isLt, y.isLt]⟩
    let G : Fin n → Fin n → ℝ := fun α₁ α₂ => ‖dft2d n g α₁ α₂‖
    |@inner ℝ _ _ f ((mgg n).walkCLM f)| * (2 * (↑n : ℝ) ^ 2) ≤
      ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        G α₁ α₂ * (G (shearS2Fin n (by omega) (α₁, α₂)).1
                      (shearS2Fin n (by omega) (α₁, α₂)).2 *
                    |cos (↑π * ↑α₁.val / ↑n)| +
                    G (shearS1Fin n (by omega) (α₁, α₂)).1
                      (shearS1Fin n (by omega) (α₁, α₂)).2 *
                    |cos (↑π * ↑α₂.val / ↑n)|) := by
  intro g G
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn0 : 0 < n := by omega
  -- Abbreviate the correlation sums
  set C₁ := ∑ x : Fin n, ∑ y : Fin n,
    g x y * (g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ hn0⟩ y +
             g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ hn0⟩ y)
  set C₂ := ∑ x : Fin n, ∑ y : Fin n,
    g x y * (g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ hn0⟩ +
             g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ hn0⟩)
  -- Step 1: Walk operator expansion: 4*inner = C₁ + C₂
  have hcorr := mgg_walkCLM_inner_eq_corr n hn f
  -- Step 2: DFT of correlation sums (from corr_pair1/2, complex-valued)
  have hF₁ := corr_pair1 n (by omega) g hn
  have hF₂ := corr_pair2 n (by omega) g hn
  -- Abbreviate the Fourier sums
  set F₁ := ∑ α₁ : Fin n, ∑ α₂ : Fin n,
    dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
      ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn0⟩) *
    (1 + ω n ^ (-(α₁.val : ℤ)))
  set F₂ := ∑ α₁ : Fin n, ∑ α₂ : Fin n,
    dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
      ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn0⟩ α₂) *
    (1 + ω n ^ (-(α₂.val : ℤ)))
  -- hF₁ : (↑n)² * ↑C₁ = F₁, hF₂ : (↑n)² * ↑C₂ = F₂
  -- Step 3: |inner| * 2n² = |C₁+C₂|/4 * 2n² = |C₁+C₂| * n²/2
  -- From hcorr: 4*inner = C₁+C₂ → inner = (C₁+C₂)/4
  have h_inner : @inner ℝ _ _ f ((mgg n).walkCLM f) = (C₁ + C₂) / 4 := by
    linarith
  rw [h_inner, abs_div, show |(4:ℝ)| = 4 from by norm_num]
  -- Goal: |C₁+C₂|/4 * (2*n²) ≤ RHS
  -- Simplify: |C₁+C₂|/4 * 2*n² = |C₁+C₂| * n²/2
  rw [div_mul_eq_mul_div]
  -- Goal: |C₁+C₂| * (2*n²) / 4 ≤ RHS
  -- |C₁+C₂| * n² ≤ |n²*C₁| + |n²*C₂|
  -- Since n²*(C₁+C₂) = Re(F₁) + Re(F₂) = Re(F₁+F₂)
  -- We need: |C₁+C₂| * (2*n²) / 4 = |C₁+C₂| * n² / 2
  have h4 : |C₁ + C₂| * (2 * (↑n : ℝ) ^ 2) / 4 = |C₁ + C₂| * (↑n : ℝ) ^ 2 / 2 := by ring
  rw [h4]
  -- Now bound |C₁+C₂| * n²/2
  -- n²*C₁ = Re(F₁) in ℝ: extract from the complex equality
  have h_re_cast : ((↑n : ℂ) ^ 2).re = (↑n : ℝ) ^ 2 := by norm_cast
  have h_C₁_re : (↑n : ℝ) ^ 2 * C₁ = (F₁).re := by
    have := congr_arg Complex.re hF₁
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    rw [h_re_cast] at this; exact this
  have h_C₂_re : (↑n : ℝ) ^ 2 * C₂ = (F₂).re := by
    have := congr_arg Complex.re hF₂
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    rw [h_re_cast] at this; exact this
  -- |C₁+C₂|*n²/2 = |n²*C₁ + n²*C₂|/2 = |Re(F₁) + Re(F₂)|/2
  have h_sum : |C₁ + C₂| * (↑n : ℝ) ^ 2 = |F₁.re + F₂.re| := by
    have h_nn : (0 : ℝ) ≤ (↑n : ℝ) ^ 2 := by positivity
    rw [mul_comm, ← abs_of_nonneg h_nn, ← abs_mul, mul_add, h_C₁_re, h_C₂_re]
  rw [h_sum]
  -- |Re(F₁) + Re(F₂)|/2 ≤ (‖F₁‖ + ‖F₂‖)/2  [|Re z| ≤ ‖z‖]
  -- ≤ (∑|term₁| + ∑|term₂|)/2  [triangle inequality on sums]
  -- Each |term| = G*G∘S*‖1+ω‖ = G*G∘S*2|cos|  [norm_one_add_ω_inv]
  -- So ≤ (2*∑G*G∘S₂*|cos₁| + 2*∑G*G∘S₁*|cos₂|)/2
  -- = ∑G*(G∘S₂*|cos₁| + G∘S₁*|cos₂|)
  -- Bound |Re(F₁)+Re(F₂)| ≤ |Re(F₁)| + |Re(F₂)| ≤ ‖F₁‖ + ‖F₂‖
  have hre_le : |F₁.re + F₂.re| / 2 ≤ (‖F₁‖ + ‖F₂‖) / 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 2).le
    calc |F₁.re + F₂.re| ≤ |F₁.re| + |F₂.re| := abs_add_le _ _
      _ ≤ ‖F₁‖ + ‖F₂‖ := add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
  -- Bound ‖F_j‖ ≤ ∑‖term_j‖ (triangle inequality on sums)
  have hF₁_tri : ‖F₁‖ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn0⟩ *
      ‖(1 : ℂ) + ω n ^ (-(α₁.val : ℤ))‖ := by
    calc ‖F₁‖ ≤ ∑ α₁ : Fin n, ‖∑ α₂ : Fin n,
        dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
          ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩) *
        (1 + ω n ^ (-(α₁.val : ℤ)))‖ := norm_sum_le _ _
      _ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        ‖dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
          ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩) *
        (1 + ω n ^ (-(α₁.val : ℤ)))‖ := by
        gcongr with α₁; exact norm_sum_le _ _
      _ = _ := by
        congr 1; ext α₁; congr 1; ext α₂
        rw [norm_mul, norm_mul, Complex.norm_conj]
  have hF₂_tri : ‖F₂‖ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      G α₁ α₂ * G ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn0⟩ α₂ *
      ‖(1 : ℂ) + ω n ^ (-(α₂.val : ℤ))‖ := by
    calc ‖F₂‖ ≤ ∑ α₁ : Fin n, ‖∑ α₂ : Fin n,
        dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
          ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂) *
        (1 + ω n ^ (-(α₂.val : ℤ)))‖ := norm_sum_le _ _
      _ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        ‖dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
          ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂) *
        (1 + ω n ^ (-(α₂.val : ℤ)))‖ := by
        gcongr with α₁; exact norm_sum_le _ _
      _ = _ := by
        congr 1; ext α₁; congr 1; ext α₂
        rw [norm_mul, norm_mul, Complex.norm_conj]
  -- Apply norm_one_add_ω_inv: ‖1+ω^{-a}‖ = 2*|cos(πa/n)|
  simp_rw [norm_one_add_ω_inv n (by omega)] at hF₁_tri hF₂_tri
  -- Chain everything
  calc |F₁.re + F₂.re| / 2
      ≤ (‖F₁‖ + ‖F₂‖) / 2 := hre_le
    _ ≤ ((∑ α₁, ∑ α₂, G α₁ α₂ * G α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩ *
            (2 * |cos (↑π * ↑α₁.val / ↑n)|)) +
         (∑ α₁, ∑ α₂, G α₁ α₂ * G ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂ *
            (2 * |cos (↑π * ↑α₂.val / ↑n)|))) / 2 := by
        gcongr
    _ = ∑ α₁, ∑ α₂, G α₁ α₂ *
          (G (shearS2Fin n hn0 (α₁, α₂)).1 (shearS2Fin n hn0 (α₁, α₂)).2 *
            |cos (↑π * ↑α₁.val / ↑n)| +
           G (shearS1Fin n hn0 (α₁, α₂)).1 (shearS1Fin n hn0 (α₁, α₂)).2 *
            |cos (↑π * ↑α₂.val / ↑n)|) := by
      -- Factor out 2/2 = 1 and combine sums
      rw [div_eq_iff (show (2:ℝ) ≠ 0 by norm_num)]
      rw [← Finset.sum_add_distrib]
      simp_rw [← Finset.sum_add_distrib]
      conv_rhs => rw [Finset.sum_mul]; arg 2; ext; rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro α₁ _
      apply Finset.sum_congr rfl; intro α₂ _
      simp only [shearS2Fin, shearS1Fin]
      ring

/-- The adjacency eigenvalue bound: for mean-zero `f` with `‖f‖ = 1`,
    `|⟨f, Wf⟩| ≤ 5√2/8` where `W = A/8` is the normalized walk operator.

    Combines:
    - `mgg_dft_bridge`: `|⟨f,Wf⟩| · 2n² ≤ ∑ G·[G∘S₂·cos₁ + G∘S₁·cos₂]`
    - `young_assembly`: `∑ G·[...] ≤ (5√2/4)·∑ G²`
    - `parseval_2d`: `∑ ‖ĝ‖² = n²·∑ g²` and `∑ g² = ‖f‖² = 1`
    - Constants: `(5√2/4)·n² / (2n²) = 5√2/8` -/
theorem mgg_rayleigh_bound (n : ℕ) (hn : 3 ≤ n)
    (f : EuclideanSpace ℝ (Fin (n * n)))
    (horth : @inner ℝ _ _ f (meanCLM (n * n) f) = 0)
    (hnorm : ‖f‖ = 1) :
    |@inner ℝ _ _ f ((mgg n).walkCLM f)| ≤ 5 * √2 / 8 := by
  -- Setup: define g (reindexed f) and G (DFT magnitudes)
  set g : Fin n → Fin n → ℝ := fun x y =>
    f ⟨x.val * n + y.val, by nlinarith [x.isLt, y.isLt]⟩ with hg_def
  set G : Fin n → Fin n → ℝ := fun α₁ α₂ => ‖dft2d n g α₁ α₂‖ with hG_def
  -- G is nonneg (norms are nonneg)
  have hG : ∀ i j, 0 ≤ G i j := fun i j => norm_nonneg _
  -- Extract ∑ f = 0 from the orthogonality condition
  have hsum_f : ∑ v : Fin (n * n), f v = 0 := by
    have h0 : @inner ℝ _ _ f (meanCLM (n * n) f) =
        ∑ v : Fin (n * n), f v * ((∑ w : Fin (n * n), f w) / ↑(n * n)) := by
      rw [PiLp.inner_apply]
      simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from fun a b => by
        show RCLike.re (b * starRingEnd ℝ a) = b * a
        simp only [RCLike.conj_to_real, RCLike.re_to_real]]
      simp [meanCLM_apply, mul_comm]
    rw [h0] at horth
    set S := ∑ v : Fin (n * n), f v
    have h1 : S * (S / ↑(n * n)) = 0 := by
      convert horth using 1; rw [← Finset.sum_mul]
    have hnn : (0 : ℝ) < ↑(n * n) := Nat.cast_pos.mpr (by positivity)
    have h2 : S ^ 2 / ↑(n * n) = 0 := by
      linarith [show S * (S / ↑(n * n)) = S ^ 2 / ↑(n * n) from by ring]
    rcases div_eq_zero_iff.mp h2 with h3 | h3
    · exact sq_eq_zero_iff.mp h3
    · linarith
  -- Reindexing: ∑ g = ∑ f (bijection (x,y) ↦ x*n+y)
  have hsum_g : ∑ x : Fin n, ∑ y : Fin n, g x y = ∑ v : Fin (n * n), f v := by
    rw [← Fintype.sum_prod_type']
    rw [← finProdFinEquiv.sum_comp (fun v => f v)]
    congr 1; ext ⟨x, y⟩
    show g x y = f.ofLp (finProdFinEquiv (x, y))
    have : finProdFinEquiv (x, y) = ⟨x.val * n + y.val, by nlinarith [x.isLt, y.isLt]⟩ :=
      Fin.ext (by show _ = x.val * n + y.val; unfold finProdFinEquiv; simp; ring)
    rw [this]
  -- G(0,0) = 0 (from mean-zero condition)
  have hG0 : G ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
    show ‖dft2d n g ⟨0, _⟩ ⟨0, _⟩‖ = 0
    rw [norm_eq_zero, dft2d_zero n g (by omega)]
    exact_mod_cast (hsum_g ▸ hsum_f)
  -- Step 1: DFT bridge
  have h_bridge := mgg_dft_bridge n hn f
  -- Step 2: Young's assembly
  have h_young := young_assembly n hn G hG0
  -- Step 3: Chain the inequalities
  have h_chain : |@inner ℝ _ _ f ((mgg n).walkCLM f)| * (2 * (↑n : ℝ) ^ 2) ≤
      5 * √2 / 4 * ∑ α₁ : Fin n, ∑ α₂ : Fin n, G α₁ α₂ ^ 2 :=
    h_bridge.trans h_young
  -- Step 4: G² = Complex.normSq (Parseval compatibility)
  have hG2 : ∑ α₁ : Fin n, ∑ α₂ : Fin n, G α₁ α₂ ^ 2 =
      ∑ α₁ : Fin n, ∑ α₂ : Fin n, Complex.normSq (dft2d n g α₁ α₂) := by
    congr 1; ext α₁; congr 1; ext α₂
    exact Complex.sq_norm (dft2d n g α₁ α₂)
  -- Step 5: Parseval's identity
  rw [hG2, parseval_2d n (by omega) g] at h_chain
  -- Step 6: ∑ g² = ‖f‖² = 1
  have hg_sq : ∑ v₁ : Fin n, ∑ v₂ : Fin n, (g v₁ v₂ : ℝ) ^ 2 = 1 := by
    have h_reindex : ∑ x : Fin n, ∑ y : Fin n, (g x y) ^ 2 =
        ∑ v : Fin (n * n), (f v) ^ 2 := by
      rw [← Fintype.sum_prod_type']
      rw [← finProdFinEquiv.sum_comp (fun v => (f v) ^ 2)]
      congr 1; ext ⟨x, y⟩
      have heq : finProdFinEquiv (x, y) =
          (⟨x.val * n + y.val, by nlinarith [x.isLt, y.isLt]⟩ : Fin (n * n)) :=
        Fin.ext (by show _ = x.val * n + y.val; unfold finProdFinEquiv; simp; ring)
      rw [heq]
    rw [h_reindex]
    have h_norm : ‖f‖ ^ 2 = ∑ v : Fin (n * n), (f v) ^ 2 := by
      rw [sq, ← real_inner_self_eq_norm_mul_norm, PiLp.inner_apply]; simp [sq]
    linarith [show ‖f‖ ^ 2 = 1 from by rw [hnorm]; norm_num]
  -- Step 7: Arithmetic: |inner| * 2n² ≤ (5√2/4) * (n² * 1) = (5√2/8) * (2n²)
  rw [hg_sq, mul_one] at h_chain
  -- h_chain : |inner| * (2 * n²) ≤ (5√2/4) * n²
  have h2n2 : (0 : ℝ) < 2 * (↑n : ℝ) ^ 2 := by positivity
  -- Rewrite RHS: (5√2/4) * n² = (5√2/8) * (2 * n²)
  have h_arith : 5 * √2 / 4 * (↑n : ℝ) ^ 2 = 5 * √2 / 8 * (2 * (↑n : ℝ) ^ 2) := by ring
  rw [h_arith] at h_chain
  exact le_of_mul_le_mul_right h_chain h2n2

