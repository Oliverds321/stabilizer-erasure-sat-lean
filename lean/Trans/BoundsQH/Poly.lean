import Trans.Query.Bounds
import FL.Lib.List

/-!
# Trans.BoundsQH.Poly: polynomial bounding functions and their closure properties

* `G k c m = B0^[k] (m + c)` with `B0 m = 25 (m+4)^2` (`Trans/Query/Bounds.lean`): a polynomial
  of degree `2^k` in `m` (`G_poly : G k c m + 4 ≤ 26^(2^k-1) (m+c+4)^(2^k)`).
* Closure: `G_mono`, `G_succ`, `G_add`, `G_mul`, `G_comp`, `G_iter`.
* `PolyB F := ∃ k c, FnB (G k c) F`: cost, depth, msize and result magnitude of `F` are
  bounded by a fixed polynomial of the magnitude of the argument.
* `Tm.CallsP`: every callee of a term is `PolyB`; `polyB_of_body`: a function whose bounds
  are its body's (e.g. `FnSig.exact`, `exactSig`, `bodySig`) is `PolyB` when its callees are.
* `chain_bound`, `tree_bound`: linear and binary recursions.
* List magnitude lemmas.
-/

set_option autoImplicit false

/-- Simp set of `PolyB` facts (used to discharge `Tm.CallsP` goals). -/
register_simp_attr polyB

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.Trans.Query.Bound

/-! ## The bounding functions -/

/-- `G k c m = B0^[k] (m + c)`. -/
def G (k c m : ℕ) : ℕ := B0^[k] (m + c)

theorem B0_ge (y : ℕ) : 5 * y + 16 ≤ B0 y := adm_B0.big y

theorem B0_sq (y : ℕ) : (y + 1) * (y + 1) + 16 ≤ B0 y := by unfold B0; nlinarith

theorem G_mono {k c m k' c' m' : ℕ} (hk : k ≤ k') (hc : c ≤ c') (hm : m ≤ m') :
    G k c m ≤ G k' c' m' :=
  (adm_B0.iter_mono k (show m + c ≤ m' + c' by omega)).trans (adm_B0.lift hk _)

theorem G_monotone (k c : ℕ) : Monotone (G k c) := fun _ _ h => G_mono le_rfl le_rfl h

theorem le_G (k c m : ℕ) : m + c ≤ G k c m := adm_B0.le_iter k _

theorem G_zero (c m : ℕ) : G 0 c m = m + c := rfl

theorem G_succ (k c m : ℕ) : 5 * G k c m + 16 ≤ G (k + 1) c m := adm_B0.succ_iter k _

theorem G_sq (k c m : ℕ) : (G k c m + 1) * (G k c m + 1) + 16 ≤ G (k + 1) c m := by
  unfold G; rw [Function.iterate_succ_apply']; exact B0_sq _

theorem G_comp_same (k j c m : ℕ) : G k c (G j c m) ≤ G (k + j + 1) c m := by
  unfold G
  have h1 : B0^[j] (m + c) + c ≤ B0^[j + 1] (m + c) := by
    rw [Function.iterate_succ_apply']
    have h2 := le_G j c m
    unfold G at h2
    have h3 := B0_ge (B0^[j] (m + c))
    omega
  calc B0^[k] (B0^[j] (m + c) + c) ≤ B0^[k] (B0^[j + 1] (m + c)) := adm_B0.iter_mono k h1
    _ = B0^[k + j + 1] (m + c) := by rw [← Function.iterate_add_apply, Nat.add_assoc]

theorem G_comp (k c j d m : ℕ) : G k c (G j d m) ≤ G (k + j + 1) (c + d) m :=
  (G_mono le_rfl (Nat.le_add_right c d) (G_mono le_rfl (Nat.le_add_left d c) le_rfl)).trans
    (G_comp_same k j (c + d) m)

theorem G_iter (K C : ℕ) : ∀ n x, (G K C)^[n] x ≤ G (n * (K + 1)) C x
  | 0, x => by simp only [Function.iterate_zero, id, Nat.zero_mul, G_zero]; omega
  | n + 1, x => by
    rw [Function.iterate_succ_apply']
    calc G K C ((G K C)^[n] x) ≤ G K C (G (n * (K + 1)) C x) :=
          G_mono le_rfl le_rfl (G_iter K C n x)
      _ ≤ G (K + n * (K + 1) + 1) C x := G_comp_same _ _ _ _
      _ = G ((n + 1) * (K + 1)) C x := by congr 1; ring

theorem G_shift (k c d m : ℕ) : G k c (m + d) = G k (c + d) m := by
  unfold G; congr 1; omega

theorem adm_G {k : ℕ} (hk : 1 ≤ k) (c : ℕ) : Adm (G k c) := adm_B0.iterShift hk c

theorem B0_add (y d : ℕ) : B0 y + d ≤ B0 (y + d) := by
  unfold B0
  have h : (y + 4) ^ 2 + d ≤ (y + d + 4) ^ 2 := by
    have : (y + d + 4) ^ 2 = (y + 4) ^ 2 + d * (2 * y + 8 + d) := by ring
    rw [this]; have : d ≤ d * (2 * y + 8 + d) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  omega

theorem B0_iter_add (k : ℕ) : ∀ y d, B0^[k] y + d ≤ B0^[k] (y + d) := by
  induction k with
  | zero => intro y d; simp
  | succ k ih =>
    intro y d
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact (ih (B0 y) d).trans (adm_B0.iter_mono k (B0_add y d))

/-- Adding a constant outside: `G k c m + d ≤ G k (c + d) m`. -/
theorem G_add_c (k c d m : ℕ) : G k c m + d ≤ G k (c + d) m := by
  unfold G; rw [← Nat.add_assoc]; exact B0_iter_add k _ d

/-! ### Arithmetic on bounds -/

section Arith
variable {k c m a b : ℕ}

theorem G_le_of {k' c' : ℕ} (h : a ≤ G k c m) (hk : k ≤ k') (hc : c ≤ c') : a ≤ G k' c' m :=
  h.trans (G_mono hk hc le_rfl)

theorem G_add (ha : a ≤ G k c m) (hb : b ≤ G k c m) : a + b ≤ G (k + 1) c m := by
  have := G_succ k c m; omega

theorem G_mul (ha : a ≤ G k c m) (hb : b ≤ G k c m) : a * b ≤ G (k + 1) c m := by
  have h1 := G_sq k c m
  have h2 : a * b ≤ (G k c m + 1) * (G k c m + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem G_const (ha : a ≤ c) : a ≤ G k c m := by have := le_G k c m; omega

theorem G_arg (ha : a ≤ m) : a ≤ G k c m := by have := le_G k c m; omega

theorem G_arg_add (ha : a ≤ m + c) : a ≤ G k c m := by have := le_G k c m; omega

end Arith

/-- `A (m+1)^2 + A ≤ G 2 A m`: quadratic bounds. -/
theorem quad_le (A m : ℕ) : A * ((m + 1) * (m + 1)) + A ≤ G 2 A m := by
  have h1 : (G 1 A m + 1) * (G 1 A m + 1) + 16 ≤ G 2 A m := G_sq 1 A m
  have h0 : (m + A + 1) * (m + A + 1) + 16 ≤ G 1 A m := by
    have := G_sq 0 A m; rwa [G_zero] at this
  have h2 : (m + 1) * (m + 1) ≤ (m + A + 1) * (m + A + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : A + 1 ≤ (m + A + 1) * (m + A + 1) := by nlinarith
  have h4 : A * ((m + 1) * (m + 1)) + A ≤
      ((m + A + 1) * (m + A + 1)) * ((m + A + 1) * (m + A + 1)) := by nlinarith
  have h5 : ((m + A + 1) * (m + A + 1)) * ((m + A + 1) * (m + A + 1)) ≤
      (G 1 A m + 1) * (G 1 A m + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Linear bounds. -/
theorem lin_le (A m : ℕ) : A * (m + 1) + A ≤ G 2 A m := by
  have := quad_le A m
  have : A * (m + 1) ≤ A * ((m + 1) * (m + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
  omega

/-! ## Polynomially bounded signatures -/

/-- `F` is polynomially bounded: one fixed `G k c` bounds cost, depth, msize and the
magnitude of the result in terms of the magnitude of the argument. -/
def PolyB {a b : Ty} (F : FnSig a b) : Prop := ∃ k c, FnB (G k c) F

theorem FnB.liftG {a b : Ty} {F : FnSig a b} {k c k' c' : ℕ} (h : FnB (G k c) F) (hk : k ≤ k')
    (hc : c ≤ c') : FnB (G k' c') F :=
  FnB.mono (fun _ => G_mono hk hc le_rfl) h

theorem FnB.polyB {a b : Ty} {F : FnSig a b} {k c : ℕ} (h : FnB (G k c) F) : PolyB F := ⟨k, c, h⟩

/-- Building `FnB (G 2 A)` from quadratic bounds. -/
theorem fnB_quad {a b : Ty} (F : FnSig a b) (A : ℕ)
    (h : ∀ y, F.cost y ≤ A * ((mag a y + 1) * (mag a y + 1)) ∧
      F.depth y ≤ A * ((mag a y + 1) * (mag a y + 1)) ∧
      F.msize y ≤ A * ((mag a y + 1) * (mag a y + 1)) ∧
      mag b (F.den y) ≤ A * ((mag a y + 1) * (mag a y + 1))) : FnB (G 2 A) F := fun y => by
  obtain ⟨h1, h2, h3, h4⟩ := h y
  have := quad_le A (mag a y)
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Building `FnB` from bounds by an arbitrary `G k c`-expression of the magnitude. -/
theorem fnB_of {a b : Ty} (F : FnSig a b) (k c : ℕ)
    (h : ∀ y, F.cost y ≤ G k c (mag a y) ∧ F.depth y ≤ G k c (mag a y) ∧
      F.msize y ≤ G k c (mag a y) ∧ mag b (F.den y) ≤ G k c (mag a y)) : FnB (G k c) F := h

/-! ## Terms whose callees are polynomially bounded -/

/-- Every callee is `PolyB`. -/
def Tm.CallsP {Γ : List Ty} {t : Ty} : Tm Γ t → Prop
  | .pair a b => (Tm.CallsP a) ∧ (Tm.CallsP b)
  | .fst p => (Tm.CallsP p)
  | .snd p => (Tm.CallsP p)
  | .ite c x y => (Tm.CallsP c) ∧ (Tm.CallsP x) ∧ (Tm.CallsP y)
  | .lcons h tl => (Tm.CallsP h) ∧ (Tm.CallsP tl)
  | .lcase s e₁ e₂ => (Tm.CallsP s) ∧ (Tm.CallsP e₁) ∧ (Tm.CallsP e₂)
  | .ncase s e₁ e₂ => (Tm.CallsP s) ∧ (Tm.CallsP e₁) ∧ (Tm.CallsP e₂)
  | .bit b n => (Tm.CallsP b) ∧ (Tm.CallsP n)
  | .letE a b => (Tm.CallsP a) ∧ (Tm.CallsP b)
  | .app F a => PolyB F ∧ (Tm.CallsP a)
  | _ => True

theorem callsB_lift {Γ : List Ty} {t : Ty} {tm : Tm Γ t} {k c k' c' : ℕ}
    (h : Tm.CallsB (G k c) tm) (hk : k ≤ k') (hc : c ≤ c') : Tm.CallsB (G k' c') tm :=
  Tm.CallsB.mono (fun _ => G_mono hk hc le_rfl) tm h

theorem Tm.CallsP.toB {Γ : List Ty} {t : Ty} (tm : Tm Γ t) (h : Tm.CallsP tm) :
    ∃ K C, Tm.CallsB (G K C) tm := by
  induction tm with
  | pair a b iha ihb =>
    obtain ⟨K1, C1, h1⟩ := iha h.1
    obtain ⟨K2, C2, h2⟩ := ihb h.2
    exact ⟨K1 + K2, C1 + C2, callsB_lift h1 (by omega) (by omega),
      callsB_lift h2 (by omega) (by omega)⟩
  | fst p ih => exact ih h
  | snd p ih => exact ih h
  | ite c x y ihc ihx ihy =>
    obtain ⟨K1, C1, h1⟩ := ihc h.1
    obtain ⟨K2, C2, h2⟩ := ihx h.2.1
    obtain ⟨K3, C3, h3⟩ := ihy h.2.2
    exact ⟨K1 + K2 + K3, C1 + C2 + C3, callsB_lift h1 (by omega) (by omega),
      callsB_lift h2 (by omega) (by omega), callsB_lift h3 (by omega) (by omega)⟩
  | lcons a b iha ihb =>
    obtain ⟨K1, C1, h1⟩ := iha h.1
    obtain ⟨K2, C2, h2⟩ := ihb h.2
    exact ⟨K1 + K2, C1 + C2, callsB_lift h1 (by omega) (by omega),
      callsB_lift h2 (by omega) (by omega)⟩
  | lcase s e₁ e₂ ihs ih₁ ih₂ =>
    obtain ⟨K1, C1, h1⟩ := ihs h.1
    obtain ⟨K2, C2, h2⟩ := ih₁ h.2.1
    obtain ⟨K3, C3, h3⟩ := ih₂ h.2.2
    exact ⟨K1 + K2 + K3, C1 + C2 + C3, callsB_lift h1 (by omega) (by omega),
      callsB_lift h2 (by omega) (by omega), callsB_lift h3 (by omega) (by omega)⟩
  | ncase s e₁ e₂ ihs ih₁ ih₂ =>
    obtain ⟨K1, C1, h1⟩ := ihs h.1
    obtain ⟨K2, C2, h2⟩ := ih₁ h.2.1
    obtain ⟨K3, C3, h3⟩ := ih₂ h.2.2
    exact ⟨K1 + K2 + K3, C1 + C2 + C3, callsB_lift h1 (by omega) (by omega),
      callsB_lift h2 (by omega) (by omega), callsB_lift h3 (by omega) (by omega)⟩
  | bit a b iha ihb =>
    obtain ⟨K1, C1, h1⟩ := iha h.1
    obtain ⟨K2, C2, h2⟩ := ihb h.2
    exact ⟨K1 + K2, C1 + C2, callsB_lift h1 (by omega) (by omega),
      callsB_lift h2 (by omega) (by omega)⟩
  | letE a b iha ihb =>
    obtain ⟨K1, C1, h1⟩ := iha h.1
    obtain ⟨K2, C2, h2⟩ := ihb h.2
    exact ⟨K1 + K2, C1 + C2, callsB_lift h1 (by omega) (by omega),
      callsB_lift h2 (by omega) (by omega)⟩
  | app F a iha =>
    obtain ⟨k, c, hF⟩ := h.1
    obtain ⟨K1, C1, h1⟩ := iha h.2
    exact ⟨k + K1, c + C1, FnB.liftG hF (by omega) (by omega), callsB_lift h1 (by omega) (by omega)⟩
  | _ => exact ⟨0, 0, trivial⟩

/-- **Signatures with body bounds** (`FnSig.exact`, `exactSig`, `bodySig`, …) are `PolyB` when
their callees are. -/
theorem polyB_of_body {a b : Ty} (F : FnSig a b) (body : Tm [a] b)
    (hcost : ∀ x, F.cost x ≤ body.cost (Env.one x) + 2)
    (hdepth : ∀ x, F.depth x ≤ body.depth (Env.one x) + 1)
    (hmsize : ∀ x, F.msize x ≤ body.msize (Env.one x))
    (hden : ∀ x, F.den x = body.den (Env.one x)) (hc : Tm.CallsP body) : PolyB F := by
  obtain ⟨K, C, hK⟩ := hc.toB body
  have hK' : Tm.CallsB (G (K + 1) C) body := callsB_lift hK (by omega) le_rfl
  have hb := body_bounded (adm_G (k := K + 1) (by omega) C) F body hcost hdepth hmsize hden hK'
    (Tm.litc body) le_rfl
  refine ⟨(Tm.nodes body + 1) * (K + 1 + 1), C + Tm.litc body, FnB.mono (fun m => ?_) hb⟩
  rw [← G_shift]
  exact G_iter _ _ _ _

/-! ## Recursions -/

/-- **Linear recursion**: if `f x ≤ B (μ x)` or `f x ≤ B (μ x) + f y` for some `y` of smaller
length `ℓ` and no larger `μ`, then `f x ≤ (ℓ x + 1) · B (μ x)`. -/
theorem chain_bound {α : Type} (ℓ μ f : α → ℕ) (B : ℕ → ℕ) (hB : Monotone B)
    (h : ∀ x, f x ≤ B (μ x) ∨ ∃ y, ℓ y < ℓ x ∧ μ y ≤ μ x ∧ f x ≤ B (μ x) + f y) :
    ∀ x, f x ≤ (ℓ x + 1) * B (μ x) := by
  intro x
  induction hx : ℓ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rcases h x with h1 | ⟨y, hy, hμ, h2⟩
    · have : B (μ x) ≤ (n + 1) * B (μ x) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    · have h3 := ih (ℓ y) (by omega) y rfl
      have h4 : (ℓ y + 1) * B (μ y) ≤ n * B (μ x) :=
        Nat.mul_le_mul (by omega) (hB hμ)
      have h5 : (n + 1) * B (μ x) = n * B (μ x) + B (μ x) := Nat.succ_mul n _
      omega

/-- **Binary recursion** of height `ℓ`: `f x ≤ 2^(ℓ x + 1) · B (μ x)`. -/
theorem tree_bound {α : Type} (ℓ μ f : α → ℕ) (B : ℕ → ℕ) (hB : Monotone B)
    (h : ∀ x, f x ≤ B (μ x) ∨ ∃ y z, ℓ y < ℓ x ∧ ℓ z < ℓ x ∧ μ y ≤ μ x ∧ μ z ≤ μ x ∧
      ℓ y + 1 = ℓ x ∧ ℓ z + 1 = ℓ x ∧ f x ≤ B (μ x) + f y + f z) :
    ∀ x, f x ≤ 2 ^ (ℓ x + 1) * B (μ x) := by
  have key : ∀ n x, ℓ x = n → ∀ M, μ x ≤ M → f x + B M ≤ 2 ^ (n + 1) * B M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx M hM
      have hBM := hB hM
      rcases h x with h1 | ⟨y, z, hy, hz, hμy, hμz, ey, ez, h2⟩
      · have hP : 2 ≤ 2 ^ (n + 1) := by
          have := Nat.one_le_two_pow (n := n); rw [pow_succ]; omega
        have : 2 * B M ≤ 2 ^ (n + 1) * B M := Nat.mul_le_mul_right _ hP
        generalize 2 ^ (n + 1) = P at *
        omega
      · have h3 := ih (ℓ y) (by omega) y rfl M (le_trans hμy hM)
        have h4 := ih (ℓ z) (by omega) z rfl M (le_trans hμz hM)
        have hy' : ℓ y + 1 = n := by omega
        have hz' : ℓ z + 1 = n := by omega
        rw [hy'] at h3
        rw [hz'] at h4
        rw [pow_succ]
        generalize 2 ^ n = P at *
        have : P * 2 * B M = P * B M + P * B M := by ring
        omega
  intro x
  have := key (ℓ x) x rfl (μ x) le_rfl
  omega

/-! ## Magnitudes of lists -/

section Lists
variable (t : Ty)

theorem mag_list_len (xs : List t.den) : xs.length + 1 ≤ mag (.list t) xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [mag_cons, List.length_cons]; omega

theorem mag_mem {xs : List t.den} {x : t.den} (h : x ∈ xs) : mag t x + 2 ≤ mag (.list t) xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [mag_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · have := mag_list_len t ys; omega
    · have := ih h'; omega

theorem mag_append (xs ys : List t.den) :
    mag (.list t) (xs ++ ys) + 1 = mag (.list t) xs + mag (.list t) ys := by
  induction xs with
  | nil => simp; omega
  | cons x xs ih => simp only [List.cons_append, mag_cons]; omega

theorem mag_append_le (xs ys : List t.den) :
    mag (.list t) (xs ++ ys) ≤ mag (.list t) xs + mag (.list t) ys := by
  have := mag_append t xs ys; omega

theorem mag_list_le (xs : List t.den) (M : ℕ) (h : ∀ x ∈ xs, mag t x ≤ M) :
    mag (.list t) xs ≤ xs.length * (M + 1) + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    simp only [mag_cons, List.length_cons, Nat.succ_mul]
    omega

theorem mag_sublist {xs ys : List t.den} (h : xs.Sublist ys) :
    mag (.list t) xs ≤ mag (.list t) ys := by
  induction h with
  | slnil => exact le_rfl
  | cons a _ ih => simp only [mag_cons]; omega
  | cons_cons a _ ih => simp only [mag_cons]; omega

theorem mag_filter (xs : List t.den) (p : t.den → Bool) :
    mag (.list t) (xs.filter p) ≤ mag (.list t) xs := mag_sublist t List.filter_sublist

theorem mag_take (xs : List t.den) (n : ℕ) : mag (.list t) (xs.take n) ≤ mag (.list t) xs :=
  mag_sublist t (List.take_sublist _ _)

theorem mag_drop (xs : List t.den) (n : ℕ) : mag (.list t) (xs.drop n) ≤ mag (.list t) xs :=
  mag_sublist t (List.drop_sublist _ _)

theorem mag_reverse (xs : List t.den) : mag (.list t) xs.reverse = mag (.list t) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have := mag_append t xs.reverse [x]
    simp only [List.reverse_cons, mag_cons, mag_nil] at this ⊢
    omega

theorem mag_replicate (n : ℕ) (x : t.den) :
    mag (.list t) (List.replicate n x) = n * (mag t x + 1) + 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, mag_cons, ih, Nat.succ_mul]; omega

theorem mag_getD (xs : List t.den) (i : ℕ) (d : t.den) :
    mag t (xs.getD i d) ≤ mag (.list t) xs + mag t d := by
  induction xs generalizing i with
  | nil => simp
  | cons y ys ih =>
    cases i with
    | zero => simp only [List.getD_cons_zero, mag_cons]; omega
    | succ i => have := ih i; simp only [List.getD_cons_succ, mag_cons]; omega

end Lists

theorem sum_le_len_mul {α : Type} (xs : List α) (f : α → ℕ) (M : ℕ) (h : ∀ x ∈ xs, f x ≤ M) :
    (xs.map f).sum ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem mag_map_le {a b : Ty} (xs : List a.den) (f : a.den → b.den) (M : ℕ)
    (h : ∀ x ∈ xs, mag b (f x) ≤ M) : mag (.list b) (xs.map f) ≤ xs.length * (M + 1) + 1 := by
  have := mag_list_le b (xs.map f) M (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact h x hx)
  simpa using this

theorem mag_flatMap_le {a b : Ty} (xs : List a.den) (f : a.den → List b.den) (M : ℕ)
    (h : ∀ x ∈ xs, mag (.list b) (f x) ≤ M) :
    mag (.list b) (xs.flatMap f) ≤ xs.length * M + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    have := mag_append b (f x) (xs.flatMap f)
    simp only [List.flatMap_cons, List.length_cons, Nat.succ_mul]
    omega

theorem maxOf_le' {α : Type} (f : α → ℕ) (xs : List α) (M : ℕ) (h : ∀ x ∈ xs, f x ≤ M) :
    QecReliability.FL.Lib.maxOf f xs ≤ M := QecReliability.FL.Lib.maxOf_le f xs M h

/-- A sum of `≤ m` terms, each `≤ G k c m`, plus a constant `d ≤ c`. -/
theorem sum_bound {α : Type} (xs : List α) (f : α → ℕ) {k c m : ℕ} (hlen : xs.length ≤ m)
    (h : ∀ x ∈ xs, f x ≤ G k c m) {d : ℕ} (hd : d ≤ c) : (xs.map f).sum + d ≤ G (k + 1) c m := by
  have h1 := sum_le_len_mul xs f _ h
  have h2 : xs.length * G k c m ≤ G k c m * G k c m :=
    Nat.mul_le_mul_right _ (hlen.trans (by have := le_G k c m; omega))
  have h3 := G_sq k c m
  have h4 := le_G k c m
  have h5 : (G k c m + 1) * (G k c m + 1) = G k c m * G k c m + 2 * G k c m + 1 := by ring
  omega

theorem maxOf_bound {α : Type} (xs : List α) (f : α → ℕ) {M : ℕ} (h : ∀ x ∈ xs, f x ≤ M) :
    QecReliability.FL.Lib.maxOf f xs ≤ M := QecReliability.FL.Lib.maxOf_le f xs M h

/-! ## Encoded sizes -/

theorem sz_le (t : Ty) (x : t.den) : (t.enc x).size ≤ 5 * mag t x + 1 := size_le_mag t x

theorem natSize_le (n : ℕ) : n.size ≤ n := NatSize.size_le_self n

end QecReliability.Trans.BoundsQH
