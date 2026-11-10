import Trans.BoundsQH.Lib

/-!
# Trans.BoundsQH.Comb: list combinators with an environment

`Query.mapEnvF` (`mapEnvQ_B`), `Hash.mapEnvF` (`mapEnvH_B`), `Query.flatMapEnvF`
(`flatMapEnvQ_B`), `flatMapF` (`flatMapF_B`) preserve polynomial bounds; `PolyB` forms.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound

theorem lin16 (k c m : ℕ) (hc : 40 ≤ c) : 16 * G k c m + 40 ≤ G (k + 1) c m := by
  have h1 := G_sq k c m
  have h2 := le_G k c m
  nlinarith

theorem env_elem {e a : Ty} (u : e.den) {xs : List a.den} {x : a.den} (h : x ∈ xs) :
    mag (.prod e a) (u, x) ≤ mag (.prod e (.list a)) (u, xs) := by
  have := mag_mem a h; simp only [mag_prod]; omega

theorem env_len {e a : Ty} (u : e.den) (xs : List a.den) :
    xs.length + 1 ≤ mag (.prod e (.list a)) (u, xs) := by
  have := mag_list_len a xs; simp only [mag_prod]; omega

/-- Per-element bounds of a callee bounded by `G k c`, at `G k (c + 40) m`. -/
theorem elem_le {a b : Ty} {F : FnSig a b} {k c : ℕ} (hF : FnB (G k c) F) {x : a.den} {m : ℕ}
    (hx : mag a x ≤ m) : F.cost x + 40 ≤ G k (c + 40) m ∧ F.depth x + 40 ≤ G k (c + 40) m ∧
      F.msize x + 40 ≤ G k (c + 40) m ∧ mag b (F.den x) + 40 ≤ G k (c + 40) m := by
  obtain ⟨h1, h2, h3, h4⟩ := hF x
  have e1 := G_mono (k := k) (c := c) le_rfl le_rfl hx
  have e2 := G_add_c k c 40 m
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem mapEnvQ_B {e a b : Ty} {F : FnSig (.prod e a) b} {k c : ℕ} (hF : FnB (G k c) F) (i : ℕ) :
    FnB (G (k + 2) (c + 40)) (Query.mapEnvF F i) := fun p => by
  obtain ⟨u, xs⟩ := p
  obtain ⟨m, hm⟩ : ∃ m, mag (.prod e (.list a)) (u, xs) = m := ⟨_, rfl⟩
  have hl := env_len u xs
  rw [hm] at hl ⊢
  have hF' := fun x (h : x ∈ xs) => elem_le hF ((env_elem u h).trans hm.le)
  have Y1 := G_succ k (c + 40) m
  have Y2 : 5 * G (k + 1) (c + 40) m + 16 ≤ G (k + 2) (c + 40) m := G_succ (k + 1) (c + 40) m
  have hl0 := le_G k (c + 40) m
  have hcost := comb_le xs (fun x => F.cost (u, x) + 20) (k := k) (c := c + 40)
    (show xs.length ≤ m by omega) (fun x h => by (try dsimp only); have := (hF' x h).1; omega)
    (d := 10) (by omega)
  have hmax := maxOf_bound xs (fun x => F.depth (u, x)) (M := G k (c + 40) m) (fun x h => by (try dsimp only); have := (hF' x h).2.1; omega)
  have hmsz := maxOf_bound xs (fun x => F.msize (u, x)) (M := G k (c + 40) m) (fun x h => by (try dsimp only); have := (hF' x h).2.2.1; omega)
  have hres := mag_map_le xs (fun x => F.den (u, x)) (G k (c + 40) m)
    (fun x h => by (try dsimp only); have := (hF' x h).2.2.2; omega)
  have hres2 := len_mul_le (k := k) (c := c + 40) (show xs.length ≤ m by omega) le_rfl
  have hsz := sz_le (.list b) (xs.map (fun x => F.den (u, x)))
  have hsz2 := sz_le (.prod e (.list a)) (u, xs)
  simp only [Query.mapEnvF_cost, Query.mapEnvF_depth, Query.mapEnvF_msize, Query.mapEnvF_den,
    Query.mapEnvCost, Query.mapEnvDepth, Query.mapEnvMsize]
  refine ⟨by omega, by omega, ?_, by omega⟩
  exact max_le (max_le (by omega) (by omega)) (by omega)

theorem mapEnvH_B {e a b : Ty} {F : FnSig (.prod e a) b} {k c : ℕ} (hF : FnB (G k c) F) (i : ℕ) :
    FnB (G (k + 2) (c + 40)) (Hash.mapEnvF F i) := fun p => by
  obtain ⟨u, xs⟩ := p
  obtain ⟨m, hm⟩ : ∃ m, mag (.prod e (.list a)) (u, xs) = m := ⟨_, rfl⟩
  have hl := env_len u xs
  rw [hm] at hl ⊢
  have hF' := fun x (h : x ∈ xs) => elem_le hF ((env_elem u h).trans hm.le)
  have Y1 := G_succ k (c + 40) m
  have Y2 : 5 * G (k + 1) (c + 40) m + 16 ≤ G (k + 2) (c + 40) m := G_succ (k + 1) (c + 40) m
  have hl0 := le_G k (c + 40) m
  have hcost := comb_le xs (fun x => F.cost (u, x) + 16) (k := k) (c := c + 40)
    (show xs.length ≤ m by omega) (fun x h => by (try dsimp only); have := (hF' x h).1; omega)
    (d := 10) (by omega)
  have hmax := maxOf_bound xs (fun x => F.depth (u, x)) (M := G k (c + 40) m) (fun x h => by (try dsimp only); have := (hF' x h).2.1; omega)
  have hmsz := maxOf_bound xs (fun x => F.msize (u, x)) (M := G k (c + 40) m) (fun x h => by (try dsimp only); have := (hF' x h).2.2.1; omega)
  have hres := mag_map_le xs (fun x => F.den (u, x)) (G k (c + 40) m)
    (fun x h => by (try dsimp only); have := (hF' x h).2.2.2; omega)
  have hres2 := len_mul_le (k := k) (c := c + 40) (show xs.length ≤ m by omega) le_rfl
  have hsz := sz_le (.list b) (xs.map (fun x => F.den (u, x)))
  have hsz2 := sz_le (.prod e (.list a)) (u, xs)
  simp only [Hash.mapEnvF_cost, Hash.mapEnvF_depth, Hash.mapEnvF_msize, Hash.mapEnvF_den]
  refine ⟨by omega, by omega, ?_, by omega⟩
  exact max_le (max_le (by omega) (by omega)) (by omega)

theorem flatMapEnvQ_B {e a b : Ty} {F : FnSig (.prod e a) (.list b)} {k c : ℕ}
    (hF : FnB (G k c) F) (i : ℕ) : FnB (G (k + 3) (c + 40)) (Query.flatMapEnvF F i) := fun p => by
  obtain ⟨u, xs⟩ := p
  obtain ⟨m, hm⟩ : ∃ m, mag (.prod e (.list a)) (u, xs) = m := ⟨_, rfl⟩
  have hl := env_len u xs
  rw [hm] at hl ⊢
  have hF' := fun x (h : x ∈ xs) => elem_le hF ((env_elem u h).trans hm.le)
  have hlenF : ∀ x ∈ xs, (F.den (u, x)).length + 40 ≤ G k (c + 40) m := fun x h => by
    have := (hF' x h).2.2.2; have := mag_list_len b (F.den (u, x)); omega
  have Y1 := G_succ k (c + 40) m
  have Y16 := lin16 k (c + 40) m (by omega)
  have Y2 : 5 * G (k + 1) (c + 40) m + 16 ≤ G (k + 2) (c + 40) m := G_succ (k + 1) (c + 40) m
  have Y3 : 5 * G (k + 2) (c + 40) m + 16 ≤ G (k + 3) (c + 40) m := G_succ (k + 2) (c + 40) m
  have hl0 := le_G k (c + 40) m
  have hl1 := le_G (k + 1) (c + 40) m
  have e2 : G (k + 1 + 1) (c + 40) m = G (k + 2) (c + 40) m := rfl
  have hcost := sum_bound xs (fun x => F.cost (u, x) + 15 * (F.den (u, x)).length + 40)
    (k := k + 1) (c := c + 40) (show xs.length ≤ m by omega)
    (fun x h => by (try dsimp only); have := (hF' x h).1; have := hlenF x h; omega) (d := 10) (by omega)
  have hmax := maxOf_bound xs (fun x => F.depth (u, x) + (F.den (u, x)).length + 1)
    (M := G (k + 1) (c + 40) m) (fun x h => by (try dsimp only); have := (hF' x h).2.1; have := hlenF x h; omega)
  have hmsz := maxOf_bound xs (fun x => F.msize (u, x)) (M := G k (c + 40) m) (fun x h => by (try dsimp only); have := (hF' x h).2.2.1; omega)
  have hres := mag_flatMap_le xs (fun x => F.den (u, x)) (G k (c + 40) m)
    (fun x h => by (try dsimp only); have := (hF' x h).2.2.2; omega)
  have hres2 := len_mul_le (k := k) (c := c + 40) (show xs.length ≤ m by omega) le_rfl
  have hsz := sz_le (.list b) (xs.flatMap (fun x => F.den (u, x)))
  have hsz2 := sz_le (.prod e (.list a)) (u, xs)
  have hm2 : xs.length * G k (c + 40) m ≤ xs.length * (G k (c + 40) m + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [Query.flatMapEnvF_cost, Query.flatMapEnvF_depth, Query.flatMapEnvF_msize,
    Query.flatMapEnvF_den, Query.flatMapEnvCost, Query.flatMapEnvDepth, Query.flatMapEnvMsize]
  refine ⟨by omega, by omega, ?_, by omega⟩
  exact max_le (max_le (by omega) (by omega)) (by omega)

theorem flatMapF_B {a b : Ty} {F : FnSig a (.list b)} {k c : ℕ} (hF : FnB (G k c) F) (i : ℕ) :
    FnB (G (k + 3) (c + 40)) (flatMapF F i) := fun xs => by
  obtain ⟨m, hm⟩ : ∃ m, mag (.list a) xs = m := ⟨_, rfl⟩
  have hl := mag_list_len a xs
  rw [hm] at hl ⊢
  have hF' := fun x (h : x ∈ xs) =>
    elem_le hF (show mag a x ≤ m by have := mag_mem a h; omega)
  have hlenF : ∀ x ∈ xs, (F.den x).length + 40 ≤ G k (c + 40) m := fun x h => by
    have := (hF' x h).2.2.2; have := mag_list_len b (F.den x); omega
  have Y1 := G_succ k (c + 40) m
  have Y16 := lin16 k (c + 40) m (by omega)
  have Y2 : 5 * G (k + 1) (c + 40) m + 16 ≤ G (k + 2) (c + 40) m := G_succ (k + 1) (c + 40) m
  have Y3 : 5 * G (k + 2) (c + 40) m + 16 ≤ G (k + 3) (c + 40) m := G_succ (k + 2) (c + 40) m
  have hl0 := le_G k (c + 40) m
  have hl1 := le_G (k + 1) (c + 40) m
  have e2 : G (k + 1 + 1) (c + 40) m = G (k + 2) (c + 40) m := rfl
  have hcost := sum_bound xs (fun x => F.cost x + 15 * (F.den x).length + 30)
    (k := k + 1) (c := c + 40) (show xs.length ≤ m by omega)
    (fun x h => by (try dsimp only); have := (hF' x h).1; have := hlenF x h; omega) (d := 10) (by omega)
  have hmax := maxOf_bound xs (fun x => F.depth x + (F.den x).length + 1)
    (M := G (k + 1) (c + 40) m) (fun x h => by (try dsimp only); have := (hF' x h).2.1; have := hlenF x h; omega)
  have hmsz := maxOf_bound xs F.msize (M := G k (c + 40) m) (fun x h => by have := (hF' x h).2.2.1; omega)
  have hres := mag_flatMap_le xs F.den (G k (c + 40) m)
    (fun x h => by have := (hF' x h).2.2.2; omega)
  have hres2 := len_mul_le (k := k) (c := c + 40) (show xs.length ≤ m by omega) le_rfl
  have hsz := sz_le (.list b) (xs.flatMap F.den)
  have hm2 : xs.length * G k (c + 40) m ≤ xs.length * (G k (c + 40) m + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [flatMapF_cost, flatMapF_depth, flatMapF_msize, flatMapF_den]
  refine ⟨by omega, by omega, ?_, by omega⟩
  exact max_le (by omega) (by omega)

theorem mapEnvQ_P {e a b : Ty} {F : FnSig (.prod e a) b} (hF : PolyB F) (i : ℕ) :
    PolyB (Query.mapEnvF F i) := by obtain ⟨k, c, h⟩ := hF; exact ⟨_, _, mapEnvQ_B h i⟩
theorem mapEnvH_P {e a b : Ty} {F : FnSig (.prod e a) b} (hF : PolyB F) (i : ℕ) :
    PolyB (Hash.mapEnvF F i) := by obtain ⟨k, c, h⟩ := hF; exact ⟨_, _, mapEnvH_B h i⟩
theorem flatMapEnvQ_P {e a b : Ty} {F : FnSig (.prod e a) (.list b)} (hF : PolyB F) (i : ℕ) :
    PolyB (Query.flatMapEnvF F i) := by obtain ⟨k, c, h⟩ := hF; exact ⟨_, _, flatMapEnvQ_B h i⟩
theorem mapF_P {a b : Ty} {F : FnSig a b} (hF : PolyB F) (i : ℕ) : PolyB (mapF F i) := by
  obtain ⟨k, c, h⟩ := hF; exact ⟨_, _, mapF_B h i⟩
theorem filterF_P {a : Ty} {F : FnSig a .bool} (hF : PolyB F) (i : ℕ) : PolyB (filterF F i) := by
  obtain ⟨k, c, h⟩ := hF; exact ⟨_, _, filterF_B h i⟩
theorem flatMapF_P {a b : Ty} {F : FnSig a (.list b)} (hF : PolyB F) (i : ℕ) :
    PolyB (flatMapF F i) := by obtain ⟨k, c, h⟩ := hF; exact ⟨_, _, flatMapF_B h i⟩

end QecReliability.Trans.BoundsQH
