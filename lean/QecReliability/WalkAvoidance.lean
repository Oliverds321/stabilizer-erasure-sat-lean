import QecReliability.RegularWalks

/-! Exact uniform port-walk counting and the spectral avoidance estimate. -/
noncomputable section
namespace QecReliability.ExpanderWalk
open scoped BigOperators
open Classical
namespace PortGraph
variable {m d : ℕ} (G : PortGraph m d)

def visits (G : PortGraph m d) : {k : ℕ} → Fin m → (Fin k → Fin d) → Fin (k + 1) → Fin m
  | 0, v, _ => fun _ => v
  | _ + 1, v, a => Fin.cons v (G.visits (G.neighbor v (a 0)) (Fin.tail a))

def stays (A : Finset (Fin m)) {k : ℕ} (v : Fin m) (a : Fin k → Fin d) : Prop :=
  ∀ j, G.visits v a j ∈ A

theorem stays_zero (A : Finset (Fin m)) (v : Fin m) (a : Fin 0 → Fin d) :
    G.stays A v a ↔ v ∈ A := by simp [stays, visits]

theorem stays_succ (A : Finset (Fin m)) {k : ℕ} (v : Fin m) (a : Fin (k+1) → Fin d) :
    G.stays A v a ↔ v ∈ A ∧ G.stays A (G.neighbor v (a 0)) (Fin.tail a) := by
  simp [stays, visits, Fin.forall_fin_succ]

def survival (G : PortGraph m d) (A : Finset (Fin m)) : ℕ → RVec m
  | 0 => mask A (fun _ => 1)
  | k+1 => G.killed A (G.survival A k)

theorem survival_mask (A : Finset (Fin m)) (k : ℕ) :
    mask A (G.survival A k) = G.survival A k := by
  cases k <;> simp [survival, killed, mask_idem]

theorem survival_succ (A : Finset (Fin m)) (k : ℕ) (v : Fin m) :
    G.survival A (k+1) v = if v ∈ A then
      (∑ i, G.survival A k (G.neighbor v i)) / (d : ℝ) else 0 := by
  simp only [survival, killed, LinearMap.comp_apply, G.survival_mask]
  rfl

theorem walk_mass (A : Finset (Fin m)) (k : ℕ) (v : Fin m) :
    (∑ a : Fin k → Fin d, if G.stays A v a then (1 : ℝ) else 0) =
      (d : ℝ)^k * G.survival A k v := by
  induction k generalizing v with
  | zero => simp [G.stays_zero, survival, mask]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Fin d)).sum_comp
      (fun a => if G.stays A v a then (1 : ℝ) else 0), Fintype.sum_prod_type]
    change (∑ i : Fin d, ∑ a : Fin k → Fin d,
      if G.stays A v (Fin.cons i a) then (1 : ℝ) else 0) = _
    by_cases hv : v ∈ A
    · simp only [G.stays_succ, Fin.cons_zero, Fin.tail_cons, hv,
        true_and, ih, G.survival_succ, if_true, ← Finset.mul_sum]
      have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.degree_pos)
      rw [pow_succ]
      field_simp
    · simp [G.stays_succ, hv, G.survival_succ]

theorem survival_energy {g δ : ℝ} (hg : G.PositiveGap g)
    (A : Finset (Fin m)) (hA : (A.card : ℝ) ≤ (1-δ)*m)
    (hβ : 0 < 1-g*δ) (k : ℕ) :
    energy (G.survival A k) ≤ (1-g*δ)^(2*k) * m := by
  induction k with
  | zero =>
    simpa [survival, energy, dot] using energy_mask_le A (fun _ => (1 : ℝ))
  | succ k ih =>
    calc
      energy (G.survival A (k+1)) ≤ (1-g*δ)^2 * energy (G.survival A k) :=
        G.killed_energy hg A hA hβ _
      _ ≤ (1-g*δ)^2 * ((1-g*δ)^(2*k) * m) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = _ := by rw [← mul_assoc, ← pow_add]; congr 2; omega

theorem survival_sum {g δ : ℝ} (hg : G.PositiveGap g)
    (A : Finset (Fin m)) (hA : (A.card : ℝ) ≤ (1-δ)*m)
    (hβ : 0 < 1-g*δ) (k : ℕ) :
    (∑ v, G.survival A k v) ≤ (m : ℝ) * (1-g*δ)^k := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have he := mul_le_mul_of_nonneg_left (G.survival_energy hg A hA hβ k) hm
  have hs := (sum_sq_le (G.survival A k)).trans he
  have hp : 0 ≤ (m : ℝ) * (1-g*δ)^k := mul_nonneg hm (pow_nonneg hβ.le _)
  have hid : (m : ℝ) * ((1-g*δ)^(2*k)*m) = ((m : ℝ)*(1-g*δ)^k)^2 := by
    rw [mul_comm 2 k, pow_mul]; ring
  rw [hid] at hs
  nlinarith [sq_nonneg ((m : ℝ)*(1-g*δ)^k - ∑ v, G.survival A k v)]

/-- All starts and all independent uniform port choices, counted with multiplicity. -/
theorem avoidance_count {g δ : ℝ} (hg : G.PositiveGap g)
    (A : Finset (Fin m)) (hA : (A.card : ℝ) ≤ (1-δ)*m)
    (hβ : 0 < 1-g*δ) (k : ℕ) :
    ((Finset.univ.filter (fun p : Fin m × (Fin k → Fin d) => G.stays A p.1 p.2)).card : ℝ) ≤
      ((m * d^k : ℕ) : ℝ) * (1-g*δ)^k := by
  classical
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type,
    G.walk_mass, ← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (G.survival_sum hg A hA hβ k)
    (pow_nonneg (Nat.cast_nonneg d) k)
  simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_comm, mul_left_comm] using h

/-- Uniform sampling of a starting vertex and k independent ports. -/
theorem avoidance_fraction {g δ : ℝ} (hg : G.PositiveGap g)
    (A : Finset (Fin m)) (hA : (A.card : ℝ) ≤ (1-δ)*m)
    (hβ : 0 < 1-g*δ) (k : ℕ) :
    ((Finset.univ.filter (fun p : Fin m × (Fin k → Fin d) => G.stays A p.1 p.2)).card : ℝ) /
      ((m*d^k : ℕ) : ℝ) ≤ (1-g*δ)^k := by
  have hM : (0 : ℝ) < (m*d^k : ℕ) := by
    exact_mod_cast Nat.mul_pos G.vertices_pos (pow_pos G.degree_pos k)
  apply (div_le_iff₀ hM).mpr
  simpa only [mul_comm] using G.avoidance_count hg A hA hβ k

end PortGraph
end QecReliability.ExpanderWalk
