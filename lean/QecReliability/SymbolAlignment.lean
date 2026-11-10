import QecReliability.CodeDistance

/-! Whole-symbol repetition and exact strict coding thresholds. No expander
existence or walk separation theorem is postulated here. -/
noncomputable section
namespace QecReliability.CodeHash
open scoped BigOperators

def agreements {M : ℕ} {Alphabet : Type*} [DecidableEq Alphabet] (x y : Fin M → Alphabet) : ℕ :=
  (Finset.univ.filter (fun i => x i = y i)).card

theorem agreements_repeat {M L c : ℕ} {Alphabet : Type*} [DecidableEq Alphabet]
    (rep : Fin L → Fin M) (hf : ∀ i, (Finset.univ.filter (fun j => rep j = i)).card ≤ c)
    (x y : Fin M → Alphabet) : agreements (x ∘ rep) (y ∘ rep) ≤ agreements x y * c := by
  classical
  let S := Finset.univ.filter (fun j => x (rep j) = y (rep j))
  let T := Finset.univ.filter (fun i => x i = y i)
  have hm : Set.MapsTo rep (S : Set (Fin L)) (T : Set (Fin M)) := by intro j hj; simpa [S, T] using hj
  change S.card ≤ T.card * c
  rw [Finset.card_eq_sum_card_fiberwise hm]
  calc
    _ ≤ ∑ _i ∈ T, c := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.card_le_card (by intro j hj; simp only [Finset.mem_filter] at hj ⊢; exact ⟨Finset.mem_univ _, hj.2⟩)).trans (hf i)
    _ = _ := by simp

def cyclicRepeat (M L : ℕ) (hM : 0 < M) : Fin L → Fin M :=
  fun i => ⟨i.val % M, Nat.mod_lt _ hM⟩

theorem cyclicRepeat_fibers {M L c : ℕ} (hM : 0 < M) (hL : L ≤ c * M) (i : Fin M) :
    (Finset.univ.filter (fun j => cyclicRepeat M L hM j = i)).card ≤ c := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter
      (fun j => cyclicRepeat M L hM j = i)) (t := Finset.range c) (fun j => j.val / M)
      (fun j _ => by
        apply Finset.mem_range.mpr
        exact (Nat.div_lt_iff_lt_mul hM).mpr (j.isLt.trans_le hL))
      (by
        intro a ha b hb hab
        have ha' : a.val % M = i.val := congrArg Fin.val (Finset.mem_filter.mp ha).2
        have hb' : b.val % M = i.val := congrArg Fin.val (Finset.mem_filter.mp hb).2
        apply Fin.ext
        have h1 := Nat.mod_add_div a.val M
        have h2 := Nat.mod_add_div b.val M
        change a.val / M = b.val / M at hab
        rw [ha', hab] at h1
        rw [hb'] at h2
        omega)
  simpa using h

theorem aligned_agreements_lt {M L t : ℕ} (hM : 0 < M) (hML : M ≤ L) (hLM : L ≤ 2 * M)
    (α : ℝ) (hα : 0 < α) (x y : Fin M → Word t)
    (hxy : (agreements x y : ℝ) < α * M / 4) :
    (agreements (x ∘ cyclicRepeat M L hM) (y ∘ cyclicRepeat M L hM) : ℝ) < α * L := by
  have h := agreements_repeat (cyclicRepeat M L hM) (cyclicRepeat_fibers hM hLM) x y
  have hr : (agreements (x ∘ cyclicRepeat M L hM) (y ∘ cyclicRepeat M L hM) : ℝ) ≤
      (agreements x y : ℝ) * 2 := by exact_mod_cast h
  have hML' : (M : ℝ) ≤ L := by exact_mod_cast hML
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  nlinarith

def alignedSystem {A : Type*} {M L t k : ℕ}
    (hM : 0 < M) (hML : M ≤ L) (hLM : L ≤ 2 * M)
    (α : ℝ) (hα : 0 < α) (encode : A → Fin M → Word t)
    (hsep : ∀ x y, x ≠ y → (agreements (encode x) (encode y) : ℝ) < α * M / 4)
    (G : Word k →ₗ[F] Word L)
    (hd : ∀ a, a ≠ 0 → α * L ≤ (weight (G a) : ℝ)) : System A L t k :=
  fromDistance (fun a => encode a ∘ cyclicRepeat M L hM) G
    (d := Nat.ceil (α * L))
    (by intro a ha; exact Nat.ceil_le.mpr (hd a ha))
    (by apply Nat.lt_ceil.mpr; have hL : (0 : ℝ) < L := by exact_mod_cast (hM.trans_le hML)
        simpa using mul_pos hα hL)
    (by intro x y hxy; apply Nat.lt_ceil.mpr
        exact aligned_agreements_lt hM hML hLM α hα _ _ (hsep x y hxy))

end QecReliability.CodeHash
