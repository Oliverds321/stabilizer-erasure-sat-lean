import QecReliability.Latent
import Mathlib.Data.Fintype.Sigma

/-! The adjacent-layer coupling is proved by inserting/deleting its marked coordinate. -/

noncomputable section

namespace QecReliability

open scoped BigOperators

abbrev WeightLayer (r j : ℕ) := {b : Causes r // b.card = j}
abbrev UpEdge (r j : ℕ) := {bi : Causes r × Fin r // bi.1.card = j ∧ bi.2 ∉ bi.1}
abbrev DownEdge (r j : ℕ) := {bi : Causes r × Fin r // bi.1.card = j + 1 ∧ bi.2 ∈ bi.1}

def insertEraseEquiv (r j : ℕ) : UpEdge r j ≃ DownEdge r j where
  toFun bi := ⟨(insert bi.1.2 bi.1.1, bi.1.2), by
    simp [Finset.card_insert_of_notMem bi.2.2, bi.2.1]⟩
  invFun bi := ⟨(bi.1.1.erase bi.1.2, bi.1.2), by
    simp [Finset.card_erase_of_mem bi.2.2, bi.2.1]⟩
  left_inv bi := by
    apply Subtype.ext
    apply Prod.ext
    · exact Finset.erase_insert bi.2.2
    · rfl
  right_inv bi := by
    apply Subtype.ext
    apply Prod.ext
    · exact Finset.insert_erase bi.2.2
    · rfl

def upSigmaEquiv (r j : ℕ) :
    UpEdge r j ≃ (Σ b : WeightLayer r j, {i : Fin r // i ∉ b.val}) where
  toFun bi := ⟨⟨bi.1.1, bi.2.1⟩, ⟨bi.1.2, bi.2.2⟩⟩
  invFun bi := ⟨(bi.1.val, bi.2.val), bi.1.property, bi.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def downSigmaEquiv (r j : ℕ) :
    DownEdge r j ≃ (Σ b : WeightLayer r (j + 1), {i : Fin r // i ∈ b.val}) where
  toFun bi := ⟨⟨bi.1.1, bi.2.1⟩, ⟨bi.1.2, bi.2.2⟩⟩
  invFun bi := ⟨(bi.1.val, bi.2.val), bi.1.property, bi.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_up_edges (r j : ℕ) (f : Causes r → ℝ) :
    (∑ bi : UpEdge r j, f bi.val.1) = (r - j : ℕ) * ∑ b : WeightLayer r j, f b := by
  classical
  have he : (∑ bi : UpEdge r j, f bi.val.1) =
      ∑ bi : (Σ b : WeightLayer r j, {i : Fin r // i ∉ b.val}), f bi.1 :=
    Fintype.sum_equiv (upSigmaEquiv r j) (fun bi => f bi.val.1)
      (fun bi => f bi.1) (fun _ => rfl)
  rw [he, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hc : Fintype.card {i : Fin r // i ∉ b.val} = r - j := by
    rw [Fintype.card_of_subtype b.valᶜ (by intro i; simp), Finset.card_compl,
      Fintype.card_fin, b.property]
  rw [hc]

theorem sum_down_edges (r j : ℕ) (f : Causes r → ℝ) :
    (∑ bi : DownEdge r j, f bi.val.1) = (j + 1 : ℕ) * ∑ b : WeightLayer r (j + 1), f b := by
  classical
  have he : (∑ bi : DownEdge r j, f bi.val.1) =
      ∑ bi : (Σ b : WeightLayer r (j + 1), {i : Fin r // i ∈ b.val}), f bi.1 :=
    Fintype.sum_equiv (downSigmaEquiv r j) (fun bi => f bi.val.1)
      (fun bi => f bi.1) (fun _ => rfl)
  rw [he, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hc : Fintype.card {i : Fin r // i ∈ b.val} = j + 1 := by
    rw [Fintype.card_of_subtype b.val (by intro i; rfl), b.property]
  rw [hc]

theorem weightLayer_card (r j : ℕ) : Nat.card (WeightLayer r j) = r.choose j := by
  classical
  rw [Nat.card_eq_fintype_card,
    Fintype.card_of_subtype (Finset.powersetCard j Finset.univ)
      (by intro b; simp [Finset.mem_powersetCard]),
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Exact balance of the marked-coordinate coupling, including empty layers. -/
theorem adjacent_layer_balance (r j : ℕ) :
    ((r - j : ℕ) : ℝ) * (r.choose j : ℝ) =
      ((j + 1 : ℕ) : ℝ) * (r.choose (j + 1) : ℝ) := by
  classical
  have h := Fintype.sum_equiv (insertEraseEquiv r j)
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => rfl)
  rw [sum_up_edges r j (fun _ => 1), sum_down_edges r j (fun _ => 1)] at h
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card, weightLayer_card] using h

theorem adjacent_layer_sum_antitone {r j : ℕ} (f : Causes r → ℝ)
    (hanti : ∀ a b, a ⊆ b → f b ≤ f a) :
    ((j + 1 : ℕ) : ℝ) * (∑ b : WeightLayer r (j + 1), f b) ≤
      ((r - j : ℕ) : ℝ) * (∑ b : WeightLayer r j, f b) := by
  classical
  rw [← sum_down_edges, ← sum_up_edges]
  rw [← Fintype.sum_equiv (insertEraseEquiv r j)
    (fun bi => f (insert bi.val.2 bi.val.1)) (fun bi => f bi.val.1) (fun _ => rfl)]
  apply Finset.sum_le_sum
  intro bi _
  exact hanti _ _ (Finset.subset_insert _ _)

theorem adjacent_layer_mean_antitone {r j : ℕ} (hj : j < r) (f : Causes r → ℝ)
    (hanti : ∀ a b, a ⊆ b → f b ≤ f a) :
    (∑ b : WeightLayer r (j + 1), f b) / (r.choose (j + 1) : ℝ) ≤
      (∑ b : WeightLayer r j, f b) / (r.choose j : ℝ) := by
  have h0 : 0 < (r.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj.le
  have h1 : 0 < (r.choose (j + 1) : ℝ) := by exact_mod_cast Nat.choose_pos hj
  have hstep : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have hbalance := adjacent_layer_balance r j
  have hsum := adjacent_layer_sum_antitone (j := j) f hanti
  apply (div_le_div_iff₀ h1 h0).mpr
  have hmul := mul_le_mul_of_nonneg_right hsum h0.le
  have he : ((r - j : ℕ) : ℝ) * (∑ b : WeightLayer r j, f b) * (r.choose j : ℝ) =
      ((j + 1 : ℕ) : ℝ) * (∑ b : WeightLayer r j, f b) * (r.choose (j + 1) : ℝ) := by
    nlinarith [congrArg (fun a : ℝ => a * ∑ b : WeightLayer r j, f b) hbalance]
  rw [he] at hmul
  nlinarith

theorem layerAverage_eq_mean {r : ℕ} {E : Type*} (C : Causes r → E)
    (f : E → ℝ) (j : Fin (r + 1)) :
    layerAverage C f j = (∑ b : WeightLayer r j.val, f (C b)) / (r.choose j.val : ℝ) := by
  classical
  unfold layerAverage
  congr 1
  let e : {b : Causes r // hammingLayer b = j} ≃ WeightLayer r j.val :=
    Equiv.subtypeEquivRight (fun _ => by simp [hammingLayer, Fin.ext_iff])
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem layerAverage_antitone {r : ℕ} {E : Type*} (C : Causes r → E)
    (f : E → ℝ) (hanti : ∀ a b, a ⊆ b → f (C b) ≤ f (C a)) :
    Antitone (layerAverage C f) := by
  intro i k hik
  rw [layerAverage_eq_mean, layerAverage_eq_mean]
  have hsteps : ∀ j < r,
      (∑ b : WeightLayer r (j + 1), f (C b)) / (r.choose (j + 1) : ℝ) ≤
        (∑ b : WeightLayer r j, f (C b)) / (r.choose j : ℝ) :=
    fun j hj => adjacent_layer_mean_antitone hj (fun b => f (C b)) hanti
  have hall : ∀ a b, a ≤ b → b ≤ r →
      (∑ u : WeightLayer r b, f (C u)) / (r.choose b : ℝ) ≤
        (∑ u : WeightLayer r a, f (C u)) / (r.choose a : ℝ) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ b hab ih =>
      intro hbr
      exact le_trans (hsteps b (by omega)) (ih (by omega))
  exact hall i.val k.val hik (Nat.le_of_lt_succ k.isLt)

end QecReliability
