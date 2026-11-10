import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
Finite-field certificate and counting bridge.

This file has no quantum-channel or algorithmic complexity assumptions.
Its statements concern nondegenerate reflexive bilinear forms and isotropic
subspaces; a concrete binary symplectic instance is developed separately.
-/

noncomputable section

namespace QecReliability

open Module LinearMap
open LinearMap (BilinForm)

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W]

def normalizer (B : BilinForm F W) (S : Submodule F W) : Submodule F W :=
  B.orthogonal S

def localized (B : BilinForm F W) (S U : Submodule F W) : Submodule F W :=
  normalizer B S ⊓ U

def Good (B : BilinForm F W) (S U : Submodule F W) (z : W) : Prop :=
  z ∈ S ⊔ B.orthogonal U

def Bad (B : BilinForm F W) (S U : Submodule F W) (z : W) : Prop :=
  ∃ x ∈ localized B S U, B x z = 1

theorem orthogonal_sup (B : BilinForm F W) (P Q : Submodule F W) :
    B.orthogonal (P ⊔ Q) = B.orthogonal P ⊓ B.orthogonal Q := by
  ext z
  constructor
  · intro hz
    exact ⟨fun x hx => hz x ((show P ≤ P ⊔ Q from le_sup_left) hx),
      fun x hx => hz x ((show Q ≤ P ⊔ Q from le_sup_right) hx)⟩
  · rintro ⟨hP, hQ⟩ x hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    change B (p + q) z = 0
    rw [BilinForm.add_left, show B p z = 0 from hP p hp,
      show B q z = 0 from hQ q hq, zero_add]

variable [FiniteDimensional F W]

theorem orthogonal_inf (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (P Q : Submodule F W) :
    B.orthogonal (P ⊓ Q) = B.orthogonal P ⊔ B.orthogonal Q := by
  have h : B.orthogonal (B.orthogonal P ⊔ B.orthogonal Q) = P ⊓ Q := by
    rw [orthogonal_sup, B.orthogonal_orthogonal hB hR,
      B.orthogonal_orthogonal hB hR]
  rw [← h, B.orthogonal_orthogonal hB hR]

theorem good_iff_orthogonal (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U : Submodule F W) (z : W) :
    Good B S U z ↔ z ∈ B.orthogonal (localized B S U) := by
  unfold Good localized normalizer
  rw [orthogonal_inf B hB hR, B.orthogonal_orthogonal hB hR]

/-- Complementarity holds in the whole ambient space, not merely the normalizer. -/
theorem bad_iff_not_good (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U : Submodule F W) (z : W) :
    Bad B S U z ↔ ¬ Good B S U z := by
  classical
  constructor
  · rintro ⟨x, hx, hxz⟩ hg
    have hz : B x z = 0 := (good_iff_orthogonal B hB hR S U z).mp hg x hx
    exact one_ne_zero (hxz.symm.trans hz)
  · intro hg
    have hn : ¬ ∀ x ∈ localized B S U, B x z = 0 := by
      intro hz
      exact hg ((good_iff_orthogonal B hB hR S U z).mpr hz)
    push_neg at hn
    obtain ⟨x, hx, hxz⟩ := hn
    refine ⟨(B x z)⁻¹ • x, (localized B S U).smul_mem _ hx, ?_⟩
    rw [BilinForm.smul_left, inv_mul_cancel₀ hxz]

theorem good_or_bad (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U : Submodule F W) (z : W) :
    Good B S U z ∨ Bad B S U z := by
  classical
  by_cases h : Good B S U z
  · exact Or.inl h
  · exact Or.inr ((bad_iff_not_good B hB hR S U z).mpr h)

def goodSpace (B : BilinForm F W) (S U : Submodule F W) : Submodule F W :=
  normalizer B S ⊓ B.orthogonal (localized B S U)

def ambiguity (B : BilinForm F W) (S U : Submodule F W) : ℕ :=
  finrank F (localized B S U) - finrank F (S ⊓ U : Submodule F W)

omit [FiniteDimensional F W] in
theorem goodSpace_eq_orthogonal_sup (B : BilinForm F W) (S U : Submodule F W) :
    goodSpace B S U = B.orthogonal (S ⊔ localized B S U) := by
  rw [orthogonal_sup]
  rfl

omit [FiniteDimensional F W] in
theorem stabilizer_inf_localized (B : BilinForm F W) (S U : Submodule F W)
    (hS : S ≤ normalizer B S) : S ⊓ localized B S U = S ⊓ U := by
  ext x
  change (x ∈ S ∧ x ∈ normalizer B S ∧ x ∈ U) ↔ (x ∈ S ∧ x ∈ U)
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hS h.1, h.2⟩⟩

theorem finrank_goodSpace_add_ambiguity (B : BilinForm F W)
    (hB : B.Nondegenerate) (hR : B.IsRefl) (S U : Submodule F W)
    (hS : S ≤ normalizer B S) :
    finrank F (goodSpace B S U) + ambiguity B S U = finrank F (normalizer B S) := by
  have h1 := B.finrank_add_finrank_orthogonal hR S
  have h2 := B.finrank_add_finrank_orthogonal hR (S ⊔ localized B S U)
  rw [B.orthogonal_top_eq_bot hB, inf_bot_eq, finrank_bot, add_zero] at h1 h2
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq S (localized B S U)
  rw [stabilizer_inf_localized B S U hS] at h3
  have h4 : finrank F (S ⊓ U : Submodule F W) ≤ finrank F (localized B S U) :=
    Submodule.finrank_mono (fun _ hx => ⟨hS hx.1, hx.2⟩)
  rw [goodSpace_eq_orthogonal_sup]
  unfold ambiguity normalizer
  omega

theorem ambiguity_mono (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U U' : Submodule F W) (hS : S ≤ normalizer B S)
    (hU : U ≤ U') : ambiguity B S U ≤ ambiguity B S U' := by
  have hK : localized B S U ≤ localized B S U' := inf_le_inf_left _ hU
  have hG : goodSpace B S U' ≤ goodSpace B S U :=
    inf_le_inf_left _ (B.orthogonal_le hK)
  have hdim := Submodule.finrank_mono hG
  have h1 := finrank_goodSpace_add_ambiguity B hB hR S U hS
  have h2 := finrank_goodSpace_add_ambiguity B hB hR S U' hS
  omega

omit [FiniteDimensional F W] in
@[simp] theorem ambiguity_bot (B : BilinForm F W) (S : Submodule F W) :
    ambiguity B S ⊥ = 0 := by
  unfold ambiguity localized
  rw [inf_bot_eq, inf_bot_eq, Nat.sub_self]

omit [FiniteDimensional F W] in
theorem ambiguity_top (B : BilinForm F W) (S : Submodule F W) :
    ambiguity B S ⊤ = finrank F (normalizer B S) - finrank F S := by
  unfold ambiguity localized
  rw [inf_top_eq, inf_top_eq]

/-- The map sends a normalizer vector to its pairing functional on the localized space. -/
def pairingMap (B : BilinForm F W) (S U : Submodule F W) :
    normalizer B S →ₗ[F] (localized B S U →ₗ[F] F) :=
  B.flip.domRestrict₁₂ (normalizer B S) (localized B S U)

omit [FiniteDimensional F W] in
@[simp] theorem pairingMap_apply (B : BilinForm F W) (S U : Submodule F W)
    (z : normalizer B S) (x : localized B S U) : pairingMap B S U z x = B x z := rfl

omit [FiniteDimensional F W] in
theorem mem_pairingMap_ker_iff (B : BilinForm F W) (S U : Submodule F W)
    (z : normalizer B S) :
    z ∈ LinearMap.ker (pairingMap B S U) ↔ (z : W) ∈ B.orthogonal (localized B S U) := by
  change pairingMap B S U z = 0 ↔ ∀ x ∈ localized B S U, B x z = 0
  constructor
  · intro h x hx
    exact congrArg (fun f : localized B S U →ₗ[F] F => f ⟨x, hx⟩) h
  · intro h
    ext x
    exact h x x.property

def kernelEquivGoodSpace (B : BilinForm F W) (S U : Submodule F W) :
    LinearMap.ker (pairingMap B S U) ≃ₗ[F] goodSpace B S U where
  toFun z := ⟨z.1.1, z.1.2, (mem_pairingMap_ker_iff B S U z.1).mp z.2⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, (mem_pairingMap_ker_iff B S U _).mpr z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_pairingMap_range (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U : Submodule F W) (hS : S ≤ normalizer B S) :
    finrank F (LinearMap.range (pairingMap B S U)) = ambiguity B S U := by
  have h := (pairingMap B S U).finrank_range_add_finrank_ker
  have he := (kernelEquivGoodSpace B S U).finrank_eq
  have hd := finrank_goodSpace_add_ambiguity B hB hR S U hS
  omega

theorem card_normalizer_eq_card_goodSpace_mul (B : BilinForm F W)
    (hB : B.Nondegenerate) (hR : B.IsRefl) (S U : Submodule F W)
    (hS : S ≤ normalizer B S) :
    Nat.card (normalizer B S) = Nat.card (goodSpace B S U) * Nat.card F ^ ambiguity B S U := by
  rw [Module.natCard_eq_pow_finrank (K := F),
    Module.natCard_eq_pow_finrank (K := F) (V := goodSpace B S U), ← pow_add,
    finrank_goodSpace_add_ambiguity B hB hR S U hS]

theorem good_fraction [Finite F] (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U : Submodule F W) (hS : S ≤ normalizer B S) :
    (Nat.card (goodSpace B S U) : ℚ) / Nat.card (normalizer B S) =
      ((Nat.card F : ℚ) ^ ambiguity B S U)⁻¹ := by
  have hp : 0 < Nat.card F := Nat.card_pos
  have hg : 0 < Nat.card (goodSpace B S U) := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    exact pow_pos hp _
  have hgq : (Nat.card (goodSpace B S U) : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hc : (Nat.card (normalizer B S) : ℚ) =
      Nat.card (goodSpace B S U) * (Nat.card F : ℚ) ^ ambiguity B S U := by
    exact_mod_cast card_normalizer_eq_card_goodSpace_mul B hB hR S U hS
  rw [hc, div_mul_eq_div_div, div_self hgq, one_div]

/-- The counted objects are vectors, not witnesses for a vector. -/
def goodSubtypeEquiv (B : BilinForm F W) (hB : B.Nondegenerate) (hR : B.IsRefl)
    (S U : Submodule F W) :
    {z : normalizer B S // Good B S U z} ≃ goodSpace B S U where
  toFun z := ⟨z.1.1, z.1.2, (good_iff_orthogonal B hB hR S U z.1).mp z.2⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, (good_iff_orthogonal B hB hR S U z.1).mpr z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem good_card_fraction [Finite F] (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U : Submodule F W) (hS : S ≤ normalizer B S) :
    (Nat.card {z : normalizer B S // Good B S U z} : ℚ) /
      Nat.card (normalizer B S) = ((Nat.card F : ℚ) ^ ambiguity B S U)⁻¹ := by
  rw [Nat.card_congr (goodSubtypeEquiv B hB hR S U)]
  exact good_fraction B hB hR S U hS

theorem good_card_add_bad_card [Finite F] (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U : Submodule F W) :
    Nat.card {z : normalizer B S // Good B S U z} +
      Nat.card {z : normalizer B S // Bad B S U z} = Nat.card (normalizer B S) := by
  classical
  letI : Finite W := Module.finite_of_finite F
  let e : {z : normalizer B S // Bad B S U z} ≃
      {z : normalizer B S // ¬ Good B S U z} :=
    Equiv.subtypeEquivRight (fun z => bad_iff_not_good B hB hR S U z)
  rw [Nat.card_congr e, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl (fun z : normalizer B S => Good B S U z))

theorem bad_card_fraction [Finite F] (B : BilinForm F W) (hB : B.Nondegenerate)
    (hR : B.IsRefl) (S U : Submodule F W) (hS : S ≤ normalizer B S) :
    (Nat.card {z : normalizer B S // Bad B S U z} : ℚ) /
      Nat.card (normalizer B S) = 1 - ((Nat.card F : ℚ) ^ ambiguity B S U)⁻¹ := by
  have hpos : 0 < Nat.card (normalizer B S) := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    exact pow_pos Nat.card_pos _
  have hn : (Nat.card (normalizer B S) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hc : (Nat.card {z : normalizer B S // Good B S U z} : ℚ) +
      Nat.card {z : normalizer B S // Bad B S U z} = Nat.card (normalizer B S) := by
    exact_mod_cast good_card_add_bad_card B hB hR S U
  have hf := good_card_fraction B hB hR S U hS
  have hd : (Nat.card {z : normalizer B S // Good B S U z} : ℚ) /
      Nat.card (normalizer B S) +
      (Nat.card {z : normalizer B S // Bad B S U z} : ℚ) / Nat.card (normalizer B S) = 1 := by
    rw [← add_div, hc, div_self hn]
  linarith

end QecReliability
