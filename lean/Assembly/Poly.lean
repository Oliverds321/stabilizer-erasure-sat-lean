import OracleCost.EncodedSAT
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Assembly.Poly: functions bounded by a polynomial envelope

`PolyBounded f` : `f L ≤ c·(L+1)^e` for some constants. Closed under constants, the
identity, `+`, `·`, `max`, pointwise domination, and composition with an envelope. The
tactic `poly_bounded` proves `PolyBounded (fun L => …)` for expressions built from these.
-/

set_option autoImplicit false

namespace QecReliability.Assembly
open OracleCost

/-- `f` is dominated by a polynomial envelope `c·(L+1)^e`. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ c e : ℕ, ∀ L, f L ≤ c * (L + 1) ^ e

namespace PolyBounded

theorem pow_le_pow_add (L e₁ e₂ : ℕ) : (L + 1) ^ e₁ ≤ (L + 1) ^ (e₁ + e₂) :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem pow_le_pow_add' (L e₁ e₂ : ℕ) : (L + 1) ^ e₂ ≤ (L + 1) ^ (e₁ + e₂) :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem const (c : ℕ) : PolyBounded (fun _ => c) := ⟨c, 0, fun L => by simp⟩

theorem id : PolyBounded (fun L => L) := ⟨1, 1, fun L => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun L => f L + g L) := by
  obtain ⟨c₁, e₁, h₁⟩ := hf
  obtain ⟨c₂, e₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, e₁ + e₂, fun L => ?_⟩
  have a := Nat.mul_le_mul_left c₁ (pow_le_pow_add L e₁ e₂)
  have b := Nat.mul_le_mul_left c₂ (pow_le_pow_add' L e₁ e₂)
  have := h₁ L
  have := h₂ L
  show f L + g L ≤ (c₁ + c₂) * (L + 1) ^ (e₁ + e₂)
  rw [Nat.add_mul]
  omega

theorem mul {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun L => f L * g L) := by
  obtain ⟨c₁, e₁, h₁⟩ := hf
  obtain ⟨c₂, e₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, e₁ + e₂, fun L => ?_⟩
  calc f L * g L ≤ (c₁ * (L + 1) ^ e₁) * (c₂ * (L + 1) ^ e₂) := Nat.mul_le_mul (h₁ L) (h₂ L)
    _ = c₁ * c₂ * (L + 1) ^ (e₁ + e₂) := by rw [pow_add]; ring

theorem pow {f : ℕ → ℕ} (hf : PolyBounded f) (e : ℕ) : PolyBounded (fun L => f L ^ e) := by
  induction e with
  | zero => simpa using const 1
  | succ e ih => simpa [pow_succ] using mul ih hf

theorem mono {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ L, f L ≤ g L) : PolyBounded f := by
  obtain ⟨c, e, hc⟩ := hg
  exact ⟨c, e, fun L => (h L).trans (hc L)⟩

theorem max {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun L => Max.max (f L) (g L)) :=
  mono (add hf hg) (fun L => max_le (by omega) (by omega))

theorem succ_le_pow (c e L : ℕ) : c * (L + 1) ^ e + 1 ≤ (c + 1) * (L + 1) ^ e := by
  have : 1 ≤ (L + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  rw [Nat.add_mul, one_mul]
  omega

/-- Composition with a polynomial envelope. -/
theorem env (P : PolynomialEnvelope) {f : ℕ → ℕ} (hf : PolyBounded f) :
    PolyBounded (fun L => P.eval (f L)) := by
  obtain ⟨c, e, h⟩ := hf
  refine ⟨P.coefficient * (c + 1) ^ P.degree, e * P.degree, fun L => ?_⟩
  unfold PolynomialEnvelope.eval
  calc P.coefficient * (f L + 1) ^ P.degree
      ≤ P.coefficient * ((c + 1) * (L + 1) ^ e) ^ P.degree := by
        gcongr
        exact (Nat.add_le_add_right (h L) 1).trans (succ_le_pow c e L)
    _ = P.coefficient * (c + 1) ^ P.degree * (L + 1) ^ (e * P.degree) := by
        rw [mul_pow, ← pow_mul]; ring

/-- The envelope `⟨c, e⟩` of a bounded function. -/
theorem envelope {f : ℕ → ℕ} (hf : PolyBounded f) :
    ∃ P : PolynomialEnvelope, ∀ L, f L ≤ P.eval L := by
  obtain ⟨c, e, h⟩ := hf
  exact ⟨⟨c, e⟩, h⟩

end PolyBounded

/-- Prove `PolyBounded (fun L => …)` structurally. -/
macro "poly_bounded" : tactic =>
  `(tactic| repeat' first
    | with_reducible assumption
    | with_reducible exact PolyBounded.const _
    | with_reducible exact PolyBounded.id
    | with_reducible apply PolyBounded.add
    | with_reducible apply PolyBounded.mul
    | with_reducible apply PolyBounded.max
    | with_reducible apply PolyBounded.pow
    | with_reducible apply PolyBounded.env)

/-- Two-variable form used for the time bound: a polynomial in `L` times a square in `x`
is below one envelope evaluated at `L + x`. -/
theorem env_two_var (c e L x : ℕ) :
    c * (L + 1) ^ e * (x + 1) ^ 2 ≤ c * (L + x + 1) ^ (e + 2) := by
  have h1 : (L + 1) ^ e ≤ (L + x + 1) ^ e := Nat.pow_le_pow_left (by omega) _
  have h2 : (x + 1) ^ 2 ≤ (L + x + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
  calc c * (L + 1) ^ e * (x + 1) ^ 2 ≤ c * (L + x + 1) ^ e * (L + x + 1) ^ 2 := by gcongr
    _ = c * (L + x + 1) ^ (e + 2) := by rw [pow_add]; ring

end QecReliability.Assembly
