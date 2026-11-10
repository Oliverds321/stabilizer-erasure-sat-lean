import ExternalSATPrimitiveLink
import ExternalSATObservedTransport

/-! Interval arithmetic for the actual physical handoff. The engine origin is
the frontend's current output-tape head, not a reset absolute coordinate.
These lemmas bound unions of already measured intervals; no output-length
estimate is used as a space bound. -/
namespace QecReliability.ExternalSATBridge.PrimitiveLink

/-- The two physical intervals overlap at the handoff head. Their hull saves
at least one cell relative to the sum of the two inclusive interval lengths. -/
theorem shifted_hull_width {a b c d p : ℤ}
    (ha : a ≤ p) (hb : p ≤ b) (hc : c ≤ 0) (hd : 0 ≤ d) :
    (max b (p + d) - min a (p + c) + 1).toNat + 1 ≤
      (b - a + 1).toNat + (d - c + 1).toNat := by
  by_cases hl : a ≤ p + c <;> by_cases hu : b ≤ p + d
  · rw [min_eq_left hl, max_eq_right hu]
    omega
  · rw [min_eq_left hl, max_eq_left (le_of_not_ge hu)]
    omega
  · rw [min_eq_right (le_of_not_ge hl), max_eq_right hu]
    omega
  · rw [min_eq_right (le_of_not_ge hl), max_eq_left (le_of_not_ge hu)]
    omega

theorem shifted_hull_width_le_sum {a b c d p : ℤ}
    (ha : a ≤ p) (hb : p ≤ b) (hc : c ≤ 0) (hd : 0 ≤ d) :
    (max b (p + d) - min a (p + c) + 1).toNat ≤
      (b - a + 1).toNat + (d - c + 1).toNat := by
  have h := shifted_hull_width ha hb hc hd
  omega

/-- Enclosing the frontend interval and the translated engine interval also
encloses every later engine head whose source coordinate is in that interval. -/
theorem shifted_hull_encloses {a b c d p x : ℤ}
    (hx : c ≤ x ∧ x ≤ d) :
    min a (p + c) ≤ p + x ∧ p + x ≤ max b (p + d) := by
  constructor
  · exact (min_le_right a (p + c)).trans (by omega)
  · exact (show p + x ≤ p + d by omega).trans (le_max_right b (p + d))

end QecReliability.ExternalSATBridge.PrimitiveLink
