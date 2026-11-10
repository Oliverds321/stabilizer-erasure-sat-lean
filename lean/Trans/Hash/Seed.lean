import QecReliability.FiniteRandomTapeExecutionCandidate
import FL.Typed.Syntax

/-!
# Trans.Hash.Seed: hash seeds as their own bit strings

A seed `s : CodeHash.Seed L t` (`L` local seeds, each `t` affine coefficients and one
intercept, over `F = ZMod 2`) is represented on the FL side by its **bit string**
(`seedT = .list .bool`), row-major: row `l` occupies positions `l*(t+1) … l*(t+1)+t`,
the first `t` bits are the coefficients, the last one is the intercept. This is exactly the
inverse of `CodeHash.seedTapeEquiv`, the decoder used by the sampler
(`CodeHash.FiniteRandomTape.outputSeeds`): the `r`-th seed of a stored word `s` is decoded
from the slice `(s.drop (r * seedBits L t)).take (seedBits L t)` (`outputSeeds_slice`).

* `seedOfBits L t bs`: decoding (total; missing bits read as `false`);
* `seedBitsOf s`: encoding; `seedOfBits_seedBitsOf`, `seedBitsOf_length`;
* `seedOfBits_coeff`, `seedOfBits_intercept`: the bits read by the hash circuits;
* `seedRows t L bs`: the rows `(coefficients, intercept)` consumed by the plain construction,
  `seedRows_eq`: their meaning.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Hash
open QecReliability.CodeHash

/-- FL type of a seed (its bit string). -/
abbrev seedT : FL.Ty := .list .bool

/-- Decode a bit string as a seed (positions beyond the list read `false`). -/
def seedOfBits (L t : ℕ) (bs : List Bool) : Seed L t :=
  seedTapeEquiv L t (fun i => bs.getD i.val false)

/-- The bit string of a seed. -/
def seedBitsOf {L t : ℕ} (s : Seed L t) : List Bool := List.ofFn ((seedTapeEquiv L t).symm s)

theorem seedBitsOf_length {L t : ℕ} (s : Seed L t) : (seedBitsOf s).length = seedBits L t := by
  simp [seedBitsOf]

theorem seedOfBits_seedBitsOf {L t : ℕ} (s : Seed L t) : seedOfBits L t (seedBitsOf s) = s := by
  have h : (fun i : Fin (seedBits L t) => (seedBitsOf s).getD i.val false) =
      (seedTapeEquiv L t).symm s := by
    funext i
    simp [seedBitsOf, List.getD_eq_getElem?_getD]
  rw [seedOfBits, h, Equiv.apply_symm_apply]

/-- Every seed is decoded from a bit string of the right length. -/
theorem seed_surj {L t : ℕ} (s : Seed L t) :
    ∃ bs : List Bool, bs.length = seedBits L t ∧ seedOfBits L t bs = s :=
  ⟨seedBitsOf s, seedBitsOf_length s, seedOfBits_seedBitsOf s⟩

theorem bitBool_symm_apply (b : Bool) : Binary.bitBool (Binary.bitBool.symm b) = b :=
  Binary.bitBool.apply_symm_apply b

theorem seedOfBits_apply (L t : ℕ) (bs : List Bool) (l : Fin L) :
    seedOfBits L t bs l =
      (fun j => Binary.bitBool.symm (bs.getD (j.val + (t + 1) * l.val) false),
        Binary.bitBool.symm (bs.getD (t + (t + 1) * l.val) false)) := rfl

theorem seedOfBits_coeff (L t : ℕ) (bs : List Bool) (l : Fin L) (j : Fin t) :
    Binary.bitBool ((seedOfBits L t bs l).1 j) = bs.getD ((t + 1) * l.val + j.val) false := by
  rw [seedOfBits_apply, bitBool_symm_apply, Nat.add_comm]

theorem seedOfBits_intercept (L t : ℕ) (bs : List Bool) (l : Fin L) :
    Binary.bitBool (seedOfBits L t bs l).2 = bs.getD ((t + 1) * l.val + t) false := by
  rw [seedOfBits_apply, bitBool_symm_apply, Nat.add_comm]

/-- Two bit strings agreeing on the first `seedBits L t` positions decode equally. -/
theorem seedOfBits_congr (L t : ℕ) (bs cs : List Bool)
    (h : ∀ i < seedBits L t, bs.getD i false = cs.getD i false) :
    seedOfBits L t bs = seedOfBits L t cs := by
  unfold seedOfBits
  congr 1
  funext i
  exact h i.val i.isLt

/-- The `r`-th seed decoded by the sampler is the decoding of the `r`-th slice. -/
theorem outputSeeds_slice (L t m : ℕ) (s : List Bool) (r : Fin (2 * m + 1)) :
    FiniteRandomTape.outputSeeds L t m s r =
      seedOfBits L t ((s.drop (r.val * seedBits L t)).take (seedBits L t)) := by
  have hst : ∀ (u : List Bool) (n : ℕ), FiniteRandomTape.storedBit u n = u.getD n false := by
    intro u n
    induction u generalizing n with
    | nil => rfl
    | cons b u ih => cases n <;> simp [FiniteRandomTape.storedBit, ih]
  simp only [FiniteRandomTape.outputSeeds, repeatedSeedTapeEquiv, blockTapeEquiv,
    mapFunctionEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, seedOfBits]
  congr 1
  funext h
  rw [hst]
  simp only [finProdFinEquiv_apply_val, List.getD_eq_getElem?_getD, List.getElem?_take,
    List.getElem?_drop, if_pos h.isLt]
  congr 2
  ring

/-! ## Rows of a seed bit string -/

/-- `L` rows `(t coefficients, intercept)` of a row-major bit string. -/
def seedRows (t : ℕ) : ℕ → List Bool → List (List Bool × Bool)
  | 0, _ => []
  | L + 1, bs => (bs.take t, bs.getD t false) :: seedRows t L (bs.drop (t + 1))

theorem seedRows_length (t L : ℕ) (bs : List Bool) : (seedRows t L bs).length = L := by
  induction L generalizing bs with
  | zero => rfl
  | succ L ih => simp [seedRows, ih]

theorem seedRows_getElem (t L : ℕ) (bs : List Bool) (hb : (t + 1) * L ≤ bs.length) (l : ℕ)
    (hl : l < (seedRows t L bs).length) :
    (seedRows t L bs)[l] =
      ((List.range t).map (fun j => bs.getD ((t + 1) * l + j) false),
        bs.getD ((t + 1) * l + t) false) := by
  induction L generalizing bs l with
  | zero => simp [seedRows] at hl
  | succ L ih =>
    cases l with
    | zero =>
      simp only [seedRows, List.getElem_cons_zero, Nat.mul_zero, Nat.zero_add, Prod.mk.injEq,
        and_true]
      apply List.ext_getElem
      · simp only [List.length_take, List.length_map, List.length_range]
        have : t ≤ bs.length := by nlinarith
        omega
      · intro n h1 h2
        simp only [List.length_map, List.length_range] at h2
        simp [List.getD_eq_getElem?_getD, List.getElem_take]
        rw [List.getElem?_eq_getElem (by simp at h1; omega)]
        simp
    | succ l =>
      simp only [seedRows, List.getElem_cons_succ]
      rw [ih _ (by simp only [List.length_drop]; rw [Nat.mul_succ] at hb; omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Prod.mk.injEq]
      constructor
      · congr 1; funext j; congr 2; ring
      · congr 2; ring

end QecReliability.Trans.Hash
