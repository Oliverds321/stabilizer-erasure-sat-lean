import Mathlib.Data.Nat.Bitwise

/-!



This file is deliberately generic: `selectCertified` remains conditional on
the finite counting theorem's Boolean reflection bridge.

The runtime data path is Nat/Bool recursion, not Classical.choose or Fintype
enumeration. The existential argument of firstWithin is used only in proofs.
Do not #eval the eventual D = 16^384 specialization. Do not prove its checker
result with decide/native_decide. The generic correctness proofs are the route.
-/

namespace FiniteLocalSelectorCandidate

/-- Visit start, ..., start + fuel - 1 in ascending order. -/
def firstWithin (p : Nat → Bool) :
    (fuel start : Nat) →
    (∃ i, start ≤ i ∧ i < start + fuel ∧ p i = true) →
    {i : Nat // start ≤ i ∧ i < start + fuel ∧ p i = true}
  | 0, start, hex => False.elim (by
      obtain ⟨i, hlo, hhi, _⟩ := hex
      omega)
  | fuel + 1, start, hex =>
      if hs : p start = true then
        ⟨start, by omega, by omega, hs⟩
      else
        let htail : ∃ i, start + 1 ≤ i ∧ i < (start + 1) + fuel ∧ p i = true := by
          obtain ⟨i, hlo, hhi, hp⟩ := hex
          have hne : i ≠ start := by
            intro heq
            subst i
            exact hs hp
          exact ⟨i, by omega, by omega, hp⟩
        let ans := firstWithin p fuel (start + 1) htail
        ⟨ans.val, by
          obtain ⟨hlo, hhi, hp⟩ := ans.property
          exact ⟨by omega, by omega, hp⟩⟩

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

theorem allBelow_eq_true (p : Nat → Bool) (n : Nat) :
    allBelow p n = true ↔ ∀ i, i < n → p i = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
      rw [allBelow, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ i hi
        by_cases hin : i < n
        · exact hprev i hin
        · have heq : i = n := by omega
          subst i
          exact hlast
      · intro h
        exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- The low n bits, including zero padding to exactly n coordinates. -/
def wordWeight (n x : Nat) : Nat :=
  match n with
  | 0 => 0
  | j + 1 => wordWeight j x + if x.testBit j then 1 else 0

theorem wordWeight_le (n x : Nat) : wordWeight n x ≤ n := by
  induction n with
  | zero => simp [wordWeight]
  | succ n ih =>
      simp only [wordWeight]
      split <;> omega

/-- Fixed row stride k; the prefix argument is the number of consumed columns. -/
def rowPrefix (k a x row : Nat) : Nat → Bool
  | 0 => false
  | j + 1 => Bool.xor (rowPrefix k a x row j)
      (a.testBit (row * k + j) && x.testBit j)

def parityWeight (k a x : Nat) : Nat → Nat
  | 0 => 0
  | row + 1 => parityWeight k a x row + if rowPrefix k a x row k then 1 else 0

def systematicWeight (k h a x : Nat) : Nat :=
  wordWeight k x + parityWeight k a x h

def checkMatrix (k h r a : Nat) : Bool :=
  allBelow (fun x => if x = 0 then true else decide (r ≤ systematicWeight k h a x)) (2 ^ k)

theorem checkMatrix_spec (k h r a : Nat) :
    checkMatrix k h r a = true ↔
      ∀ x, x < 2 ^ k → x ≠ 0 → r ≤ systematicWeight k h a x := by
  rw [checkMatrix, allBelow_eq_true]
  constructor
  · intro hgood x hlt hne
    have hx := hgood x hlt
    simpa [hne] using hx
  · intro hgood x hlt
    by_cases hx : x = 0
    · simp [hx]
    · simpa [hx] using hgood x hlt hx

structure CertifiedParity (k h r : Nat) where
  code : Fin (2 ^ (h * k))
  distance : ∀ x, x < 2 ^ k → x ≠ 0 → r ≤ systematicWeight k h code.val x

def selectCertified (k h r : Nat)
    (hex : ∃ a, a < 2 ^ (h * k) ∧ checkMatrix k h r a = true) :
    CertifiedParity k h r :=
  let hex' : ∃ a, 0 ≤ a ∧ a < 0 + 2 ^ (h * k) ∧ checkMatrix k h r a = true := by
    obtain ⟨a, ha, hp⟩ := hex
    exact ⟨a, Nat.zero_le _, by simpa using ha, hp⟩
  let ans := firstWithin (checkMatrix k h r) (2 ^ (h * k)) 0 hex'
  { code := ⟨ans.val, by simpa using ans.property.2.1⟩
    distance := (checkMatrix_spec k h r ans.val).mp ans.property.2.2 }

def matrixEntry {k h r : Nat} (A : CertifiedParity k h r)
    (row : Fin h) (col : Fin k) : Bool :=
  A.code.val.testBit (row.val * k + col.val)

/-- This is the packed count. Its equality with the two-index support count
requires the row-major index bijection, as recorded in the handoff. -/
def trueEntryCount {k h r : Nat} (A : CertifiedParity k h r) : Nat :=
  wordWeight (h * k) A.code.val

theorem trueEntryCount_le {k h r : Nat} (A : CertifiedParity k h r) :
    trueEntryCount A ≤ h * k :=
  wordWeight_le (h * k) A.code.val

end FiniteLocalSelectorCandidate
