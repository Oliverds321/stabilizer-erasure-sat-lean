import FL.Typed.Syntax

/-!
# FL library: natural numbers on the binary encoding

Every function is a typed body (`*Body`), a signature (`*F`, carrying the Lean meaning and
closed-form bounds), and a validity theorem (`*_valid`) in the form
`P[i]? = some body.compile → (deps valid) → ∀ x, (F i).ValidAt P x`.
Bodies are parameterised by their own index `i` and by the indices of their callees.

Bounds (with `A = a.size`, `B = b.size`, `Nat.size` = bit length):

| function | meaning | cost | depth | msize |
|---|---|---|---|---|
| `succF` | `n + 1` | `25A + 25` | `A + 1` | `4A + 10` |
| `predF` | `n - 1` | `25A + 25` | `A + 1` | `4A + 10` |
| `addcF` | `a + b + c` | `50(A+B) + 50` | `A + B + 2` | `4(A+B) + 20` |
| `addF` | `a + b` | `50(A+B) + 60` | `A + B + 3` | `4(A+B) + 20` |
| `subbF` | `(b + c ≤ a, a - (b + c))` | `60(A+B) + 60` | `A + B + 2` | `4(A+B) + 20` |
| `subF` `leF` `ltF` `maxF` `minF` | | `60(A+B) + 80` | `A + B + 3` | `4(A+B) + 20` |
| `eqF` | `a = b` | `120(A+B) + 150` | `A + B + 3` | `4(A+B) + 20` |
| `mulF` | `a * b` | `mulCost a b = 100(A+1)(A+B+1)` | `2(A+B) + 4` | `8(A+B) + 40` |
| `bitLenF` | `Nat.size n` | `30(A+1)(A+1)` | `2A + 2` | `4A + 10` |
| `div2F` `mod2F` `oddF` | `n / 2`, `n % 2`, `n odd` | `≤ 12` | `1` | `5` |
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.FL.Lib
open Tm NatSize

variable {P : Program}

/-! ## Successor and predecessor -/

@[simps] def succF (i : ℕ) : FnSig .nat .nat where
  idx := i
  den n := n + 1
  cost n := 25 * n.size + 25
  depth n := n.size + 1
  msize n := 4 * n.size + 10

def succBody (i : ℕ) : Tm [.nat] .nat :=
  .ncase v0 (.lit (1 : ℕ)) (.ite v0 (.letE (.app (succF i) v1) (.bit .ff v0)) (.bit .tt v1))

theorem succ_valid {i : ℕ} (hP : P[i]? = some (succBody i).compile) :
    ∀ n, (succF i).ValidAt P n := by
  refine FnSig.valid_of_body _ _ hP (fun n => n) fun (n : ℕ) ih => ?_
  by_cases hn : n = 0
  · subst hn; constructor <;> tm_auto [succBody]
  · have hs := size_half hn
    have hih := ih (n / 2) (by omega)
    rcases Nat.mod_two_cases n with hb | hb <;>
      constructor <;> tm_auto [succBody, hn, hb, hih]

@[simps] def predF (i : ℕ) : FnSig .nat .nat where
  idx := i
  den n := n - 1
  cost n := 25 * n.size + 25
  depth n := n.size + 1
  msize n := 4 * n.size + 10

def predBody (i : ℕ) : Tm [.nat] .nat :=
  .ncase v0 .zero (.ite v0 (.bit .ff v1) (.letE (.app (predF i) v1) (.bit .tt v0)))

theorem pred_valid {i : ℕ} (hP : P[i]? = some (predBody i).compile) :
    ∀ n, (predF i).ValidAt P n := by
  refine FnSig.valid_of_body _ _ hP (fun n => n) fun (n : ℕ) ih => ?_
  by_cases hn : n = 0
  · subst hn; constructor <;> tm_auto [predBody]
  · have hs := size_half hn
    have hih := ih (n / 2) (by omega)
    rcases Nat.mod_two_cases n with hb | hb <;>
      constructor <;> tm_auto [predBody, hn, hb, hih]

/-! ## Addition with carry -/

/-- `addc (c, a, b) = a + b + c`. -/
@[simps] def addcF (i : ℕ) : FnSig (.prod .bool (.prod .nat .nat)) .nat where
  idx := i
  den x := x.2.1 + x.2.2 + x.1.toNat
  cost x := 50 * (x.2.1.size + x.2.2.size) + 50
  depth x := x.2.1.size + x.2.2.size + 2
  msize x := 4 * (x.2.1.size + x.2.2.size) + 20

def addcBody (is i : ℕ) : Tm [.prod .bool (.prod .nat .nat)] .nat :=
  .ncase (.fst (.snd v0))
    (.ite (.fst v0) (.app (succF is) (.snd (.snd v0))) (.snd (.snd v0)))
    (.ncase (.snd (.snd v2))
      (.ite (.fst v2) (.app (succF is) (.fst (.snd v2))) (.fst (.snd v2)))
      (.letE (.app (addcF i) (.pair (.maj v0 v2 (.fst v4)) (.pair v3 v1)))
        (.bit (.xor3 v1 v3 (.fst v5)) v0)))

theorem addc_valid {is i : ℕ} (hs : ∀ n, (succF is).ValidAt P n)
    (hP : P[i]? = some (addcBody is i).compile) : ∀ x, (addcF i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.2.1) ?_
  rintro ⟨c, (a : ℕ), (b : ℕ)⟩ ih
  by_cases ha : a = 0
  · subst ha; cases c <;> constructor <;> tm_auto [addcBody, hs]
  by_cases hb : b = 0
  · subst hb; cases c <;> constructor <;> tm_auto [addcBody, hs, ha]
  have hsa := size_half ha
  have hsb := size_half hb
  have hih := fun c' => ih (c', a / 2, b / 2) (by dsimp only; omega)
  rcases Nat.mod_two_cases a with ha2 | ha2 <;> rcases Nat.mod_two_cases b with hb2 | hb2 <;>
    cases c <;> constructor <;> tm_auto [addcBody, hs, ha, hb, ha2, hb2, hih]

@[simps] def addF (i : ℕ) : FnSig (.prod .nat .nat) .nat where
  idx := i
  den x := x.1 + x.2
  cost x := 50 * (x.1.size + x.2.size) + 60
  depth x := x.1.size + x.2.size + 3
  msize x := 4 * (x.1.size + x.2.size) + 20

def addBody (ic : ℕ) : Tm [.prod .nat .nat] .nat := .app (addcF ic) (.pair .ff v0)

theorem add_valid {ic i : ℕ} (hc : ∀ x, (addcF ic).ValidAt P x)
    (hP : P[i]? = some (addBody ic).compile) : ∀ x, (addF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩
  constructor <;> tm_auto [addBody, hc]

/-! ## Subtraction with borrow, comparisons -/

/-- `subb (c, a, b) = (b + c ≤ a, a - (b + c))`: truncated subtraction together with the
test that no truncation happened. -/
@[simps] def subbF (i : ℕ) : FnSig (.prod .bool (.prod .nat .nat)) (.prod .bool .nat) where
  idx := i
  den x := (decide (x.2.2 + x.1.toNat ≤ x.2.1), x.2.1 - (x.2.2 + x.1.toNat))
  cost x := 60 * (x.2.1.size + x.2.2.size) + 60
  depth x := x.2.1.size + x.2.2.size + 2
  msize x := 4 * (x.2.1.size + x.2.2.size) + 20

def subbBody (ip i : ℕ) : Tm [.prod .bool (.prod .nat .nat)] (.prod .bool .nat) :=
  .ncase (.snd (.snd v0))
    (.ite (.fst v0)
      (.pair (.isPos (.fst (.snd v0))) (.app (predF ip) (.fst (.snd v0))))
      (.pair .tt (.fst (.snd v0))))
    (.ncase (.fst (.snd v2))
      (.pair .ff .zero)
      (.letE (.app (subbF i) (.pair (.borrow v0 v2 (.fst v4)) (.pair v1 v3)))
        (.ite (.fst v0) (.pair .tt (.bit (.xor3 v1 v3 (.fst v5)) (.snd v0))) (.pair .ff .zero))))

set_option maxHeartbeats 1000000 in
theorem subb_valid {ip i : ℕ} (hp : ∀ n, (predF ip).ValidAt P n)
    (hP : P[i]? = some (subbBody ip i).compile) : ∀ x, (subbF i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.2.2) ?_
  rintro ⟨c, (a : ℕ), (b : ℕ)⟩ ih
  by_cases hb : b = 0
  · subst hb
    by_cases ha : a = 0
    · subst ha; cases c <;> constructor <;> tm_auto [subbBody, hp]
    · cases c <;> constructor <;> tm_auto [subbBody, hp, ha]
  by_cases ha : a = 0
  · subst ha; cases c <;> constructor <;> tm_auto [subbBody, hp, hb]
  have hsa := size_half ha
  have hsb := size_half hb
  have hih := fun c' => ih (c', a / 2, b / 2) (by dsimp only; omega)
  rcases Nat.mod_two_cases a with ha2 | ha2 <;> rcases Nat.mod_two_cases b with hb2 | hb2 <;>
    cases c <;> constructor <;> tm_auto [subbBody, hp, ha, hb, ha2, hb2, hih]

/-- `a - b` (truncated). -/
@[simps] def subF (i : ℕ) : FnSig (.prod .nat .nat) .nat where
  idx := i
  den x := x.1 - x.2
  cost x := 60 * (x.1.size + x.2.size) + 80
  depth x := x.1.size + x.2.size + 3
  msize x := 4 * (x.1.size + x.2.size) + 20

def subBody (ib : ℕ) : Tm [.prod .nat .nat] .nat := .snd (.app (subbF ib) (.pair .ff v0))

theorem sub_valid {ib i : ℕ} (hb : ∀ x, (subbF ib).ValidAt P x)
    (hP : P[i]? = some (subBody ib).compile) : ∀ x, (subF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩
  constructor <;> tm_auto [subBody, hb]

/-- `a ≤ b`. -/
@[simps] def leF (i : ℕ) : FnSig (.prod .nat .nat) .bool where
  idx := i
  den x := decide (x.1 ≤ x.2)
  cost x := 60 * (x.1.size + x.2.size) + 80
  depth x := x.1.size + x.2.size + 3
  msize x := 4 * (x.1.size + x.2.size) + 20

def leBody (ib : ℕ) : Tm [.prod .nat .nat] .bool :=
  .fst (.app (subbF ib) (.pair .ff (.pair (.snd v0) (.fst v0))))

theorem le_valid {ib i : ℕ} (hb : ∀ x, (subbF ib).ValidAt P x)
    (hP : P[i]? = some (leBody ib).compile) : ∀ x, (leF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩
  constructor <;> tm_auto [leBody, hb]

/-- `a < b`. -/
@[simps] def ltF (i : ℕ) : FnSig (.prod .nat .nat) .bool where
  idx := i
  den x := decide (x.1 < x.2)
  cost x := 60 * (x.1.size + x.2.size) + 80
  depth x := x.1.size + x.2.size + 3
  msize x := 4 * (x.1.size + x.2.size) + 20

def ltBody (ib : ℕ) : Tm [.prod .nat .nat] .bool :=
  .fst (.app (subbF ib) (.pair .tt (.pair (.snd v0) (.fst v0))))

theorem lt_valid {ib i : ℕ} (hb : ∀ x, (subbF ib).ValidAt P x)
    (hP : P[i]? = some (ltBody ib).compile) : ∀ x, (ltF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩
  constructor <;> tm_auto [ltBody, hb]

/-- `a = b`. -/
@[simps] def eqF (i : ℕ) : FnSig (.prod .nat .nat) .bool where
  idx := i
  den x := decide (x.1 = x.2)
  cost x := 120 * (x.1.size + x.2.size) + 150
  depth x := x.1.size + x.2.size + 3
  msize x := 4 * (x.1.size + x.2.size) + 20

def eqBody (ib : ℕ) : Tm [.prod .nat .nat] .bool :=
  .and (.fst (.app (subbF ib) (.pair .ff (.pair (.snd v0) (.fst v0)))))
    (.fst (.app (subbF ib) (.pair .ff v0)))

theorem eq_valid {ib i : ℕ} (hb : ∀ x, (subbF ib).ValidAt P x)
    (hP : P[i]? = some (eqBody ib).compile) : ∀ x, (eqF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩
  constructor <;> tm_auto [eqBody, hb]

/-- `max a b`. -/
@[simps] def maxF (i : ℕ) : FnSig (.prod .nat .nat) .nat where
  idx := i
  den x := max x.1 x.2
  cost x := 60 * (x.1.size + x.2.size) + 80
  depth x := x.1.size + x.2.size + 3
  msize x := 4 * (x.1.size + x.2.size) + 20

def maxBody (ib : ℕ) : Tm [.prod .nat .nat] .nat :=
  .ite (.fst (.app (subbF ib) (.pair .ff (.pair (.snd v0) (.fst v0))))) (.snd v0) (.fst v0)

theorem max_valid {ib i : ℕ} (hb : ∀ x, (subbF ib).ValidAt P x)
    (hP : P[i]? = some (maxBody ib).compile) : ∀ x, (maxF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩
  constructor <;> tm_auto [maxBody, hb]

/-- `min a b`. -/
@[simps] def minF (i : ℕ) : FnSig (.prod .nat .nat) .nat where
  idx := i
  den x := min x.1 x.2
  cost x := 60 * (x.1.size + x.2.size) + 80
  depth x := x.1.size + x.2.size + 3
  msize x := 4 * (x.1.size + x.2.size) + 20

def minBody (ib : ℕ) : Tm [.prod .nat .nat] .nat :=
  .ite (.fst (.app (subbF ib) (.pair .ff (.pair (.snd v0) (.fst v0))))) (.fst v0) (.snd v0)

theorem min_valid {ib i : ℕ} (hb : ∀ x, (subbF ib).ValidAt P x)
    (hP : P[i]? = some (minBody ib).compile) : ∀ x, (minF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩
  constructor <;> tm_auto [minBody, hb]

/-! ## Halving, parity -/

@[simps] def div2F (i : ℕ) : FnSig .nat .nat where
  idx := i
  den n := n / 2
  cost _ := 12
  depth _ := 1
  msize _ := 5

def div2Body : Tm [.nat] .nat := .div2 v0

theorem div2_valid {i : ℕ} (hP : P[i]? = some div2Body.compile) :
    ∀ n, (div2F i).ValidAt P n := by
  refine FnSig.valid_of_body_nonrec _ _ hP fun (n : ℕ) => ?_
  by_cases hn : n = 0 <;> constructor <;> tm_auto [div2Body, hn]

@[simps] def mod2F (i : ℕ) : FnSig .nat .nat where
  idx := i
  den n := n % 2
  cost _ := 12
  depth _ := 1
  msize _ := 5

def mod2Body : Tm [.nat] .nat := .ncase v0 .zero (.ite v0 (.lit (1 : ℕ)) .zero)

theorem mod2_valid {i : ℕ} (hP : P[i]? = some mod2Body.compile) :
    ∀ n, (mod2F i).ValidAt P n := by
  refine FnSig.valid_of_body_nonrec _ _ hP fun (n : ℕ) => ?_
  by_cases hn : n = 0
  · constructor <;> tm_auto [mod2Body, hn]
  · rcases Nat.mod_two_cases n with h | h <;> constructor <;> tm_auto [mod2Body, hn, h]

@[simps] def oddF (i : ℕ) : FnSig .nat .bool where
  idx := i
  den n := decide (n % 2 = 1)
  cost _ := 12
  depth _ := 1
  msize _ := 5

def oddBody : Tm [.nat] .bool := .odd v0

theorem odd_valid {i : ℕ} (hP : P[i]? = some oddBody.compile) :
    ∀ n, (oddF i).ValidAt P n := by
  refine FnSig.valid_of_body_nonrec _ _ hP fun (n : ℕ) => ?_
  by_cases hn : n = 0 <;> constructor <;> tm_auto [oddBody, hn]

/-! ## Bit length -/

/-- `Nat.size n` (number of binary digits). -/
@[simps] def bitLenF (i : ℕ) : FnSig .nat .nat where
  idx := i
  den n := n.size
  cost n := 30 * (n.size + 1) * (n.size + 1)
  depth n := 2 * n.size + 2
  msize n := 4 * n.size + 10

def bitLenBody (is i : ℕ) : Tm [.nat] .nat :=
  .ncase v0 .zero (.app (succF is) (.app (bitLenF i) v1))

theorem bitLen_valid {is i : ℕ} (hs : ∀ n, (succF is).ValidAt P n)
    (hP : P[i]? = some (bitLenBody is i).compile) : ∀ n, (bitLenF i).ValidAt P n := by
  refine FnSig.valid_of_body _ _ hP (fun n => n) fun (n : ℕ) ih => ?_
  by_cases hn : n = 0
  · subst hn; constructor <;> tm_auto [bitLenBody]
  · have hsz := size_half hn
    have hih := ih (n / 2) (by omega)
    constructor
    · tm_auto [bitLenBody, hn, hs, hih]
    · tm_auto [bitLenBody, hn, hs, hih]
    · tm_unfold [bitLenBody, hn]
      have h1 := size_le_self (n / 2).size
      rw [← hsz]
      nlinarith
    · tm_auto [bitLenBody, hn, hs, hih]
    · tm_auto [bitLenBody, hn, hs, hih]

/-! ## Multiplication (shift and add) -/

/-- Cost bound of `mulF` (kept folded so that callers' cost goals stay linear). -/
def mulCost (a b : ℕ) : ℕ := 100 * (a.size + 1) * (a.size + b.size + 1)

theorem mulCost_le (a b S : ℕ) (h : a.size + b.size ≤ S) : mulCost a b ≤ 100 * (S + 1) * (S + 1) := by
  unfold mulCost
  have h1 : a.size + 1 ≤ S + 1 := by omega
  have h2 : a.size + b.size + 1 ≤ S + 1 := by omega
  calc 100 * (a.size + 1) * (a.size + b.size + 1) ≤ 100 * (S + 1) * (a.size + b.size + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    _ ≤ 100 * (S + 1) * (S + 1) := Nat.mul_le_mul_left _ h2

@[simps] def mulF (i : ℕ) : FnSig (.prod .nat .nat) .nat where
  idx := i
  den x := x.1 * x.2
  cost x := mulCost x.1 x.2
  depth x := 2 * (x.1.size + x.2.size) + 4
  msize x := 8 * (x.1.size + x.2.size) + 40

def mulBody (ia i : ℕ) : Tm [.prod .nat .nat] .nat :=
  .ncase (.fst v0) .zero
    (.letE (.app (mulF i) (.pair v1 (.snd v2)))
      (.letE (.bit .ff v0)
        (.ite v2 (.app (addF ia) (.pair v0 (.snd v4))) v0)))

theorem mul_valid {ia i : ℕ} (hadd : ∀ x, (addF ia).ValidAt P x)
    (hP : P[i]? = some (mulBody ia i).compile) : ∀ x, (mulF i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.1) ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩ ih
  by_cases ha : a = 0
  · subst ha; constructor <;> tm_auto [mulBody, mulCost]
  have hsa := size_half ha
  have hih := ih (a / 2, b) (by dsimp only; omega)
  have hab := size_mul_le (a / 2) b
  rcases Nat.mod_two_cases a with h2 | h2
  · constructor
    · tm_auto [mulBody, ha, h2, hadd, hih]
    · tm_unfold [mulBody, ha, h2]
      rw [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h2)]
    · tm_unfold [mulBody, ha, h2, mulCost]
      rw [← hsa]
      nlinarith
    · tm_auto [mulBody, ha, h2, hadd, hih]
    · tm_auto [mulBody, ha, h2, hadd, hih]
  · constructor
    · tm_auto [mulBody, ha, h2, hadd, hih]
    · tm_unfold [mulBody, ha, h2]
      have : a = 2 * (a / 2) + 1 := by omega
      conv_rhs => rw [this]
      ring
    · tm_unfold [mulBody, ha, h2, mulCost]
      size_bounds
      rw [← hsa]
      nlinarith
    · tm_auto [mulBody, ha, h2, hadd, hih]
    · tm_auto [mulBody, ha, h2, hadd, hih]

end QecReliability.FL.Lib
