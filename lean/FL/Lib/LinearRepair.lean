import FL.Lib.List
import PhysicalBridge.LinearRepairScan

/-!
# Worked example: `RationalOutput.LinearRepair.run` in FL

The measured repair scan (`PhysicalBridge/LinearRepairScan.lean`) walks two count lists,
building a ratio per pair, keeping the running minimum (`Ratio.lesser`, compared by
cross-multiplication) and optionally clamping it from below (`Ratio.greater`), while
maintaining five counters.

Data representation (`Ty`):
* `Ratio` ↦ `R = nat × nat` (`toR x = (x.num, x.den)`; the proofs are dropped);
* the constants `(shape, r, a, ell)` ↦ `CTy = bool × nat × R × R`;
* `Result` ↦ `ResTy = list R × nat × nat × nat × nat × nat` (`toRes`).

Lean side: `lesserR`, `greaterR`, `countsR`, `entryR` (one step's three ratios), `accR`
(one step's result update) and `runR`, with `runR_toR : runR … = toRes (run …)`.

FL side (one global function each): `lesserF`, `greaterF`, `countsF`, `entryF` (one step's
ratios), `ctrF` (counters), `mdF` (running max of denominators), `accF` (assembles the new
record), `runF` (the scan), each with a `*_valid` theorem; the final statement is
`run_transcribed`. Bounds: `lesser_cost_le`, `entryCost_le`, `entryDepth_le`, and for the
whole scan `runCost_le` / `runDepth_le`: if every numerator/denominator of `a`, `ell`,
`prev`, every `g.1 + b.1`, `r`, and `j + 6 n + 6` have bit length `≤ B` (`n` = number of
pairs), then cost `≤ 16000 (n + 1) (B + 1)²` and depth `≤ n + 20 B + 41`. The size budget
`runMsize` is the explicit recursive maximum of the per-step budgets (callee budgets plus the
encoded sizes of the three argument tuples); a closed form for it is not proved here.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.FL.Lib.LinearRepairFL

open Tm NatSize RationalOutput

/-! ## Lean side on the representation -/

/-! The data types are notations (not definitions), so that no unfolding is ever needed and
`omega` sees one spelling of each encoded size. -/
local notation "TR" => Ty.prod Ty.nat Ty.nat
local notation "TC" => Ty.prod Ty.bool (Ty.prod Ty.nat (Ty.prod TR TR))
local notation "TE" => Ty.prod TR (Ty.prod TR TR)
local notation "TRes" =>
  Ty.prod (Ty.list TR) (Ty.prod Ty.nat (Ty.prod Ty.nat (Ty.prod Ty.nat (Ty.prod Ty.nat Ty.nat))))
local notation "TEArg" => Ty.prod TC (Ty.prod Ty.nat (Ty.prod TR (Ty.prod TR TR)))
local notation "TAArg" => Ty.prod TC (Ty.prod Ty.nat (Ty.prod TR (Ty.prod TE TRes)))
local notation "TArg" => Ty.prod TC (Ty.prod Ty.nat (Ty.prod TR (Ty.prod (Ty.list TR) (Ty.list TR))))

def toR (x : Ratio) : ℕ × ℕ := (x.num, x.den)

def toRes (x : LinearRepair.Result) : Ty.den (TRes) :=
  (x.values.map toR, x.pairVisits, x.ratioBuilds, x.orderComparisons, x.endpointTests,
    x.maxAccumulatorDen)

def lesserR (x y : ℕ × ℕ) : ℕ × ℕ := if x.1 * y.2 ≤ y.1 * x.2 then x else y
def greaterR (x y : ℕ × ℕ) : ℕ × ℕ := if x.1 * y.2 ≤ y.1 * x.2 then y else x
def countsR (a b : ℕ) : ℕ × ℕ := if a + b = 0 then (0, 1) else (a, a + b)

theorem toR_lesser (x y : Ratio) : toR (Ratio.lesser x y) = lesserR (toR x) (toR y) := by
  unfold Ratio.lesser lesserR toR; split_ifs <;> rfl
theorem toR_greater (x y : Ratio) : toR (Ratio.greater x y) = greaterR (toR x) (toR y) := by
  unfold Ratio.greater greaterR toR; split_ifs <;> rfl
theorem toR_counts (a b : ℕ) : toR (Ratio.counts a b) = countsR a b := by
  unfold Ratio.counts countsR toR; split_ifs <;> rfl

theorem lesserR_eq (x y : Ratio) :
    lesserR (x.num, x.den) (y.num, y.den) = ((Ratio.lesser x y).num, (Ratio.lesser x y).den) :=
  toR_lesser x y |>.symm
theorem greaterR_eq (x y : Ratio) :
    greaterR (x.num, x.den) (y.num, y.den) = ((Ratio.greater x y).num, (Ratio.greater x y).den) :=
  toR_greater x y |>.symm
theorem countsR_eq (a b : ℕ) :
    countsR a b = ((Ratio.counts a b).num, (Ratio.counts a b).den) := toR_counts a b |>.symm

/-- One step: `(e, current, output)`. `c = (shape, r, a, ell)`. -/
def entryR (c : Ty.den (TC)) (j : ℕ) (prev g b : ℕ × ℕ) : Ty.den (TE) :=
  let e : ℕ × ℕ := if j = 0 then c.2.2.1 else if j = c.2.1 then c.2.2.2 else countsR g.1 b.1
  let cur : ℕ × ℕ := if j = 0 then e else lesserR prev e
  (e, cur, if c.1 then greaterR c.2.2.2 cur else e)

/-- One step's update of the result record. -/
def accR (c : Ty.den (TC)) (j : ℕ) (prev : ℕ × ℕ) (t : Ty.den (TE)) (rest : Ty.den (TRes)) : Ty.den (TRes) :=
  (t.2.2 :: rest.1, rest.2.1 + 1,
    rest.2.2.1 + (if j = 0 ∨ j = c.2.1 then 0 else 1),
    rest.2.2.2.1 + (if j = 0 then 0 else 1) + (if c.1 then 1 else 0),
    rest.2.2.2.2.1 + (if j = 0 then 1 else 2),
    max prev.2 (max t.1.2 (max t.2.1.2 (max t.2.2.2 rest.2.2.2.2.2))))

def runR (c : Ty.den (TC)) : ℕ → ℕ × ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Ty.den (TRes)
  | _, prev, [], _ => ([], 0, 0, 0, 0, prev.2)
  | _, prev, _ :: _, [] => ([], 0, 0, 0, 0, prev.2)
  | j, prev, g :: gs, b :: bs =>
    accR c j prev (entryR c j prev g b) (runR c (j + 1) (entryR c j prev g b).2.1 gs bs)

/-- The representation commutes with the scan. -/
theorem runR_toR (shape : Bool) (r : ℕ) (a ell : Ratio) (gs bs : List (ℕ × ℕ)) (j : ℕ)
    (prev : Ratio) :
    runR (shape, r, toR a, toR ell) j (toR prev) gs bs =
      toRes (LinearRepair.run shape r a ell j prev gs bs) := by
  induction gs generalizing bs j prev with
  | nil => simp [runR, LinearRepair.run, toRes, toR]
  | cons g gs ih =>
    cases bs with
    | nil => simp [runR, LinearRepair.run, toRes, toR]
    | cons b bs =>
      have hcur : (entryR (shape, r, toR a, toR ell) j (toR prev) g b).2.1 =
          toR (if j = 0 then LinearRepair.sourceEntry r a ell j g b
            else Ratio.lesser prev (LinearRepair.sourceEntry r a ell j g b)) := by
        unfold entryR LinearRepair.sourceEntry
        split_ifs <;> simp [toR_lesser, toR_counts]
      rw [runR, LinearRepair.run, hcur, ih]
      unfold accR entryR toRes LinearRepair.sourceEntry
      split_ifs <;> simp_all [lesserR_eq, greaterR_eq, countsR_eq, toR]

/-! ## FL: ratio comparison and construction -/

variable {P : Program}

/-- `lesser (x, y)`: compare `x.1 * y.2 ≤ y.1 * x.2` (two multiplications and one `≤`). -/
@[simps] def lesserF (i : ℕ) : FnSig (.prod TR TR) TR where
  idx := i
  den p := lesserR p.1 p.2
  cost p := mulCost p.1.1 p.2.2 + mulCost p.2.1 p.1.2 +
    60 * ((p.1.1 * p.2.2).size + (p.2.1 * p.1.2).size) + 120
  depth p := 2 * (p.1.1.size + p.1.2.size + p.2.1.size + p.2.2.size) + 10
  msize p := 8 * (p.1.1.size + p.1.2.size + p.2.1.size + p.2.2.size) + 60

def lesserBody (imul ile : ℕ) : Tm [.prod TR TR] TR :=
  .ite (.app (leF ile) (.pair (.app (mulF imul) (.pair (.fst (.fst v0)) (.snd (.snd v0))))
                              (.app (mulF imul) (.pair (.fst (.snd v0)) (.snd (.fst v0))))))
    (.fst v0) (.snd v0)

theorem lesser_valid {imul ile i : ℕ} (hmul : ∀ x, (mulF imul).ValidAt P x)
    (hle : ∀ x, (leF ile).ValidAt P x) (hP : P[i]? = some (lesserBody imul ile).compile) :
    ∀ p, (lesserF i).ValidAt P p := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨⟨(x1 : ℕ), (x2 : ℕ)⟩, ⟨(y1 : ℕ), (y2 : ℕ)⟩⟩
  constructor <;> tm_auto [lesserBody, hmul, hle, lesserR]

/-- `greater (x, y)`. -/
@[simps] def greaterF (i : ℕ) : FnSig (.prod TR TR) TR where
  idx := i
  den p := greaterR p.1 p.2
  cost p := mulCost p.1.1 p.2.2 + mulCost p.2.1 p.1.2 +
    60 * ((p.1.1 * p.2.2).size + (p.2.1 * p.1.2).size) + 120
  depth p := 2 * (p.1.1.size + p.1.2.size + p.2.1.size + p.2.2.size) + 10
  msize p := 8 * (p.1.1.size + p.1.2.size + p.2.1.size + p.2.2.size) + 60

def greaterBody (imul ile : ℕ) : Tm [.prod TR TR] TR :=
  .ite (.app (leF ile) (.pair (.app (mulF imul) (.pair (.fst (.fst v0)) (.snd (.snd v0))))
                              (.app (mulF imul) (.pair (.fst (.snd v0)) (.snd (.fst v0))))))
    (.snd v0) (.fst v0)

theorem greater_valid {imul ile i : ℕ} (hmul : ∀ x, (mulF imul).ValidAt P x)
    (hle : ∀ x, (leF ile).ValidAt P x) (hP : P[i]? = some (greaterBody imul ile).compile) :
    ∀ p, (greaterF i).ValidAt P p := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨⟨(x1 : ℕ), (x2 : ℕ)⟩, ⟨(y1 : ℕ), (y2 : ℕ)⟩⟩
  constructor <;> tm_auto [greaterBody, hmul, hle, greaterR]

/-- Closed-form bound for `lesserF`/`greaterF` (same cost). -/
theorem lesser_cost_le (i : ℕ) (p : (Ty.prod TR TR).den) (S : ℕ)
    (hS : p.1.1.size + p.1.2.size + p.2.1.size + p.2.2.size ≤ S) :
    (lesserF i).cost p ≤ 400 * (S + 1) * (S + 1) := by
  simp only [lesserF_cost]
  have h1 := mulCost_le p.1.1 p.2.2 S (by omega)
  have h2 := mulCost_le p.2.1 p.1.2 S (by omega)
  have h3 := size_mul_le p.1.1 p.2.2
  have h4 := size_mul_le p.2.1 p.1.2
  nlinarith

theorem greater_cost_eq (i j : ℕ) (p : (Ty.prod TR TR).den) :
    (greaterF i).cost p = (lesserF j).cost p := rfl

/-- `counts (a, b) = if a + b = 0 then (0, 1) else (a, a + b)`. -/
@[simps] def countsF (i : ℕ) : FnSig (.prod .nat .nat) TR where
  idx := i
  den p := countsR p.1 p.2
  cost p := 50 * (p.1.size + p.2.size) + 100
  depth p := p.1.size + p.2.size + 5
  msize p := 8 * (p.1.size + p.2.size) + 40

def countsBody (iadd : ℕ) : Tm [.prod .nat .nat] TR :=
  .letE (.app (addF iadd) v0) (.ite (.isZero v0) (.lit ((0, 1) : ℕ × ℕ)) (.pair (.fst v1) v0))

theorem counts_valid {iadd i : ℕ} (hadd : ∀ x, (addF iadd).ValidAt P x)
    (hP : P[i]? = some (countsBody iadd).compile) : ∀ p, (countsF i).ValidAt P p := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(a : ℕ), (b : ℕ)⟩
  constructor <;> tm_auto [countsBody, hadd, countsR]

/-! ## FL: one step -/

/-- Arguments of the calls made by one step (for the cost of `entryF`). -/
def entryCost (x : Ty.den (TEArg)) : ℕ :=
  (eqF 0).cost (x.2.1, x.1.2.1) + (countsF 0).cost (x.2.2.2.1.1, x.2.2.2.2.1) +
    (lesserF 0).cost (x.2.2.1, (entryR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1) +
    (greaterF 0).cost (x.1.2.2.2, (entryR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2.1) + 100

def entryDepth (x : Ty.den (TEArg)) : ℕ :=
  (eqF 0).depth (x.2.1, x.1.2.1) + (countsF 0).depth (x.2.2.2.1.1, x.2.2.2.2.1) +
    (lesserF 0).depth (x.2.2.1, (entryR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1) +
    (greaterF 0).depth (x.1.2.2.2, (entryR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2.1) + 5

def entryMsize (x : Ty.den (TEArg)) : ℕ :=
  (eqF 0).msize (x.2.1, x.1.2.1) + (countsF 0).msize (x.2.2.2.1.1, x.2.2.2.2.1) +
    (lesserF 0).msize (x.2.2.1, (entryR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).1) +
    (greaterF 0).msize (x.1.2.2.2, (entryR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).2.1) +
    2 * (Ty.enc (TEArg) x).size + 2 * (Ty.enc (TE) (entryR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)).size + 20

/-- One step: `(e, current, output)` from `(c, j, prev, g, b)`. -/
@[simps] def entryF (i : ℕ) : FnSig TEArg TE where
  idx := i
  den x := entryR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  cost := entryCost
  depth := entryDepth
  msize := entryMsize

def entryBody (ieq icounts iles igrt : ℕ) : Tm [TEArg] TE :=
  .letE
    (.ite (.isZero (.fst (.snd v0)))
      (.fst (.snd (.snd (.fst v0))))
      (.ite (.app (eqF ieq) (.pair (.fst (.snd v0)) (.fst (.snd (.fst v0)))))
        (.snd (.snd (.snd (.fst v0))))
        (.app (countsF icounts)
          (.pair (.fst (.fst (.snd (.snd (.snd v0))))) (.fst (.snd (.snd (.snd (.snd v0)))))))))
    (.letE
      (.ite (.isZero (.fst (.snd v1))) v0 (.app (lesserF iles) (.pair (.fst (.snd (.snd v1))) v0)))
      (.pair v1 (.pair v0
        (.ite (.fst (.fst v2)) (.app (greaterF igrt) (.pair (.snd (.snd (.snd (.fst v2)))) v0))
          v1))))

set_option maxHeartbeats 4000000 in
theorem entry_valid {ieq icounts iles igrt i : ℕ} (heq : ∀ x, (eqF ieq).ValidAt P x)
    (hcounts : ∀ x, (countsF icounts).ValidAt P x) (hles : ∀ x, (lesserF iles).ValidAt P x)
    (hgrt : ∀ x, (greaterF igrt).ValidAt P x)
    (hP : P[i]? = some (entryBody ieq icounts iles igrt).compile) :
    ∀ x, (entryF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨⟨shape, (r : ℕ), ⟨(a1 : ℕ), (a2 : ℕ)⟩, ⟨(l1 : ℕ), (l2 : ℕ)⟩⟩, (j : ℕ),
    ⟨(p1 : ℕ), (p2 : ℕ)⟩, ⟨(g1 : ℕ), (g2 : ℕ)⟩, ⟨(b1 : ℕ), (b2 : ℕ)⟩⟩
  by_cases hj : j = 0
  · subst hj
    cases shape <;> constructor <;>
      tm_auto [entryBody, entryR, entryCost, entryDepth, entryMsize, heq, hcounts, hles, hgrt]
  · by_cases hjr : j = r
    · subst hjr
      cases shape <;> constructor <;>
        tm_auto [entryBody, entryR, entryCost, entryDepth, entryMsize, heq, hcounts, hles, hgrt,
          hj]
    · cases shape <;> constructor <;>
        tm_auto [entryBody, entryR, entryCost, entryDepth, entryMsize, heq, hcounts, hles, hgrt,
          hj, hjr]

/-! ## FL: one step's update of the result record

Split into two small functions (`ctrF`: the four counters; `mdF`: the running maximum of
denominators) and an assembling body `accF`, so that no single body is large. -/

/-- The four counters of one step. -/
def ctrR (j r : ℕ) (shape : Bool) (pv rb oc et : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (pv + 1, rb + (if j = 0 ∨ j = r then 0 else 1),
    oc + (if j = 0 then 0 else 1) + (if shape then 1 else 0), et + (if j = 0 then 1 else 2))

/-- `(j, r, shape, pv, rb, oc, et) ↦ ctrR …`. -/
@[simps] def ctrF (i : ℕ) : FnSig (.prod .nat (.prod .nat (.prod .bool (.prod .nat (.prod .nat
    (.prod .nat .nat)))))) (.prod .nat (.prod .nat (.prod .nat .nat))) where
  idx := i
  den x := ctrR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2
  cost x := 150 * (x.2.2.2.1 + x.2.2.2.2.1 + x.2.2.2.2.2.1 + x.2.2.2.2.2.2 + 2).size +
    120 * (x.1.size + x.2.1.size) + 400
  depth x := (x.2.2.2.1 + x.2.2.2.2.1 + x.2.2.2.2.2.1 + x.2.2.2.2.2.2 + 2).size +
    x.1.size + x.2.1.size + 10
  msize x := 20 * (x.2.2.2.1 + x.2.2.2.2.1 + x.2.2.2.2.2.1 + x.2.2.2.2.2.2 + 2).size +
    8 * (x.1.size + x.2.1.size) + 100

def ctrBody (isucc ieq : ℕ) : Tm [.prod .nat (.prod .nat (.prod .bool (.prod .nat (.prod .nat
    (.prod .nat .nat)))))] (.prod .nat (.prod .nat (.prod .nat .nat))) :=
  .pair (.app (succF isucc) (.fst (.snd (.snd (.snd v0)))))
    (.pair (.ite (.or (.isZero (.fst v0)) (.app (eqF ieq) (.pair (.fst v0) (.fst (.snd v0)))))
              (.fst (.snd (.snd (.snd (.snd v0)))))
              (.app (succF isucc) (.fst (.snd (.snd (.snd (.snd v0)))))))
      (.pair (.letE (.ite (.isZero (.fst v0)) (.fst (.snd (.snd (.snd (.snd (.snd v0))))))
                (.app (succF isucc) (.fst (.snd (.snd (.snd (.snd (.snd v0))))))))
              (.ite (.fst (.snd (.snd v1))) (.app (succF isucc) v0) v0))
        (.ite (.isZero (.fst v0)) (.app (succF isucc) (.snd (.snd (.snd (.snd (.snd (.snd v0)))))))
          (.app (succF isucc) (.app (succF isucc) (.snd (.snd (.snd (.snd (.snd (.snd v0)))))))))))

set_option maxHeartbeats 1000000 in
theorem ctr_valid {isucc ieq i : ℕ} (hs : ∀ x, (succF isucc).ValidAt P x)
    (heq : ∀ x, (eqF ieq).ValidAt P x) (hP : P[i]? = some (ctrBody isucc ieq).compile) :
    ∀ x, (ctrF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(j : ℕ), (r : ℕ), shape, (pv : ℕ), (rb : ℕ), (oc : ℕ), (et : ℕ)⟩
  have m1 := size_mono (show pv ≤ pv + rb + oc + et + 2 by omega)
  have m2 := size_mono (show rb + 1 ≤ pv + rb + oc + et + 2 by omega)
  have m3 := size_mono (show oc + 1 ≤ pv + rb + oc + et + 2 by omega)
  have m4 := size_mono (show et + 1 ≤ pv + rb + oc + et + 2 by omega)
  have m5 := size_succ_le (pv + rb + oc + et + 2)
  have m6 := size_mono (show oc + 1 + 1 ≤ pv + rb + oc + et + 2 + 1 by omega)
  have m7 := size_mono (show et + 1 + 1 ≤ pv + rb + oc + et + 2 + 1 by omega)
  have m8 := size_mono (show pv + 1 ≤ pv + rb + oc + et + 2 by omega)
  have m9 := size_mono (show rb ≤ pv + rb + oc + et + 2 by omega)
  have m10 := size_mono (show oc ≤ pv + rb + oc + et + 2 by omega)
  have m11 := size_mono (show et ≤ pv + rb + oc + et + 2 by omega)
  by_cases hj : j = 0
  · subst hj
    cases shape <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (tm_lean [ctrBody, succF_cost, succF_depth, succF_msize, succF_den, eqF_cost, eqF_depth,
          eqF_msize, eqF_den, hs, heq]; done)
      | tm_auto [ctrBody, ctrR]
  · by_cases hjr : j = r
    · subst hjr
      cases shape <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        first
        | (tm_lean [ctrBody, succF_cost, succF_depth, succF_msize, succF_den, eqF_cost, eqF_depth,
            eqF_msize, eqF_den, hs, heq, hj]; done)
        | tm_auto [ctrBody, ctrR, hj]
    · cases shape <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        first
        | (tm_lean [ctrBody, succF_cost, succF_depth, succF_msize, succF_den, eqF_cost, eqF_depth,
            eqF_msize, eqF_den, hs, heq, hj, hjr]; done)
        | tm_auto [ctrBody, ctrR, hj, hjr]

/-- `max p2 (max e2 (max c2 (max o2 mad)))`. -/
@[simps] def mdF (i : ℕ) : FnSig (.prod .nat (.prod .nat (.prod .nat (.prod .nat .nat)))) .nat where
  idx := i
  den x := max x.1 (max x.2.1 (max x.2.2.1 (max x.2.2.2.1 x.2.2.2.2)))
  cost x := 240 * (x.1.size + x.2.1.size + x.2.2.1.size + x.2.2.2.1.size + x.2.2.2.2.size) + 400
  depth x := x.1.size + x.2.1.size + x.2.2.1.size + x.2.2.2.1.size + x.2.2.2.2.size + 10
  msize x := 8 * (x.1.size + x.2.1.size + x.2.2.1.size + x.2.2.2.1.size + x.2.2.2.2.size) + 40

def mdBody (imax : ℕ) : Tm [.prod .nat (.prod .nat (.prod .nat (.prod .nat .nat)))] .nat :=
  .app (maxF imax) (.pair (.fst v0)
    (.app (maxF imax) (.pair (.fst (.snd v0))
      (.app (maxF imax) (.pair (.fst (.snd (.snd v0)))
        (.app (maxF imax) (.pair (.fst (.snd (.snd (.snd v0)))) (.snd (.snd (.snd (.snd v0)))))))))))

theorem md_valid {imax i : ℕ} (hmax : ∀ x, (maxF imax).ValidAt P x)
    (hP : P[i]? = some (mdBody imax).compile) : ∀ x, (mdF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(p : ℕ), (e : ℕ), (c : ℕ), (o : ℕ), (m : ℕ)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · tm_lean [mdBody, hmax]
  · simp only [tm_simp, mdBody, mdF_den, maxF_den]
  · tm_lean [mdBody, maxF_cost, mdF_cost, maxF_den]
  · tm_lean [mdBody, maxF_depth, mdF_depth, maxF_den]
  · tm_lean [mdBody, maxF_msize, mdF_msize, maxF_den]

section Acc
variable {Γ : List Ty} (x : Tm Γ (TAArg))
abbrev aShape : Tm Γ .bool := .fst (.fst x)
abbrev aR : Tm Γ .nat := .fst (.snd (.fst x))
abbrev aJ : Tm Γ .nat := .fst (.snd x)
abbrev aPrev : Tm Γ (TR) := .fst (.snd (.snd x))
abbrev aT : Tm Γ (TE) := .fst (.snd (.snd (.snd x)))
abbrev aRest : Tm Γ (TRes) := .snd (.snd (.snd (.snd x)))
end Acc

/-- Arguments of the two calls made by `accF`. -/
def ctrArg (x : Ty.den (TAArg)) : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ :=
  (x.2.1, x.1.2.1, x.1.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1)
def mdArg (x : Ty.den (TAArg)) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (x.2.2.1.2, x.2.2.2.1.1.2, x.2.2.2.1.2.1.2, x.2.2.2.1.2.2.2, x.2.2.2.2.2.2.2.2.2)

/-- `acc (c, j, prev, (e, cur, out), rest) = accR …`. -/
@[simps] def accF (i : ℕ) : FnSig (TAArg) (TRes) where
  idx := i
  den x := accR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  cost x := (ctrF 0).cost (ctrArg x) + (mdF 0).cost (mdArg x) + 300
  depth x := (ctrF 0).depth (ctrArg x) + (mdF 0).depth (mdArg x) + 2
  msize x := 2 * (Ty.enc (TAArg) x).size + (ctrF 0).msize (ctrArg x) + (mdF 0).msize (mdArg x) +
    (Ty.enc (.prod .nat (.prod .nat (.prod .nat .nat))) ((ctrF 0).den (ctrArg x))).size +
    (Ty.enc .nat ((mdF 0).den (mdArg x))).size + 20

def accBody (ictr imd : ℕ) : Tm [TAArg] (TRes) :=
  .pair (.lcons (.snd (.snd (aT v0))) (.fst (aRest v0)))
    (.letE (.app (ctrF ictr) (.pair (aJ v0) (.pair (aR v0) (.pair (aShape v0)
        (.pair (.fst (.snd (aRest v0))) (.pair (.fst (.snd (.snd (aRest v0))))
          (.pair (.fst (.snd (.snd (.snd (aRest v0))))) (.fst (.snd (.snd (.snd (.snd (aRest v0)))))))))))))
      (.pair (.fst v0) (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0)))
        (.pair (.snd (.snd (.snd v0)))
          (.app (mdF imd) (.pair (.snd (aPrev v1)) (.pair (.snd (.fst (aT v1)))
            (.pair (.snd (.fst (.snd (aT v1)))) (.pair (.snd (.snd (.snd (aT v1))))
              (.snd (.snd (.snd (.snd (.snd (aRest v1))))))))))))))))

theorem acc_valid {ictr imd i : ℕ} (hctr : ∀ x, (ctrF ictr).ValidAt P x)
    (hmd : ∀ x, (mdF imd).ValidAt P x) (hP : P[i]? = some (accBody ictr imd).compile) :
    ∀ x, (accF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨⟨shape, (r : ℕ), a, ell⟩, (j : ℕ), ⟨(p1 : ℕ), (p2 : ℕ)⟩,
    ⟨⟨(e1 : ℕ), (e2 : ℕ)⟩, ⟨(c1 : ℕ), (c2 : ℕ)⟩, ⟨(o1 : ℕ), (o2 : ℕ)⟩⟩,
    vals, (pv : ℕ), (rb : ℕ), (oc : ℕ), (et : ℕ), (mad : ℕ)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · tm_lean [accBody, hctr, hmd]
  · simp only [tm_simp, accBody, accF_den, ctrF_den, mdF_den, accR, ctrR]
  · tm_lean [accBody, accF_cost, ctrArg, mdArg, ctrF_cost, mdF_cost]
  · tm_lean [accBody, accF_depth, ctrArg, mdArg, ctrF_depth, mdF_depth]
  · tm_lean [accBody, accF_msize, ctrArg, mdArg, ctrF_den, mdF_den, ctrF_msize, mdF_msize]

/-! ## FL: the scan -/

def runCost (c : Ty.den (TC)) : ℕ → ℕ × ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ
  | _, _, [], _ => 40
  | _, _, _ :: _, [] => 50
  | j, prev, g :: gs, b :: bs =>
    entryCost (c, j, prev, g, b) + (25 * j.size + 25) +
      runCost c (j + 1) (entryR c j prev g b).2.1 gs bs +
      (accF 0).cost (c, j, prev, entryR c j prev g b,
        runR c (j + 1) (entryR c j prev g b).2.1 gs bs) + 100

def runDepth (c : Ty.den (TC)) : ℕ → ℕ × ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ
  | _, _, [], _ => 1
  | _, _, _ :: _, [] => 1
  | j, prev, g :: gs, b :: bs =>
    max (entryDepth (c, j, prev, g, b)) (max (j.size + 1)
      (max (runDepth c (j + 1) (entryR c j prev g b).2.1 gs bs)
        ((accF 0).depth (c, j, prev, entryR c j prev g b,
          runR c (j + 1) (entryR c j prev g b).2.1 gs bs)))) + 1

def runMsize (c : Ty.den (TC)) : ℕ → ℕ × ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ
  | _, prev, [], _ => 4 * prev.2.size + 20
  | _, prev, _ :: _, [] => 4 * prev.2.size + 20
  | j, prev, g :: gs, b :: bs =>
    max (runMsize c (j + 1) (entryR c j prev g b).2.1 gs bs)
      (entryMsize (c, j, prev, g, b) + (4 * j.size + 10) +
        (accF 0).msize (c, j, prev, entryR c j prev g b,
          runR c (j + 1) (entryR c j prev g b).2.1 gs bs) +
        (Ty.enc (TEArg) (c, j, prev, g, b)).size +
        (Ty.enc (TArg) (c, j + 1, (entryR c j prev g b).2.1, gs, bs)).size +
        (Ty.enc (TAArg) (c, j, prev, entryR c j prev g b,
          runR c (j + 1) (entryR c j prev g b).2.1 gs bs)).size + 10)

/-- `run (c, j, prev, gs, bs) = runR c j prev gs bs`. -/
@[simps] def runF (i : ℕ) : FnSig (TArg) (TRes) where
  idx := i
  den x := runR x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  cost x := runCost x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  depth x := runDepth x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  msize x := runMsize x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The empty result `([], 0, 0, 0, 0, prev.den)`, for an argument term `x`. -/
abbrev nilRes {Γ : List Ty} (x : Tm Γ (TArg)) : Tm Γ (TRes) :=
  .pair .lnil (.pair .zero (.pair .zero (.pair .zero (.pair .zero (.snd (.fst (.snd (.snd x))))))))

def runBody (is ient iacc i : ℕ) : Tm [TArg] (TRes) :=
  .lcase (.fst (.snd (.snd (.snd v0))))
    (nilRes v0)
    (.lcase (.snd (.snd (.snd (.snd v2))))
      (nilRes v2)
      (.letE (.app (entryF ient)
          (.pair (.fst v4) (.pair (.fst (.snd v4)) (.pair (.fst (.snd (.snd v4))) (.pair v2 v0)))))
        (.letE (.app (runF i)
            (.pair (.fst v5) (.pair (.app (succF is) (.fst (.snd v5)))
              (.pair (.fst (.snd v0)) (.pair v4 v2)))))
          (.app (accF iacc)
            (.pair (.fst v6) (.pair (.fst (.snd v6)) (.pair (.fst (.snd (.snd v6))) (.pair v1 v0))))))))

set_option maxHeartbeats 10000000 in
theorem run_bodyOK {is ient iacc i : ℕ} (hs : ∀ x, (succF is).ValidAt P x)
    (hent : ∀ x, (entryF ient).ValidAt P x) (hacc : ∀ x, (accF iacc).ValidAt P x)
    (x : Ty.den (TArg)) (ih : ∀ y, (fun x : Ty.den (TArg) => x.2.2.2.1.length) y <
      (fun x : Ty.den (TArg) => x.2.2.2.1.length) x → (runF i).ValidAt P y) :
    (runF i).BodyOK P (runBody is ient iacc i) x := by
  rcases x with ⟨c, (j : ℕ), prev, (_ | ⟨g, gs⟩), bs⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (tm_lean [runBody, runCost, runDepth, runMsize, runF_cost, runF_depth, runF_msize, runF_den]; done)
      | tm_auto [runBody, runCost, runDepth, runMsize, runF_cost, runF_depth, runF_msize, runF_den, runR]
  cases bs with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (tm_lean [runBody, runCost, runDepth, runMsize, runF_cost, runF_depth, runF_msize, runF_den]; done)
      | tm_auto [runBody, runCost, runDepth, runMsize, runF_cost, runF_depth, runF_msize, runF_den, runR]
  | cons b bs =>
    have hih := ih (c, j + 1, (entryR c j prev g b).2.1, gs, bs) (by simp)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (tm_lean [runBody, runCost, runDepth, runMsize, runF_cost, runF_depth, runF_msize, runF_den, entryF_cost, entryF_depth, entryF_msize, entryF_den, succF_cost, succF_depth, succF_msize, succF_den, accF_den, accF_cost, accF_depth, accF_msize, hih, hs, hent, hacc]; done)
      | tm_auto [runBody, runCost, runDepth, runMsize, runF_cost, runF_depth, runF_msize, runF_den, runR, hih, hs, hent, hacc]

theorem run_valid {is ient iacc i : ℕ} (hs : ∀ x, (succF is).ValidAt P x)
    (hent : ∀ x, (entryF ient).ValidAt P x) (hacc : ∀ x, (accF iacc).ValidAt P x)
    (hP : P[i]? = some (runBody is ient iacc i).compile) : ∀ x, (runF i).ValidAt P x :=
  FnSig.valid_of_body _ _ hP (fun x => x.2.2.2.1.length) (run_bodyOK hs hent hacc)

/-- **The transcription.** Given the installed components, `runF i` computes the scan on the
encoded arguments, and its meaning is the representation of `LinearRepair.run`. -/
theorem run_transcribed {i : ℕ} (hrun : ∀ x, (runF i).ValidAt P x) (shape : Bool) (r : ℕ)
    (a ell : Ratio) (j : ℕ) (prev : Ratio) (gs bs : List (ℕ × ℕ)) :
    (runF i).ValidAt P ((shape, r, toR a, toR ell), j, toR prev, gs, bs) ∧
      (runF i).den ((shape, r, toR a, toR ell), j, toR prev, gs, bs) =
        toRes (LinearRepair.run shape r a ell j prev gs bs) :=
  ⟨hrun _, runR_toR shape r a ell gs bs j prev⟩

/-! ## Closed-form bounds

`RB B x`: both components of the ratio `x` have bit length `≤ B`. With all inputs bounded
this way, every intermediate ratio is one of the inputs or a `counts` (all `≤ B` bits), so
each step costs `O((B + 1)²)` (two multiplications of `B`-bit numbers dominate) and the scan
costs `O(n (B + 1)²)` for `n` pairs; the call depth is `O(n + B)`. -/

def RB (B : ℕ) (x : ℕ × ℕ) : Prop := x.1.size ≤ B ∧ x.2.size ≤ B

theorem countsR_RB {B : ℕ} (hB : 1 ≤ B) (a b : ℕ) (h : (a + b).size ≤ B) : RB B (countsR a b) := by
  unfold countsR RB
  split_ifs
  · have : (1 : ℕ).size ≤ 1 := size_le_self 1
    simp; omega
  · exact ⟨(size_mono (by omega)).trans h, h⟩

theorem lesserR_RB {B : ℕ} {x y : ℕ × ℕ} (hx : RB B x) (hy : RB B y) : RB B (lesserR x y) := by
  unfold lesserR; split_ifs <;> assumption

theorem greaterR_RB {B : ℕ} {x y : ℕ × ℕ} (hx : RB B x) (hy : RB B y) : RB B (greaterR x y) := by
  unfold greaterR; split_ifs <;> assumption

theorem entryR_RB {B : ℕ} (hB : 1 ≤ B) (c : Ty.den (TC)) (j : ℕ) (prev g b : ℕ × ℕ)
    (ha : RB B c.2.2.1) (hl : RB B c.2.2.2) (hp : RB B prev) (hgb : (g.1 + b.1).size ≤ B) :
    RB B (entryR c j prev g b).1 ∧ RB B (entryR c j prev g b).2.1 ∧
      RB B (entryR c j prev g b).2.2 := by
  let e : ℕ × ℕ := if j = 0 then c.2.2.1 else if j = c.2.1 then c.2.2.2 else countsR g.1 b.1
  have he : RB B e := by
    dsimp only [e]
    split_ifs
    · exact ha
    · exact hl
    · exact countsR_RB hB g.1 b.1 hgb
  let cur : ℕ × ℕ := if j = 0 then e else lesserR prev e
  have hcur : RB B cur := by
    dsimp only [cur]
    split_ifs
    · exact he
    · exact lesserR_RB hp he
  change RB B e ∧ RB B cur ∧ RB B (if c.1 then greaterR c.2.2.2 cur else e)
  refine ⟨he, hcur, ?_⟩
  split_ifs
  · exact greaterR_RB hl hcur
  · exact he

theorem max4_size_le (a b c d e : ℕ) :
    (max a (max b (max c (max d e)))).size ≤ max a.size (max b.size (max c.size (max d.size e.size))) := by
  rw [Nat.size_le]
  have key : ∀ x : ℕ, x.size ≤ max a.size (max b.size (max c.size (max d.size e.size))) →
      x < 2 ^ max a.size (max b.size (max c.size (max d.size e.size))) := fun x hx =>
    lt_of_lt_of_le (lt_pow_size x) (Nat.pow_le_pow_right (by omega) hx)
  simp only [max_lt_iff]
  exact ⟨key a (by omega), key b (by omega), key c (by omega), key d (by omega), key e (by omega)⟩

/-- Counters and the accumulated denominator of the result. -/
theorem runR_bounds {B : ℕ} (hB : 1 ≤ B) (c : Ty.den (TC)) (ha : RB B c.2.2.1)
    (hl : RB B c.2.2.2) (gs bs : List (ℕ × ℕ)) (hgb : ∀ g ∈ gs, ∀ b ∈ bs, (g.1 + b.1).size ≤ B) :
    ∀ (j : ℕ) (prev : ℕ × ℕ), RB B prev →
      (runR c j prev gs bs).2.1 ≤ gs.length ∧ (runR c j prev gs bs).2.2.1 ≤ gs.length ∧
      (runR c j prev gs bs).2.2.2.1 ≤ 2 * gs.length ∧
      (runR c j prev gs bs).2.2.2.2.1 ≤ 2 * gs.length ∧
      (runR c j prev gs bs).2.2.2.2.2.size ≤ B := by
  induction gs generalizing bs with
  | nil => intro j prev hp; simp [runR, hp.2]
  | cons g gs ih =>
    cases bs with
    | nil => intro j prev hp; simp [runR, hp.2]
    | cons b bs =>
      intro j prev hp
      obtain ⟨h1, h2, h3⟩ := entryR_RB hB c j prev g b ha hl hp (hgb g (by simp) b (by simp))
      obtain ⟨k1, k2, k3, k4, k5⟩ := ih bs (fun g' hg b' hb => hgb g' (by simp [hg]) b'
        (by simp [hb])) (j + 1) _ h2
      simp only [runR, accR, List.length_cons]
      simp only [Ty.den] at k1 k2 k3 k4 k5 ⊢
      refine ⟨by omega, by split_ifs <;> omega, by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
      have := max4_size_le prev.2 (entryR c j prev g b).1.2 (entryR c j prev g b).2.1.2
        (entryR c j prev g b).2.2.2 (runR c (j + 1) (entryR c j prev g b).2.1 gs bs).2.2.2.2.2
      have := hp.2; have := h1.2; have := h2.2; have := h3.2
      simp only [Ty.den] at *
      omega

theorem entryCost_le {B : ℕ} (hB : 1 ≤ B) (c : Ty.den (TC)) (j : ℕ) (prev g b : ℕ × ℕ)
    (ha : RB B c.2.2.1) (hl : RB B c.2.2.2) (hp : RB B prev) (hgb : (g.1 + b.1).size ≤ B)
    (hj : j.size ≤ B) (hr : c.2.1.size ≤ B) :
    entryCost (c, j, prev, g, b) ≤ 14000 * (B + 1) * (B + 1) := by
  obtain ⟨h1, h2, h3⟩ := entryR_RB hB c j prev g b ha hl hp hgb
  have l1 := lesser_cost_le 0 (prev, (entryR c j prev g b).1) (4 * B)
    (by have := hp.1; have := hp.2; have := h1.1; have := h1.2; simp only; omega)
  have l2 := lesser_cost_le 0 (c.2.2.2, (entryR c j prev g b).2.1) (4 * B)
    (by have := hl.1; have := hl.2; have := h2.1; have := h2.2; simp only; omega)
  have g1 := size_mono (show g.1 ≤ g.1 + b.1 by omega)
  have b1 := size_mono (show b.1 ≤ g.1 + b.1 by omega)
  unfold entryCost
  simp only [eqF_cost, countsF_cost]
  rw [greater_cost_eq 0 0]
  nlinarith

theorem entryDepth_le {B : ℕ} (hB : 1 ≤ B) (c : Ty.den (TC)) (j : ℕ) (prev g b : ℕ × ℕ)
    (ha : RB B c.2.2.1) (hl : RB B c.2.2.2) (hp : RB B prev) (hgb : (g.1 + b.1).size ≤ B)
    (hj : j.size ≤ B) (hr : c.2.1.size ≤ B) :
    entryDepth (c, j, prev, g, b) ≤ 20 * B + 40 := by
  obtain ⟨h1, h2, h3⟩ := entryR_RB hB c j prev g b ha hl hp hgb
  have g1 := size_mono (show g.1 ≤ g.1 + b.1 by omega)
  have b1 := size_mono (show b.1 ≤ g.1 + b.1 by omega)
  unfold entryDepth
  simp only [eqF_depth, countsF_depth, lesserF_depth, greaterF_depth]
  have := hp.1; have := hp.2; have := h1.1; have := h1.2; have := hl.1; have := hl.2
  have := h2.1; have := h2.2
  omega

/-- Size bookkeeping for one step of the scan (shared by the cost and depth bounds). -/
theorem step_sizes {B : ℕ} (hB : 1 ≤ B) (c : Ty.den (TC)) (ha : RB B c.2.2.1)
    (hl : RB B c.2.2.2) (j : ℕ) (prev g b : ℕ × ℕ) (gs bs : List (ℕ × ℕ)) (hp : RB B prev)
    (hgb : ∀ g' ∈ g :: gs, ∀ b' ∈ b :: bs, (g'.1 + b'.1).size ≤ B)
    (hj : (j + 6 * (gs.length + 1) + 6).size ≤ B) :
    RB B (entryR c j prev g b).1 ∧ RB B (entryR c j prev g b).2.1 ∧ RB B (entryR c j prev g b).2.2 ∧ j.size ≤ B ∧
      ((runR c (j + 1) (entryR c j prev g b).2.1 gs bs).2.1 + (runR c (j + 1) (entryR c j prev g b).2.1 gs bs).2.2.1 + (runR c (j + 1) (entryR c j prev g b).2.1 gs bs).2.2.2.1 + (runR c (j + 1) (entryR c j prev g b).2.1 gs bs).2.2.2.2.1 + 2).size ≤ B ∧
      (runR c (j + 1) (entryR c j prev g b).2.1 gs bs).2.2.2.2.2.size ≤ B ∧ (j + 1 + 6 * gs.length + 6).size ≤ B ∧
      (∀ g' ∈ gs, ∀ b' ∈ bs, (g'.1 + b'.1).size ≤ B) := by
  have hgb' : ∀ g' ∈ gs, ∀ b' ∈ bs, (g'.1 + b'.1).size ≤ B :=
    fun g' hg b' hb => hgb g' (by simp [hg]) b' (by simp [hb])
  obtain ⟨h1, h2, h3⟩ := entryR_RB hB c j prev g b ha hl hp (hgb g (by simp) b (by simp))
  obtain ⟨k1, k2, k3, k4, k5⟩ := runR_bounds hB c ha hl gs bs hgb' (j + 1) _ h2
  simp only [Ty.den] at k1 k2 k3 k4 k5
  exact ⟨h1, h2, h3, (size_mono (by omega)).trans hj, (size_mono (by omega)).trans hj, k5,
    (size_mono (by omega)).trans hj, hgb'⟩

/-- **Cost of the scan**: `O(n (B + 1)²)` for `n` pairs of `B`-bit data. -/
theorem runCost_le {B : ℕ} (hB : 1 ≤ B) (c : Ty.den (TC)) (ha : RB B c.2.2.1)
    (hl : RB B c.2.2.2) (hr : c.2.1.size ≤ B) (gs bs : List (ℕ × ℕ))
    (hgb : ∀ g ∈ gs, ∀ b ∈ bs, (g.1 + b.1).size ≤ B) :
    ∀ (j : ℕ) (prev : ℕ × ℕ), RB B prev → (j + 6 * gs.length + 6).size ≤ B →
      runCost c j prev gs bs ≤ 16000 * (gs.length + 1) * (B + 1) * (B + 1) := by
  induction gs generalizing bs with
  | nil => intro j prev _ _; simp only [runCost, List.length_nil]; nlinarith
  | cons g gs ih =>
    cases bs with
    | nil =>
      intro j prev _ _
      have h1 : 1 ≤ (gs.length + 1 + 1) * (B + 1) * (B + 1) :=
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
      simp only [runCost, List.length_cons]; nlinarith
    | cons b bs =>
      intro j prev hp hj
      simp only [List.length_cons] at hj ⊢
      obtain ⟨h1, h2, h3, hj0, hctr, hmad, hj1, hgb'⟩ :=
        step_sizes hB c ha hl j prev g b gs bs hp hgb hj
      have hrec := ih bs hgb' (j + 1) _ h2 hj1
      have hent := entryCost_le hB c j prev g b ha hl hp (hgb g (by simp) b (by simp)) hj0 hr
      simp only [runCost, accF_cost, ctrF_cost, mdF_cost, ctrArg, mdArg]
      have := hp.2; have := h1.2; have := h2.2; have := h3.2
      simp only [Ty.den] at *
      nlinarith

/-- **Depth of the scan**: linear in the number of pairs plus the bit length. -/
theorem runDepth_le {B : ℕ} (hB : 1 ≤ B) (c : Ty.den (TC)) (ha : RB B c.2.2.1)
    (hl : RB B c.2.2.2) (hr : c.2.1.size ≤ B) (gs bs : List (ℕ × ℕ))
    (hgb : ∀ g ∈ gs, ∀ b ∈ bs, (g.1 + b.1).size ≤ B) :
    ∀ (j : ℕ) (prev : ℕ × ℕ), RB B prev → (j + 6 * gs.length + 6).size ≤ B →
      runDepth c j prev gs bs ≤ gs.length + 20 * B + 41 := by
  induction gs generalizing bs with
  | nil => intro j prev _ _; simp only [runDepth]; omega
  | cons g gs ih =>
    cases bs with
    | nil => intro j prev _ _; simp only [runDepth]; omega
    | cons b bs =>
      intro j prev hp hj
      simp only [List.length_cons] at hj ⊢
      obtain ⟨h1, h2, h3, hj0, hctr, hmad, hj1, hgb'⟩ :=
        step_sizes hB c ha hl j prev g b gs bs hp hgb hj
      have hrec := ih bs hgb' (j + 1) _ h2 hj1
      have hent := entryDepth_le hB c j prev g b ha hl hp (hgb g (by simp) b (by simp)) hj0 hr
      simp only [runDepth, accF_depth, ctrF_depth, mdF_depth, ctrArg, mdArg]
      have := hp.2; have := h1.2; have := h2.2; have := h3.2
      simp only [Ty.den] at *
      omega


end QecReliability.FL.Lib.LinearRepairFL
