import WholeWrapperController
import FL.Lib.LinearRepair

/-!
# Trans.Control.Types: FL encodings of the macro controller's data

Every controller object is represented by naturals, Booleans, lists and products (`Ty`):

* `PC` ↦ `nat` (`pcCode`, constructor index `0 … 19`);
* `Opcode` ↦ `nat × bool × nat` (`encOp`: `(tag, flag, argument)`);
* `ReturnTag` ↦ `bool` (`.prefix ↦ true`);
* `RequestKey` ↦ `bool × bool × nat × nat × nat × list bool`
  (`encKey`: `(isCell, good, coefficient, repetition, scale, pre)`; base keys have
  `scale = 0`, `pre = []`);
* `PrefixTransitions.Control` ↦ `nat × nat × list bool × nat` (`encCtl`: tag `0` enter,
  `1` await, `2` ret; `(tag, depth/count, pre, cap)`);
* `PrefixTransitions.Frame` ↦ `bool × nat × list bool × nat` (`encFrame`: `left ↦ false`);
* `PrefixTransitions.Config` ↦ `TCtl × list TFrame` (`encPre`);
* `Ratio` ↦ `nat × nat` (`toR`, as in `FL/Lib/LinearRepair.lean`); `Entry` ↦ `nat × nat`;
* `Config` (46 fields) ↦ a product of seven groups (`encCfg`), see `TCfg`.

All encodings are injective (`*_injective`, in particular `encCfg_injective`).
-/

set_option autoImplicit false

namespace QecReliability.Trans.Control
open QecReliability.FL QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.RationalOutput

/-! ## Types -/

abbrev TR : Ty := .prod .nat .nat
abbrev TEnt : Ty := .prod .nat .nat
abbrev TOp : Ty := .prod .nat (.prod .bool .nat)
abbrev TKey : Ty := .prod .bool (.prod .bool (.prod .nat (.prod .nat (.prod .nat (.list .bool)))))
abbrev TCtl : Ty := .prod .nat (.prod .nat (.prod (.list .bool) .nat))
abbrev TFrame : Ty := .prod .bool (.prod .nat (.prod (.list .bool) .nat))
abbrev TPre : Ty := .prod TCtl (.list TFrame)

/-- Group 0 (control): `pc, code, good, coefficient, repetition, scale, nonempty, returnTag`. -/
abbrev TG0 : Ty := .prod .nat (.prod (.list TOp) (.prod .bool (.prod .nat (.prod .nat
  (.prod .nat (.prod .bool .bool))))))
/-- Group 1 (calls): `request, query, reply, prefixState, cellCalls, trialCalls,
coefficientCalls`. -/
abbrev TG1 : Ty := .prod TKey (.prod (.list .bool) (.prod .bool (.prod TPre (.prod .nat
  (.prod .nat .nat)))))
/-- Group 2 (trials): `cellsRev, pairSrc, pairDst, trialsRev, selected, selectIndex,
scaleFactor`. -/
abbrev TG2 : Ty := .prod (.list TEnt) (.prod (.list TEnt) (.prod (.list TEnt) (.prod (.list TEnt)
  (.prod .nat (.prod .nat .nat)))))
/-- Group 3 (median sort): `sortTodo, sorted, insertValue, insertLeftRev, insertRight,
insertResult, lookupRemaining`. -/
abbrev TG3 : Ty := .prod (.list .nat) (.prod (.list .nat) (.prod .nat (.prod (.list .nat)
  (.prod (.list .nat) (.prod (.list .nat) .nat)))))
/-- Group 4 (tables): `goodRev, badRev, goodTable, badTable, repairGood, repairBad`. -/
abbrev TG4 : Ty := .prod (.list TEnt) (.prod (.list TEnt) (.prod (.list TEnt) (.prod (.list TEnt)
  (.prod (.list TEnt) (.list TEnt)))))
/-- Group 5 (repair): `endpoint0, endpoint1, previous, repairIndex, outputRev, output`. -/
abbrev TG5 : Ty := .prod TR (.prod TR (.prod TR (.prod .nat (.prod (.list TR) (.list TR)))))
/-- Group 6 (counters): `pairVisits, ratioBuilds, orderComparisons, endpointTests,
maxAccumulatorDen`. -/
abbrev TG6 : Ty := .prod .nat (.prod .nat (.prod .nat (.prod .nat .nat)))

abbrev TCfg : Ty := .prod TG0 (.prod TG1 (.prod TG2 (.prod TG3 (.prod TG4 (.prod TG5 TG6)))))

/-! ## Encodings -/

def pcCode : PC → ℕ
  | .fetch => 0 | .prefix => 1 | .compile => 2 | .invoke => 3 | .resume => 4
  | .reverseCells => 5 | .selectScan => 6 | .trialCommit => 7
  | .sortNext => 8 | .insertScan => 9 | .insertRestore => 10 | .medianLookup => 11
  | .reverseGood => 12 | .reverseBad => 13 | .endpointZero => 14 | .endpointOne => 15
  | .repair => 16 | .reverseOutput => 17 | .done => 18 | .fault => 19

theorem pcCode_injective : Function.Injective pcCode := by
  intro a b h; cases a <;> cases b <;> simp_all [pcCode]

theorem pcCode_lt (pc : PC) : pcCode pc < 20 := by cases pc <;> simp [pcCode]

def encOp : Opcode → ℕ × Bool × ℕ
  | .beginCoefficient good j => (0, good, j)
  | .base rep => (1, false, rep)
  | .cell scale => (2, false, scale)
  | .select => (3, false, 0)
  | .median => (4, false, 0)
  | .store => (5, false, 0)
  | .finish => (6, false, 0)

theorem encOp_injective : Function.Injective encOp := by
  intro a b h; cases a <;> cases b <;> simp_all [encOp]

def encTag : ReturnTag → Bool
  | .base => false
  | .prefix => true

theorem encTag_injective : Function.Injective encTag := by
  intro a b h; cases a <;> cases b <;> simp_all [encTag]

def encKey : RequestKey → Bool × Bool × ℕ × ℕ × ℕ × List Bool
  | .base good j rep => (false, good, j, rep, 0, [])
  | .cell good j rep scale pre => (true, good, j, rep, scale, pre)

theorem encKey_injective : Function.Injective encKey := by
  intro a b h; cases a <;> cases b <;> simp_all [encKey]

def encCtl : PrefixTransitions.Control → ℕ × ℕ × List Bool × ℕ
  | .enter d pre cap => (0, d, pre, cap)
  | .await d pre cap => (1, d, pre, cap)
  | .ret count => (2, count, [], 0)

theorem encCtl_injective : Function.Injective encCtl := by
  intro a b h; cases a <;> cases b <;> simp_all [encCtl]

def encFrame : PrefixTransitions.Frame → Bool × ℕ × List Bool × ℕ
  | .left d pre cap => (false, d, pre, cap)
  | .right lc => (true, lc, [], 0)

theorem encFrame_injective : Function.Injective encFrame := by
  intro a b h; cases a <;> cases b <;> simp_all [encFrame]

def encPre (c : PrefixTransitions.Config) :
    (ℕ × ℕ × List Bool × ℕ) × List (Bool × ℕ × List Bool × ℕ) :=
  (encCtl c.control, c.stack.map encFrame)

theorem encPre_injective : Function.Injective encPre := by
  rintro ⟨c, s⟩ ⟨c', s'⟩ h
  simp only [encPre, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [encCtl_injective h1, (List.map_injective_iff.mpr encFrame_injective) h2]

/-- Ratios as `(num, den)` (the representation of `FL/Lib/LinearRepair.lean`). -/
abbrev toR (x : Ratio) : ℕ × ℕ := FL.Lib.LinearRepairFL.toR x

theorem toR_eq (x : Ratio) : toR x = (x.num, x.den) := rfl

theorem toR_injective : Function.Injective toR := by
  rintro ⟨a, b, _, _⟩ ⟨c, d, _, _⟩ h
  simp only [toR_eq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- The whole controller configuration. -/
def encCfg (s : Config) : TCfg.den :=
  ((pcCode s.pc, s.code.map encOp, s.good, s.coefficient, s.repetition, s.scale, s.nonempty,
      encTag s.returnTag),
   (encKey s.request, s.query, s.reply, encPre s.prefixState, s.cellCalls, s.trialCalls,
      s.coefficientCalls),
   (s.cellsRev, s.pairSrc, s.pairDst, s.trialsRev, s.selected, s.selectIndex, s.scaleFactor),
   (s.sortTodo, s.sorted, s.insertValue, s.insertLeftRev, s.insertRight, s.insertResult,
      s.lookupRemaining),
   (s.goodRev, s.badRev, s.goodTable, s.badTable, s.repairGood, s.repairBad),
   (toR s.endpoint0, toR s.endpoint1, toR s.previous, s.repairIndex, s.outputRev.map toR,
      s.output.map toR),
   (s.pairVisits, s.ratioBuilds, s.orderComparisons, s.endpointTests, s.maxAccumulatorDen))

theorem encCfg_injective : Function.Injective encCfg := by
  intro a b h
  have hops := List.map_injective_iff.mpr encOp_injective
  have hrs := List.map_injective_iff.mpr toR_injective
  simp only [encCfg, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15⟩,
    ⟨h16, h17, h18, h19, h20, h21, h22⟩, ⟨h23, h24, h25, h26, h27, h28, h29⟩,
    ⟨h30, h31, h32, h33, h34, h35⟩, ⟨h36, h37, h38, h39, h40, h41⟩,
    ⟨h42, h43, h44, h45, h46⟩⟩ := h
  cases a; cases b
  simp only at *
  rw [pcCode_injective h1, hops h2, encTag_injective h8, encKey_injective h9,
    encPre_injective h12, toR_injective h36, toR_injective h37, toR_injective h38, hrs h40,
    hrs h41]
  subst_vars
  rfl

end QecReliability.Trans.Control
