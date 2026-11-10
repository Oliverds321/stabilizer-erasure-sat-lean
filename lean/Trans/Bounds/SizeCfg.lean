import Trans.Control.Types
import WholeWrapperRepresentation

/-!
# Trans.Bounds.SizeCfg: encoded size of a controller configuration

**`sz_encCfg_le`**: `(Ty.enc TCfg (encCfg s)).size ≤ 10 * (representedBits s).length + 400` for
every configuration `s`. The macro layer bounds `(representedBits s).length` at every reachable
state (`Assembly.instReachable_bounds`), so this is the configuration half of the size bridge.

Accounting: every natural `x` of the configuration costs `4·x.size + 1` tree nodes in the FL
encoding and `2·x.size + 1` bits in `representedBits` (a `natHeader`); list/pair constructors
are charged to the headers of their entries; the query is stored as raw bits and the prefix
state as `PrefixTransitions.configBits`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Bounds
open QecReliability.FL
open QecReliability.Trans.Control
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate

/-! ## `configFields` with the private helpers restated -/

def bw (b : Bool) : ℕ := if b then 1 else 0
def opW : Opcode → List ℕ
  | .beginCoefficient side j => [0,bw side,j]
  | .base rep => [1,rep,0]
  | .cell scale => [2,scale,0]
  | .select => [3,0,0] | .median => [4,0,0] | .store => [5,0,0] | .finish => [6,0,0]
def reqW : RequestKey → List ℕ
  | .base side j rep => [0,bw side,j,rep,0]
  | .cell side j rep scale _ => [1,bw side,j,rep,scale]
def reqP : RequestKey → List Bool
  | .base _ _ _ => []
  | .cell _ _ _ _ pre => pre
def entW (xs : List Entry) : List ℕ := xs.flatMap (fun x => [x.1,x.2])
def ratW (xs : List RationalOutput.Ratio) : List ℕ := xs.flatMap (fun x => [x.num,x.den])

theorem configFields_eq (s : Config) : configFields s =
  [[pcCode s.pc,bw s.good,s.coefficient,s.repetition,s.scale,bw s.nonempty,
    (match s.returnTag with | .base => 0 | .prefix => 1),bw s.reply,
    s.cellCalls,s.trialCalls,s.coefficientCalls,s.selected,s.selectIndex,s.scaleFactor,
    s.insertValue,s.lookupRemaining,s.repairIndex,s.pairVisits,s.ratioBuilds,
    s.orderComparisons,s.endpointTests,s.maxAccumulatorDen],
   s.code.flatMap opW,reqW s.request,
   (reqP s.request).map bw,
   entW s.cellsRev,entW s.pairSrc,entW s.pairDst,
   entW s.trialsRev,s.sortTodo,s.sorted,s.insertLeftRev,s.insertRight,s.insertResult,
   entW s.goodRev,entW s.badRev,entW s.goodTable,entW s.badTable,
   entW s.repairGood,entW s.repairBad,
   ratW [s.endpoint0,s.endpoint1,s.previous],ratW s.outputRev,ratW s.output] := rfl

/-! ## Header weight -/

/-- Total header length of a list of naturals. -/
def hw (xs : List ℕ) : ℕ := (xs.flatMap QueryCodec.natHeader).length

@[simp] theorem hw_nil : hw [] = 0 := rfl
@[simp] theorem hw_cons (x : ℕ) (xs : List ℕ) : hw (x :: xs) = 2 * x.size + 1 + hw xs := by
  simp only [hw, List.flatMap_cons, List.length_append, QueryCodec.natHeader_length]
theorem hw_append (xs ys : List ℕ) : hw (xs ++ ys) = hw xs + hw ys := by
  simp only [hw, List.flatMap_append, List.length_append]

theorem length_le_hw (xs : List ℕ) : xs.length ≤ hw xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [hw_cons, List.length_cons]; omega

theorem hw_le_fieldBits (xs : List ℕ) : hw xs ≤ (fieldBits xs).length := by
  simp only [fieldBits, List.length_append, hw]; omega

theorem sum_hw_le_fieldsBits (fs : List (List ℕ)) : (fs.map hw).sum ≤ (fieldsBits fs).length := by
  have h : ∀ gs : List (List ℕ), (gs.map hw).sum ≤ (gs.flatMap fieldBits).length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have := hw_le_fieldBits g
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]; omega
  have := h fs
  simp only [fieldsBits, List.length_append]; omega

/-! ## Tuple shapes (generic types, so that `Ty.sz_prod` stops at the components) -/

theorem shape2 {a b : Ty} (x1 : a.den) (x2 : b.den) :
    (Ty.enc (.prod a b) (x1, x2)).size = (a.enc x1).size + (b.enc x2).size + 1 := by
  simp only [Ty.sz_prod]; omega
theorem shape3 {a b c : Ty} (x1 : a.den) (x2 : b.den) (x3 : c.den) :
    (Ty.enc (.prod a (.prod b c)) (x1, x2, x3)).size =
      (a.enc x1).size + (b.enc x2).size + (c.enc x3).size + 2 := by
  simp only [Ty.sz_prod]; omega
theorem shape4 {a b c d : Ty} (x1 : a.den) (x2 : b.den) (x3 : c.den) (x4 : d.den) :
    (Ty.enc (.prod a (.prod b (.prod c d))) (x1, x2, x3, x4)).size =
      (a.enc x1).size + (b.enc x2).size + (c.enc x3).size + (d.enc x4).size + 3 := by
  simp only [Ty.sz_prod]; omega
theorem shape5 {a b c d e : Ty} (x1 : a.den) (x2 : b.den) (x3 : c.den) (x4 : d.den)
    (x5 : e.den) :
    (Ty.enc (.prod a (.prod b (.prod c (.prod d e)))) (x1, x2, x3, x4, x5)).size =
      (a.enc x1).size + (b.enc x2).size + (c.enc x3).size + (d.enc x4).size +
        (e.enc x5).size + 4 := by
  simp only [Ty.sz_prod]; omega
theorem shape6 {a b c d e f : Ty} (x1 : a.den) (x2 : b.den) (x3 : c.den) (x4 : d.den)
    (x5 : e.den) (x6 : f.den) :
    (Ty.enc (.prod a (.prod b (.prod c (.prod d (.prod e f))))) (x1, x2, x3, x4, x5, x6)).size =
      (a.enc x1).size + (b.enc x2).size + (c.enc x3).size + (d.enc x4).size +
        (e.enc x5).size + (f.enc x6).size + 5 := by
  simp only [Ty.sz_prod]; omega
theorem shape7 {a b c d e f g : Ty} (x1 : a.den) (x2 : b.den) (x3 : c.den) (x4 : d.den)
    (x5 : e.den) (x6 : f.den) (x7 : g.den) :
    (Ty.enc (.prod a (.prod b (.prod c (.prod d (.prod e (.prod f g))))))
      (x1, x2, x3, x4, x5, x6, x7)).size =
      (a.enc x1).size + (b.enc x2).size + (c.enc x3).size + (d.enc x4).size +
        (e.enc x5).size + (f.enc x6).size + (g.enc x7).size + 6 := by
  simp only [Ty.sz_prod]; omega
theorem shape8 {a b c d e f g h : Ty} (x1 : a.den) (x2 : b.den) (x3 : c.den) (x4 : d.den)
    (x5 : e.den) (x6 : f.den) (x7 : g.den) (x8 : h.den) :
    (Ty.enc (.prod a (.prod b (.prod c (.prod d (.prod e (.prod f (.prod g h)))))))
      (x1, x2, x3, x4, x5, x6, x7, x8)).size =
      (a.enc x1).size + (b.enc x2).size + (c.enc x3).size + (d.enc x4).size +
        (e.enc x5).size + (f.enc x6).size + (g.enc x7).size + (h.enc x8).size + 7 := by
  simp only [Ty.sz_prod]; omega

/-! ## Per-type accounting -/

theorem nat_le_hdr (n : ℕ) : (Ty.enc .nat n).size + 1 ≤ 2 * (2 * n.size + 1) := by
  have := Ty.sz_nat_le n; omega

theorem sz_lt_pow (t k : ℕ) (ht : t < 2 ^ k) : (Ty.enc .nat t).size ≤ 4 * k + 1 := by
  have h1 := Ty.sz_nat_le t
  have h2 : t.size ≤ k := Nat.size_le.mpr ht
  omega

theorem sz_small (t : ℕ) (ht : t < 32) : (Ty.enc .nat t).size ≤ 21 :=
  sz_lt_pow t 5 (by omega)

theorem sz_natList (xs : List ℕ) : (Ty.enc (.list .nat) xs).size ≤ 2 * hw xs + 1 := by
  induction xs with
  | nil => exact Nat.le_of_eq rfl
  | cons x xs ih =>
    have := Ty.sz_nat_le x
    simp only [Ty.enc_list_cons_nat, Val.size, hw_cons]
    simp only [Ty.enc_nat] at this
    omega

theorem sz_entList (xs : List (ℕ × ℕ)) :
    (Ty.enc (.list (.prod .nat .nat)) xs).size ≤ 2 * hw (entW xs) + 1 := by
  induction xs with
  | nil => simp [entW]
  | cons x xs ih =>
    have h1 := Ty.sz_nat_le x.1
    have h2 := Ty.sz_nat_le x.2
    have e : entW (x :: xs) = [x.1, x.2] ++ entW xs := rfl
    simp only [Ty.enc_list_cons_nat2, Val.size, e, hw_append, hw_cons, hw_nil]
    simp only [Ty.enc_nat] at h1 h2
    omega

theorem sz_ratList (xs : List RationalOutput.Ratio) :
    (Ty.enc (.list (.prod .nat .nat)) (xs.map toR)).size ≤ 2 * hw (ratW xs) + 1 := by
  induction xs with
  | nil => simp [ratW]
  | cons x xs ih =>
    have h1 := Ty.sz_nat_le x.num
    have h2 := Ty.sz_nat_le x.den
    have e : ratW (x :: xs) = [x.num, x.den] ++ ratW xs := rfl
    have e2 : toR x = (x.num, x.den) := rfl
    simp only [List.map_cons, Ty.enc_list_cons_nat2, Val.size, e, e2, hw_append, hw_cons,
      hw_nil]
    simp only [Ty.enc_nat] at h1 h2
    omega

theorem sz_entList' (xs : List (ℕ × ℕ)) :
    (Ty.enc (.list TEnt) xs).size ≤ 2 * hw (entW xs) + 1 := sz_entList xs

theorem sz_ratList' (xs : List RationalOutput.Ratio) :
    (Ty.enc (.list TR) (xs.map toR)).size ≤ 2 * hw (ratW xs) + 1 := sz_ratList xs

theorem sz_boolList (bs : List Bool) : (Ty.enc (.list .bool) bs).size ≤ 4 * bs.length + 1 := by
  have := Ty.sz_list_le .bool bs 3 (fun b _ => Ty.sz_bool_le b)
  omega

theorem sz_op (op : Opcode) : (Ty.enc TOp (encOp op)).size + 1 ≤ 10 * hw (opW op) := by
  have z0 := sz_lt_pow 0 0 (by omega)
  have z1 := sz_lt_pow 1 1 (by omega)
  have z2 := sz_lt_pow 2 2 (by omega)
  have z3 := sz_lt_pow 3 2 (by omega)
  have z4 := sz_lt_pow 4 3 (by omega)
  have z5 := sz_lt_pow 5 3 (by omega)
  have z6 := sz_lt_pow 6 3 (by omega)
  have hb := Ty.sz_bool_le false
  cases op with
  | beginCoefficient side j =>
    have h1 := Ty.sz_nat_le j; have h2 := Ty.sz_bool_le side
    simp only [encOp, opW, hw_cons, hw_nil]; rw [shape3]; omega
  | base rep =>
    have h1 := Ty.sz_nat_le rep
    simp only [encOp, opW, hw_cons, hw_nil]; rw [shape3]; omega
  | cell scale =>
    have h1 := Ty.sz_nat_le scale
    simp only [encOp, opW, hw_cons, hw_nil]; rw [shape3]; omega
  | select => simp only [encOp, opW, hw_cons, hw_nil]; rw [shape3]; omega
  | median => simp only [encOp, opW, hw_cons, hw_nil]; rw [shape3]; omega
  | store => simp only [encOp, opW, hw_cons, hw_nil]; rw [shape3]; omega
  | finish => simp only [encOp, opW, hw_cons, hw_nil]; rw [shape3]; omega

theorem sz_code (ops : List Opcode) :
    (Ty.enc (.list TOp) (ops.map encOp)).size ≤ 10 * hw (ops.flatMap opW) + 1 := by
  induction ops with
  | nil => exact Nat.le_of_eq rfl
  | cons op ops ih =>
    have := sz_op op
    rw [List.map_cons, Ty.sz_list_cons, List.flatMap_cons, hw_append]
    omega

theorem sz_key (k : RequestKey) :
    (Ty.enc TKey (encKey k)).size ≤ 8 * (hw (reqW k) + hw ((reqP k).map bw)) + 20 := by
  cases k with
  | base side j rep =>
    have h1 := Ty.sz_nat_le j; have h2 := Ty.sz_nat_le rep; have h3 := Ty.sz_bool_le side
    have h4 := Ty.sz_bool_le false; have h5 := sz_small 0 (by omega)
    simp only [encKey, reqW, reqP, hw_cons, hw_nil, List.map_nil]; rw [shape6]
    have h6 : (Ty.enc (.list .bool) ([] : List Bool)).size = 1 := rfl
    omega
  | cell side j rep scale pre =>
    have h1 := Ty.sz_nat_le j; have h2 := Ty.sz_nat_le rep; have h3 := Ty.sz_bool_le side
    have h4 := Ty.sz_bool_le true; have h5 := Ty.sz_nat_le scale
    have h6 := sz_boolList pre
    have h7 := length_le_hw (pre.map bw)
    simp only [List.length_map] at h7
    simp only [encKey, reqW, reqP, hw_cons, hw_nil]; rw [shape6]
    omega

open PrefixTransitions in
theorem sz_ctl (c : PrefixTransitions.Control) :
    (Ty.enc TCtl (encCtl c)).size ≤ 8 * (controlBits c).length + 30 := by
  cases c with
  | enter d pre cap =>
    have h1 := Ty.sz_nat_le d; have h2 := Ty.sz_nat_le cap; have h3 := sz_boolList pre
    have h4 := sz_small 0 (by omega)
    simp only [encCtl, controlBits, List.length_append, QueryCodec.natHeader_length,
      List.length_cons, List.length_nil]
    rw [shape4]
    omega
  | await d pre cap =>
    have h1 := Ty.sz_nat_le d; have h2 := Ty.sz_nat_le cap; have h3 := sz_boolList pre
    have h4 := sz_small 1 (by omega)
    simp only [encCtl, controlBits, List.length_append, QueryCodec.natHeader_length,
      List.length_cons, List.length_nil]
    rw [shape4]
    omega
  | ret count =>
    have h1 := Ty.sz_nat_le count; have h4 := sz_small 2 (by omega)
    have h5 := sz_small 0 (by omega)
    have h6 : (Ty.enc (.list .bool) ([] : List Bool)).size = 1 := rfl
    simp only [encCtl, controlBits, List.length_append, QueryCodec.natHeader_length,
      List.length_cons, List.length_nil]
    rw [shape4]
    omega

open PrefixTransitions in
theorem sz_frame (f : PrefixTransitions.Frame) :
    (Ty.enc TFrame (encFrame f)).size + 1 ≤ 9 * (frameBits f).length := by
  cases f with
  | left d pre cap =>
    have h1 := Ty.sz_nat_le d; have h2 := Ty.sz_nat_le cap; have h3 := sz_boolList pre
    have h4 := Ty.sz_bool_le false
    simp only [encFrame, frameBits, List.length_append, QueryCodec.natHeader_length,
      List.length_cons, List.length_nil]
    rw [shape4]
    omega
  | right lc =>
    have h1 := Ty.sz_nat_le lc; have h4 := Ty.sz_bool_le true
    have h5 := sz_lt_pow 0 0 (by omega)
    have h6 : (Ty.enc (.list .bool) ([] : List Bool)).size = 1 := rfl
    simp only [encFrame, frameBits, List.length_append, QueryCodec.natHeader_length,
      List.length_cons, List.length_nil]
    rw [shape4]
    omega

open PrefixTransitions in
theorem sz_stack (st : List PrefixTransitions.Frame) :
    (Ty.enc (.list TFrame) (st.map encFrame)).size ≤ 9 * (st.flatMap frameBits).length + 1 := by
  induction st with
  | nil => exact Nat.le_of_eq rfl
  | cons f st ih =>
    have := sz_frame f
    rw [List.map_cons, Ty.sz_list_cons, List.flatMap_cons, List.length_append]
    omega

open PrefixTransitions in
theorem sz_pre (ps : PrefixTransitions.Config) :
    (Ty.enc TPre (encPre ps)).size ≤ 9 * (configBits ps).length + 40 := by
  have h1 := sz_ctl ps.control
  have h2 := sz_stack ps.stack
  simp only [encPre, configBits, List.length_append, QueryCodec.natHeader_length]
  rw [shape2]
  omega

/-! ## Groups -/

section Groups
variable (s : Config)

theorem sz_g0 : (Ty.enc TG0 (pcCode s.pc, s.code.map encOp, s.good, s.coefficient, s.repetition,
      s.scale, s.nonempty, encTag s.returnTag)).size ≤
    10 * hw (s.code.flatMap opW) + 4 * s.coefficient.size + 4 * s.repetition.size +
      4 * s.scale.size + 50 := by
  have h0 := sz_small (pcCode s.pc) (by have := pcCode_lt s.pc; omega)
  have h1 := sz_code s.code
  have h2 := Ty.sz_bool_le s.good
  have h3 := Ty.sz_nat_le s.coefficient
  have h4 := Ty.sz_nat_le s.repetition
  have h5 := Ty.sz_nat_le s.scale
  have h6 := Ty.sz_bool_le s.nonempty
  have h7 := Ty.sz_bool_le (encTag s.returnTag)
  rw [shape8]
  omega

theorem sz_g1 : (Ty.enc TG1 (encKey s.request, s.query, s.reply, encPre s.prefixState,
      s.cellCalls, s.trialCalls, s.coefficientCalls)).size ≤
    8 * (hw (reqW s.request) + hw ((reqP s.request).map bw)) + 4 * s.query.length +
      9 * (PrefixTransitions.configBits s.prefixState).length + 4 * s.cellCalls.size + 4 * s.trialCalls.size +
      4 * s.coefficientCalls.size + 80 := by
  have h0 := sz_key s.request
  have h1 := sz_boolList s.query
  have h2 := Ty.sz_bool_le s.reply
  have h3 := sz_pre s.prefixState
  have h4 := Ty.sz_nat_le s.cellCalls
  have h5 := Ty.sz_nat_le s.trialCalls
  have h6 := Ty.sz_nat_le s.coefficientCalls
  rw [shape7]
  omega

theorem sz_g2 : (Ty.enc TG2 (s.cellsRev, s.pairSrc, s.pairDst, s.trialsRev, s.selected,
      s.selectIndex, s.scaleFactor)).size ≤
    2 * (hw (entW s.cellsRev) + hw (entW s.pairSrc) + hw (entW s.pairDst) +
      hw (entW s.trialsRev)) + 4 * s.selected.size + 4 * s.selectIndex.size +
      4 * s.scaleFactor.size + 20 := by
  have h0 := sz_entList' s.cellsRev
  have h1 := sz_entList' s.pairSrc
  have h2 := sz_entList' s.pairDst
  have h3 := sz_entList' s.trialsRev
  have h4 := Ty.sz_nat_le s.selected
  have h5 := Ty.sz_nat_le s.selectIndex
  have h6 := Ty.sz_nat_le s.scaleFactor
  rw [shape7]
  omega

theorem sz_g3 : (Ty.enc TG3 (s.sortTodo, s.sorted, s.insertValue, s.insertLeftRev,
      s.insertRight, s.insertResult, s.lookupRemaining)).size ≤
    2 * (hw s.sortTodo + hw s.sorted + hw s.insertLeftRev + hw s.insertRight +
      hw s.insertResult) + 4 * s.insertValue.size + 4 * s.lookupRemaining.size + 20 := by
  have h0 := sz_natList s.sortTodo
  have h1 := sz_natList s.sorted
  have h2 := Ty.sz_nat_le s.insertValue
  have h3 := sz_natList s.insertLeftRev
  have h4 := sz_natList s.insertRight
  have h5 := sz_natList s.insertResult
  have h6 := Ty.sz_nat_le s.lookupRemaining
  rw [shape7]
  omega

theorem sz_g4 : (Ty.enc TG4 (s.goodRev, s.badRev, s.goodTable, s.badTable, s.repairGood,
      s.repairBad)).size ≤
    2 * (hw (entW s.goodRev) + hw (entW s.badRev) + hw (entW s.goodTable) +
      hw (entW s.badTable) + hw (entW s.repairGood) + hw (entW s.repairBad)) + 20 := by
  have h0 := sz_entList' s.goodRev
  have h1 := sz_entList' s.badRev
  have h2 := sz_entList' s.goodTable
  have h3 := sz_entList' s.badTable
  have h4 := sz_entList' s.repairGood
  have h5 := sz_entList' s.repairBad
  rw [shape6]
  omega

theorem sz_g5 : (Ty.enc TG5 (toR s.endpoint0, toR s.endpoint1, toR s.previous, s.repairIndex,
      s.outputRev.map toR, s.output.map toR)).size ≤
    2 * (hw (ratW [s.endpoint0, s.endpoint1, s.previous]) + hw (ratW s.outputRev) +
      hw (ratW s.output)) + 4 * s.repairIndex.size + 20 := by
  have h0 := sz_ratList' [s.endpoint0, s.endpoint1, s.previous]
  have h1 := sz_ratList' s.outputRev
  have h2 := sz_ratList' s.output
  have h3 := Ty.sz_nat_le s.repairIndex
  have e : (Ty.enc (.list TR) ([s.endpoint0, s.endpoint1, s.previous].map toR)).size
      = (Ty.enc TR (toR s.endpoint0)).size + (Ty.enc TR (toR s.endpoint1)).size +
        (Ty.enc TR (toR s.previous)).size + 4 := by
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, Ty.sz_list_cons,
      Ty.sz_list_cons, Ty.sz_list_cons, Ty.sz_list_nil]; omega
  rw [shape6]
  omega

theorem sz_g6 : (Ty.enc TG6 (s.pairVisits, s.ratioBuilds, s.orderComparisons, s.endpointTests,
      s.maxAccumulatorDen)).size ≤
    4 * s.pairVisits.size + 4 * s.ratioBuilds.size + 4 * s.orderComparisons.size +
      4 * s.endpointTests.size + 4 * s.maxAccumulatorDen.size + 20 := by
  have h0 := Ty.sz_nat_le s.pairVisits
  have h1 := Ty.sz_nat_le s.ratioBuilds
  have h2 := Ty.sz_nat_le s.orderComparisons
  have h3 := Ty.sz_nat_le s.endpointTests
  have h4 := Ty.sz_nat_le s.maxAccumulatorDen
  rw [shape5]
  omega

end Groups

/-! ## The bridge -/

theorem sz_cfg_split (s : Config) : (Ty.enc TCfg (encCfg s)).size =
    (Ty.enc TG0 (pcCode s.pc, s.code.map encOp, s.good, s.coefficient, s.repetition,
      s.scale, s.nonempty, encTag s.returnTag)).size +
    (Ty.enc TG1 (encKey s.request, s.query, s.reply, encPre s.prefixState,
      s.cellCalls, s.trialCalls, s.coefficientCalls)).size +
    (Ty.enc TG2 (s.cellsRev, s.pairSrc, s.pairDst, s.trialsRev, s.selected,
      s.selectIndex, s.scaleFactor)).size +
    (Ty.enc TG3 (s.sortTodo, s.sorted, s.insertValue, s.insertLeftRev,
      s.insertRight, s.insertResult, s.lookupRemaining)).size +
    (Ty.enc TG4 (s.goodRev, s.badRev, s.goodTable, s.badTable, s.repairGood,
      s.repairBad)).size +
    (Ty.enc TG5 (toR s.endpoint0, toR s.endpoint1, toR s.previous, s.repairIndex,
      s.outputRev.map toR, s.output.map toR)).size +
    (Ty.enc TG6 (s.pairVisits, s.ratioBuilds, s.orderComparisons, s.endpointTests,
      s.maxAccumulatorDen)).size + 6 := by
  unfold encCfg
  rw [shape7]

/-- The header weight of all configuration fields is at most the represented length. -/
theorem hw_fields_le (s : Config) :
    (hw [pcCode s.pc,bw s.good,s.coefficient,s.repetition,s.scale,bw s.nonempty,
      (match s.returnTag with | .base => 0 | .prefix => 1),bw s.reply,
      s.cellCalls,s.trialCalls,s.coefficientCalls,s.selected,s.selectIndex,s.scaleFactor,
      s.insertValue,s.lookupRemaining,s.repairIndex,s.pairVisits,s.ratioBuilds,
      s.orderComparisons,s.endpointTests,s.maxAccumulatorDen]) +
    hw (s.code.flatMap opW) + hw (reqW s.request) + hw ((reqP s.request).map bw) +
    hw (entW s.cellsRev) + hw (entW s.pairSrc) + hw (entW s.pairDst) + hw (entW s.trialsRev) +
    hw s.sortTodo + hw s.sorted + hw s.insertLeftRev + hw s.insertRight + hw s.insertResult +
    hw (entW s.goodRev) + hw (entW s.badRev) + hw (entW s.goodTable) + hw (entW s.badTable) +
    hw (entW s.repairGood) + hw (entW s.repairBad) +
    hw (ratW [s.endpoint0, s.endpoint1, s.previous]) + hw (ratW s.outputRev) +
    hw (ratW s.output) ≤ (fieldsBits (configFields s)).length := by
  calc
    _ = ((configFields s).map hw).sum := by
      rw [configFields_eq]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_assoc, Nat.add_zero]
    _ ≤ (fieldsBits (configFields s)).length := sum_hw_le_fieldsBits (configFields s)

/-- **Size bridge, configuration part.** -/
theorem sz_encCfg_le (s : Config) :
    (Ty.enc TCfg (encCfg s)).size ≤ 10 * (representedBits s).length + 400 := by
  have hs := sz_cfg_split s
  have g0 := sz_g0 s
  have g1 := sz_g1 s
  have g2 := sz_g2 s
  have g3 := sz_g3 s
  have g4 := sz_g4 s
  have g5 := sz_g5 s
  have g6 := sz_g6 s
  have hf := hw_fields_le s
  have hr : (representedBits s).length = (fieldsBits (configFields s)).length +
      (2 * s.query.length.size + 1) + s.query.length +
      (PrefixTransitions.configBits s.prefixState).length := by
    simp only [representedBits, List.length_append, QueryCodec.natHeader_length]
  simp only [hw_cons, hw_nil] at hf
  omega

end QecReliability.Trans.Bounds
