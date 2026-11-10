import Assembly.Spec
import Final.RawBits
import Interp.Call
import RegMachine.Main

/-!
# Assembly.Program: the top-level register program

Twenty registers:

| reg | name | role |
|---|---|---|
| 0 | `rIN` | machine input (problem encoding ++ coins); consumed by `rawToVal` |
| 1 | `rST` | encoded controller state `(enc s).bits` (argument of every FL call) |
| 2 | `rTMP` | result of FL calls |
| 3 | `rDN` | result of `isDone` (loop flag) |
| 4 | `rQ` | raw SAT query |
| 5 | `rOUT` | raw output word |
| 6–19 | | interpreter scratch (always empty between calls) |

```
ST := encBits IN                   -- rawToVal
TMP := init(ST); ST := TMP         -- FL
DN := isDone(ST)                   -- FL
while head DN ≠ true:
  TMP := isInvoke(ST)
  if head TMP = true:
    TMP := query(ST); Q := raw(TMP)
    if SAT(Q) then ST := (true, ST) else ST := (false, ST)   -- pair (answer, state)
    Q := []
    TMP := resume(ST); ST := TMP
  else
    TMP := step(ST); ST := TMP
  DN := isDone(ST)
TMP := output(ST); OUT := raw(TMP)
```
-/

set_option autoImplicit false

noncomputable section
namespace QecReliability.Assembly
open RegMachine Interp FL Function

/-! ## Registers -/

def rIN : Fin 20 := 0
def rST : Fin 20 := 1
def rTMP : Fin 20 := 2
def rDN : Fin 20 := 3
def rQ : Fin 20 := 4
def rOUT : Fin 20 := 5

/-- Interpreter placement: argument `rST`, result `res`, scratch `i ↦ i + 4` (`6 … 19`). -/
def place (res : Fin 20) (i : Fin 16) : Fin 20 :=
  if i.val = 0 then rST else if i.val = 1 then res else ⟨i.val + 4, by omega⟩

theorem place_zero (res : Fin 20) : place res 0 = rST := rfl
theorem place_one (res : Fin 20) : place res 1 = res := rfl

theorem place_scratch (res : Fin 20) (i : Fin 16) (hi : 2 ≤ i.val) :
    (place res i).val = i.val + 4 := by
  unfold place
  rw [if_neg (by omega), if_neg (by omega)]

theorem place_injective {res : Fin 20} (hres : 2 ≤ res.val ∧ res.val ≤ 5) :
    Injective (place res) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  unfold place at hv
  simp only [rST] at hv
  split_ifs at hv <;> simp_all <;> omega

/-! ## Register files of the form used throughout -/

/-- A register file whose only non-empty registers are `ST, TMP, DN, Q, OUT`. -/
def regsOf (st tmp dn q out : List Bool) : Regs 20 := fun r =>
  if r = rST then st else if r = rTMP then tmp else if r = rDN then dn else
  if r = rQ then q else if r = rOUT then out else []

section RegsOf
variable (st tmp dn q out : List Bool)

@[simp] theorem regsOf_ST : regsOf st tmp dn q out rST = st := rfl
@[simp] theorem regsOf_TMP : regsOf st tmp dn q out rTMP = tmp := rfl
@[simp] theorem regsOf_DN : regsOf st tmp dn q out rDN = dn := rfl
@[simp] theorem regsOf_Q : regsOf st tmp dn q out rQ = q := rfl
@[simp] theorem regsOf_OUT : regsOf st tmp dn q out rOUT = out := rfl
@[simp] theorem regsOf_IN : regsOf st tmp dn q out rIN = [] := rfl

theorem regsOf_scratch (r : Fin 20) (hr : 6 ≤ r.val) : regsOf st tmp dn q out r = [] := by
  unfold regsOf
  have h1 : r ≠ rST := fun e => by subst e; simp [rST] at hr
  have h2 : r ≠ rTMP := fun e => by subst e; simp [rTMP] at hr
  have h3 : r ≠ rDN := fun e => by subst e; simp [rDN] at hr
  have h4 : r ≠ rQ := fun e => by subst e; simp [rQ] at hr
  have h5 : r ≠ rOUT := fun e => by subst e; simp [rOUT] at hr
  simp [h1, h2, h3, h4, h5]

theorem regsOf_place (res : Fin 20) (i : Fin 16) (hi : 2 ≤ i.val) :
    regsOf st tmp dn q out (place res i) = [] :=
  regsOf_scratch _ _ _ _ _ _ (by rw [place_scratch res i hi]; omega)

theorem update_regsOf_ST (st' : List Bool) :
    update (regsOf st tmp dn q out) rST st' = regsOf st' tmp dn q out := by
  funext r
  by_cases h : r = rST
  · subst h; simp
  · rw [update_of_ne h]; simp [regsOf, h]

theorem update_regsOf_TMP (tmp' : List Bool) :
    update (regsOf st tmp dn q out) rTMP tmp' = regsOf st tmp' dn q out := by
  funext r
  by_cases h : r = rTMP
  · subst h; simp
  · rw [update_of_ne h]; simp [regsOf, h]

theorem update_regsOf_DN (dn' : List Bool) :
    update (regsOf st tmp dn q out) rDN dn' = regsOf st tmp dn' q out := by
  funext r
  by_cases h : r = rDN
  · subst h; simp
  · rw [update_of_ne h]; simp [regsOf, h]

theorem update_regsOf_Q (q' : List Bool) :
    update (regsOf st tmp dn q out) rQ q' = regsOf st tmp dn q' out := by
  funext r
  by_cases h : r = rQ
  · subst h; simp
  · rw [update_of_ne h]; simp [regsOf, h]

theorem update_regsOf_OUT (out' : List Bool) :
    update (regsOf st tmp dn q out) rOUT out' = regsOf st tmp dn q out' := by
  funext r
  by_cases h : r = rOUT
  · subst h; simp
  · rw [update_of_ne h]; simp [regsOf, h]

theorem fits_regsOf {S : ℕ} (h1 : st.length ≤ S) (h2 : tmp.length ≤ S) (h3 : dn.length ≤ S)
    (h4 : q.length ≤ S) (h5 : out.length ≤ S) : Fits S (regsOf st tmp dn q out) := by
  intro r
  unfold regsOf
  split_ifs <;> simp_all

end RegsOf

/-- After `rawToVal rST rIN` on the input file. -/
theorem rawToVal_regs (input : List Bool) :
    update (update (inputRegs (R := 19) input) rST (inputRegs (R := 19) input rST ++ encBits input))
      rIN [] = regsOf (encBits input) [] [] [] [] := by
  funext r
  by_cases h0 : r = rIN
  · subst h0; simp [regsOf, rIN, rST, rTMP, rDN, rQ, rOUT]
  · rw [update_of_ne h0]
    by_cases h1 : r = rST
    · subst h1; simp [inputRegs, rST, regsOf]
    · rw [update_of_ne h1]
      have h0' : r ≠ 0 := h0
      simp [inputRegs, h0', regsOf, h1]

/-! ## Statements -/

/-- An FL call of function `f`: argument `rST`, result `res`. -/
def flc (P : Program) (f : ℕ) (res : Fin 20) : Stmt (OInstr 20) :=
  toOracle (flCall P f (place res))

/-- `ST := TMP; TMP := []`. -/
def moveST : Stmt (OInstr 20) :=
  toOracle (.seq (.prim (.clear rST)) (.seq (.prim (.append rST rTMP)) (.prim (.clear rTMP))))

/-- Prepend one bit to `ST`. -/
def pf (b : Bool) : Stmt (OInstr 20) := .prim (.basic (.pushFront rST b))

/-- `ST := (Val.cons (Enc.bool true) st).bits`. -/
def pairT : Stmt (OInstr 20) := .seq (pf false) (.seq (pf false) (.seq (pf true) (pf true)))

/-- `ST := (Val.cons (Enc.bool false) st).bits`. -/
def pairF : Stmt (OInstr 20) := .seq (pf false) (pf true)

/-- The SAT-call branch of the loop body. -/
def invokeBranch (P : Program) (I : Indices) : Stmt (OInstr 20) :=
  .seq (flc P I.query rTMP) (.seq (toOracle (valToRaw rQ rTMP))
    (.seq (.ite (.call rQ) pairT pairF) (.seq (.prim (.basic (.clear rQ)))
      (.seq (flc P I.resume rTMP) moveST))))

/-- The ordinary-edge branch of the loop body. -/
def stepBranch (P : Program) (I : Indices) : Stmt (OInstr 20) :=
  .seq (flc P I.step rTMP) moveST

/-- One controller edge. -/
def body (P : Program) (I : Indices) : Stmt (OInstr 20) :=
  .seq (flc P I.isInvoke rTMP)
    (.seq (.ite (.basic (.headIs rTMP true)) (invokeBranch P I) (stepBranch P I))
      (flc P I.isDone rDN))

/-- The main loop: `while head DN ≠ true do body`. -/
def mainLoop (P : Program) (I : Indices) : Stmt (OInstr 20) :=
  .loop (.basic (.headIs rDN true)) false (body P I)

/-- Input conversion, initialisation, first termination test. -/
def preamble (P : Program) (I : Indices) : Stmt (OInstr 20) :=
  .seq (toOracle (rawToVal rST rIN)) (.seq (flc P I.init rTMP) (.seq moveST (flc P I.isDone rDN)))

/-- Output: `OUT := raw (output ST)`. -/
def postamble (P : Program) (I : Indices) : Stmt (OInstr 20) :=
  .seq (flc P I.output rTMP) (toOracle (valToRaw rOUT rTMP))

/-- **The top-level structured program.** -/
def mainProg (P : Program) (I : Indices) : SProg (OInstr 20) :=
  ⟨.seq (preamble P I) (.seq (mainLoop P I) (postamble P I)), .basic (.const true)⟩

end QecReliability.Assembly

end
