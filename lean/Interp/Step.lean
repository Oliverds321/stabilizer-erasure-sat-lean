import Interp.Parse
import FL.StepV

/-!
# One CEK step as a register program

The interpreter works on 16 local registers (`Fin 16`):

| reg | role |
|---|---|
| 0 `rA` | argument (only read, by the wrapper `Interp/Call.lean`) |
| 1 `rB` | result (written by the wrapper) |
| 2 `rS` | the encoded CEK state `State.enc` |
| 3 `rP` | the encoded program `Program.enc P` (read only) |
| 4 `rH` | halt flag (`[]` while running, `[true]` after the final state) |
| 5 `rC` | counter of `moveTree` |
| 6 `rJ` | junk (wildcards) |
| 7 `rV` | returned value (ret mode) |
| 8–11 `rX rY rZ rU` | pattern variables |
| 12 `rL` | environment / list being indexed |
| 13 `rK` | continuation stack |
| 14 `rI` | unary index |
| 15 `rW` | result of `nthS` |

`stepS` is a decision tree mirroring `FL.step`: a `Trie` on the fixed prefix of the state
(mode bit, the expression tag or — after moving the returned value to `rV` — the frame tag),
then a leaf that parses the rest of the state into variable registers, possibly indexes a list
(`nthS`, for variables and calls), writes the successor state from a template, and clears its
registers. All registers `4..15` are empty before and after a step (`Clean`).

Main results: `stepS_run` (every successful `FL.step`) and `stepS_halt` (the final state
`ret y []`: `rS := y.bits`, `rH := [true]`).
-/

set_option autoImplicit false

namespace QecReliability.Interp
open QecReliability.RegMachine QecReliability.FL Function

local notation "rA" => (0 : Fin 16)
local notation "rB" => (1 : Fin 16)
local notation "rS" => (2 : Fin 16)
local notation "rP" => (3 : Fin 16)
local notation "rH" => (4 : Fin 16)
local notation "rC" => (5 : Fin 16)
local notation "rJ" => (6 : Fin 16)
local notation "rV" => (7 : Fin 16)
local notation "rX" => (8 : Fin 16)
local notation "rY" => (9 : Fin 16)
local notation "rZ" => (10 : Fin 16)
local notation "rU" => (11 : Fin 16)
local notation "rL" => (12 : Fin 16)
local notation "rK" => (13 : Fin 16)
local notation "rI" => (14 : Fin 16)
local notation "rW" => (15 : Fin 16)

variable {B : ℕ}

/-- Scratch registers `4..15` are empty. -/
def Clean (s : Regs 16) : Prop := ∀ r : Fin 16, 4 ≤ r.val → s r = []

theorem Clean.upd_S {s : Regs 16} (hc : Clean s) (x : List Bool) : Clean (update s rS x) := by
  intro r hr
  rw [update_of_ne (by intro e; subst e; simp at hr)]
  exact hc r hr

/-! ## Templates and leaves -/

/-- Template of `unary j`. -/
def tU : ℕ → Tm 16
  | 0 => .nil
  | j + 1 => .cons .nil (tU j)

/-- Template of `State.enc (.eval e env k)`. -/
def tEv (e env k : Tm 16) : Tm 16 := .cons .nil (.cons e (.cons env k))
/-- Template of `State.enc (.ret v k)`. -/
def tRt (v k : Tm 16) : Tm 16 := .cons (tU 1) (.cons v k)
/-- Template of a frame with tag `j`. -/
def tFr (j : ℕ) (x : Tm 16) : Tm 16 := .cons (tU j) x

/-- A leaf on the state register. -/
def leaf (ps : List (Pat 16)) (mid : Stmt (Instr 16)) (tm : Tm 16) (clr : List (Fin 16)) :
    Stmt (Instr 16) :=
  leafS rS rC rJ ps mid tm clr

/-- A ret-mode leaf: first put the returned value back in front of the state. -/
def rleaf (ps : List (Pat 16)) (mid : Stmt (Instr 16)) (tm : Tm 16) (clr : List (Fin 16)) :
    Stmt (Instr 16) :=
  .seq (restoreS rV rS) (leaf ps mid tm clr)

/-! ### Eval mode (after the expression tag; `rS = payload ++ (cons env k)`) -/

def evVar : Stmt (Instr 16) :=
  leaf [.var rI, .cons (.var rL) (.var rK)] (nthS rL rI rW rC rJ) (tRt (.reg rW) (.reg rK))
    [rI, rL, rK, rW]
def evNil : Stmt (Instr 16) :=
  leaf [.wild, .cons .wild (.var rK)] nop (tRt .nil (.reg rK)) [rK]
def evCons : Stmt (Instr 16) :=
  leaf [.cons (.var rX) (.var rY), .cons (.var rL) (.var rK)] nop
    (tEv (.reg rX) (.reg rL) (.cons (tFr 0 (.cons (.reg rY) (.reg rL))) (.reg rK))) [rX, rY, rL, rK]
def evCase : Stmt (Instr 16) :=
  leaf [.cons (.var rX) (.cons (.var rY) (.var rZ)), .cons (.var rL) (.var rK)] nop
    (tEv (.reg rX) (.reg rL) (.cons (tFr 2 (.cons (.reg rY) (.cons (.reg rZ) (.reg rL)))) (.reg rK)))
    [rX, rY, rZ, rL, rK]
def evCall : Stmt (Instr 16) :=
  leaf [.cons (.var rX) (.var rY), .cons (.var rL) (.var rK)] nop
    (tEv (.reg rY) (.reg rL) (.cons (tFr 3 (.reg rX)) (.reg rK))) [rX, rY, rL, rK]
def evLet : Stmt (Instr 16) :=
  leaf [.cons (.var rX) (.var rY), .cons (.var rL) (.var rK)] nop
    (tEv (.reg rX) (.reg rL) (.cons (tFr 4 (.cons (.reg rY) (.reg rL))) (.reg rK))) [rX, rY, rL, rK]
def evCond : Stmt (Instr 16) :=
  leaf [.cons (.var rX) (.cons (.var rY) (.var rZ)), .cons (.var rL) (.var rK)] nop
    (tEv (.reg rX) (.reg rL) (.cons (tFr 5 (.cons (.reg rY) (.cons (.reg rZ) (.reg rL)))) (.reg rK)))
    [rX, rY, rZ, rL, rK]
def evFst : Stmt (Instr 16) :=
  leaf [.var rX, .cons (.var rL) (.var rK)] nop
    (tEv (.reg rX) (.reg rL) (.cons (tFr 6 .nil) (.reg rK))) [rX, rL, rK]
def evSnd : Stmt (Instr 16) :=
  leaf [.var rX, .cons (.var rL) (.var rK)] nop
    (tEv (.reg rX) (.reg rL) (.cons (tFr 7 .nil) (.reg rK))) [rX, rL, rK]

/-- Eval-mode leaves, indexed by the expression tag. -/
def evLeaves : List (Stmt (Instr 16)) :=
  [evVar, evNil, evCons, evCase, evCall, evLet, evCond, evFst, evSnd]

/-! ### Ret mode (after the frame tag; `rV = v`, `rS = payload ++ k`) -/

def frConsL : Stmt (Instr 16) :=
  rleaf [.var rX, .cons (.var rY) (.var rL), .var rK] nop
    (tEv (.reg rY) (.reg rL) (.cons (tFr 1 (.reg rX)) (.reg rK))) [rX, rY, rL, rK]
def frConsR : Stmt (Instr 16) :=
  rleaf [.var rY, .var rX, .var rK] nop (tRt (.cons (.reg rX) (.reg rY)) (.reg rK)) [rX, rY, rK]
def frSelNil : Stmt (Instr 16) :=
  rleaf [.nil, .cons (.var rX) (.cons .wild (.var rL)), .var rK] nop
    (tEv (.reg rX) (.reg rL) (.reg rK)) [rX, rL, rK]
def frCaseCons : Stmt (Instr 16) :=
  rleaf [.cons (.var rZ) (.var rU), .cons .wild (.cons (.var rY) (.var rL)), .var rK] nop
    (tEv (.reg rY) (.cons (.reg rZ) (.cons (.reg rU) (.reg rL))) (.reg rK)) [rY, rZ, rU, rL, rK]
def frCondCons : Stmt (Instr 16) :=
  rleaf [.cons .wild .wild, .cons .wild (.cons (.var rY) (.var rL)), .var rK] nop
    (tEv (.reg rY) (.reg rL) (.reg rK)) [rY, rL, rK]
def frCase : Stmt (Instr 16) := .ite (.headIs rV false) frSelNil frCaseCons
def frCall : Stmt (Instr 16) :=
  rleaf [.var rX, .var rI, .var rK] (.seq (.prim (.append rL rP)) (nthS rL rI rW rC rJ))
    (tEv (.reg rW) (.cons (.reg rX) .nil) (.reg rK)) [rX, rI, rK, rL, rW]
def frLet : Stmt (Instr 16) :=
  rleaf [.var rX, .cons (.var rY) (.var rL), .var rK] nop
    (tEv (.reg rY) (.cons (.reg rX) (.reg rL)) (.reg rK)) [rX, rY, rL, rK]
def frCond : Stmt (Instr 16) := .ite (.headIs rV false) frSelNil frCondCons
def frFst : Stmt (Instr 16) :=
  rleaf [.cons (.var rX) .wild, .nil, .var rK] nop (tRt (.reg rX) (.reg rK)) [rX, rK]
def frSnd : Stmt (Instr 16) :=
  rleaf [.cons .wild (.var rX), .nil, .var rK] nop (tRt (.reg rX) (.reg rK)) [rX, rK]

/-- Ret-mode leaves, indexed by the frame tag. -/
def frLeaves : List (Stmt (Instr 16)) :=
  [frConsL, frConsR, frCase, frCall, frLet, frCond, frFst, frSnd]

/-- The final state `ret y []`: `rS := y`, raise the halt flag. -/
def haltLeaf : Stmt (Instr 16) :=
  .seq (.prim (.append rS rV)) (.seq (.prim (.clear rV)) (.prim (.pushBack rH true)))

/-- Ret mode after moving the value to `rV`: empty stack (halt) or frame tag. -/
def frameTrie : Trie 16 := .br (.leaf haltLeaf) (.pop (tagTrie frLeaves))

def retStmt : Stmt (Instr 16) := .seq (moveTree rV rS rC) (frameTrie.code rS)

/-- Prefix of the state: `cons`, mode (`u0` eval / `u1` ret), … -/
def topTrie : Trie 16 :=
  .pop (.br (.pop (.pop (tagTrie evLeaves))) (.pop (.pop (.pop (.leaf retStmt)))))

/-- **One CEK step on the state register `rS`.** -/
def stepS : Stmt (Instr 16) := topTrie.code rS

/-! ## Dispatch -/

theorem eval_size (j : ℕ) (pay E Kv : Val) :
    (flatBits [pay, .cons E Kv]).length + 2 * j + 5 =
      (Val.cons .nil (.cons (.cons (Enc.unary j) pay) (.cons E Kv))).size := by
  simp only [flatBits, List.length_append, Val.bits_length, Val.size_cons, Val.size_nil,
    Enc.unary_size, List.length_nil]
  omega

theorem eval_dispatch {j : ℕ} {st : Stmt (Instr 16)} (hj : evLeaves[j]? = some st)
    {pay E Kv : Val} {s t : Regs 16} {n : ℕ} (hfit : Fits B s)
    (hS : s rS = (Val.cons .nil (.cons (.cons (Enc.unary j) pay) (.cons E Kv))).bits)
    (h : Runs B st (update s rS (flatBits [pay, .cons E Kv])) t n) :
    Runs B stepS s t (n + 3 * (2 * j + 5)) := by
  have hw : topTrie.walk ([true, false, true, true] ++ (Enc.unary j).bits) = some st := by
    have e : topTrie.walk ([true, false, true, true] ++ (Enc.unary j).bits) =
        (tagTrie evLeaves).walk (Enc.unary j).bits := rfl
    rw [e, tagTrie_walk]; exact hj
  have hS' : s rS = [true, false, true, true] ++ (Enc.unary j).bits ++ flatBits [pay, .cons E Kv] := by
    rw [hS]; simp [Val.bits, flatBits]
  have := trie_run (src := rS) _ topTrie st s t _ n hw hS' hfit h
  refine this.mono ?_
  simp

theorem ret_size (j : ℕ) (v pay Kv : Val) :
    (flatBits [v, pay, Kv]).length + 2 * j + 8 =
      (Val.cons (Enc.unary 1) (.cons v (.cons (.cons (Enc.unary j) pay) Kv))).size := by
  simp only [flatBits, List.length_append, Val.bits_length, Val.size_cons,
    Enc.unary_size, List.length_nil]
  omega

theorem ret_prefix {s t : Regs 16} {n : ℕ} {v rest : Val} (hfit : Fits B s)
    (hS : s rS = (Val.cons (Enc.unary 1) (.cons v rest)).bits)
    (h : Runs B retStmt (update s rS (v.bits ++ rest.bits)) t n) :
    Runs B stepS s t (n + 15) := by
  have hw : topTrie.walk [true, true, false, false, true] = some retStmt := rfl
  have hS' : s rS = [true, true, false, false, true] ++ (v.bits ++ rest.bits) := by
    rw [hS]; simp [Val.bits, Enc.unary]
  exact trie_run (src := rS) _ topTrie retStmt s t _ n hw hS' hfit h

theorem ret_dispatch {j : ℕ} {st : Stmt (Instr 16)} (hj : frLeaves[j]? = some st)
    {v pay Kv : Val} {s t : Regs 16} {n : ℕ} (hfit : Fits B s)
    (hS : s rS = (Val.cons (Enc.unary 1) (.cons v (.cons (.cons (Enc.unary j) pay) Kv))).bits)
    (hV : s rV = []) (hC : s rC = []) (hB : v.size + 1 ≤ B)
    (h : Runs B st (update (update s rV v.bits) rS (pay.bits ++ Kv.bits)) t n) :
    Runs B stepS s t (n + 3 * (2 * j + 3) + 5 * v.size + 17) := by
  set rest := Val.cons (.cons (Enc.unary j) pay) Kv with hrest
  set s1 := update s rS (v.bits ++ rest.bits) with hs1
  have hf1 : Fits B s1 := fits_upd hfit (by
    have := hfit rS; rw [hS] at this; simp [Val.bits] at this ⊢; omega)
  have hm := moveTree_run (B := B) (dst := rV) (src := rS) (c := rC) (by decide) (by decide)
    (by decide) (s := s1) (v := v) (rest := rest.bits) (d := []) (by simp [hs1])
    (by simp [hs1, hC]) (by simp [hs1, hV]) hf1 (by simp; omega) hB
  set s2 := upd3 s1 rV ([] ++ v.bits) rC [] rS rest.bits with hs2
  have hw : frameTrie.walk ([true, true] ++ (Enc.unary j).bits) = some st := by
    have e : frameTrie.walk ([true, true] ++ (Enc.unary j).bits) =
        (tagTrie frLeaves).walk (Enc.unary j).bits := rfl
    rw [e, tagTrie_walk]; exact hj
  have hs2S : s2 rS = [true, true] ++ (Enc.unary j).bits ++ (pay.bits ++ Kv.bits) := by
    simp [hs2, upd3, hrest, Val.bits]
  have e : update s2 rS (pay.bits ++ Kv.bits) = update (update s rV v.bits) rS (pay.bits ++ Kv.bits) := by
    funext q
    by_cases hq1 : q = rS
    · subst hq1; simp
    · by_cases hq2 : q = rC
      · subst hq2; simp [hs2, upd3, hs1, hC]
      · by_cases hq3 : q = rV
        · subst hq3; simp [hs2, upd3]
        · simp [hs2, upd3, hs1, hq1, hq2, hq3]
  rw [← e] at h
  have ht := (trie_run (src := rS) _ frameTrie st s2 t _ n hw hs2S hm.fits_end h).mono
    (n' := n + 3 * (2 + (2 * j + 1))) (by simp; omega)
  have hr := ret_prefix (n := 5 * v.size + 2 + (n + 3 * (2 + (2 * j + 1)))) hfit hS (hm.seq ht)
  refine hr.mono ?_
  simp; omega

/-- **The final state.** `ret y []` ↦ `rS := y.bits`, `rH := [true]`. -/
theorem stepS_halt {y : Val} {s : Regs 16} (hfit : Fits B s)
    (hS : s rS = (State.ret y []).enc.bits) (hc : Clean s) (hB : y.size + 1 ≤ B) :
    Runs B stepS s (update (update s rS y.bits) rH [true]) (5 * y.size + 25) := by
  have hV : s rV = [] := hc rV (by decide)
  have hC : s rC = [] := hc rC (by decide)
  have hH : s rH = [] := hc rH (by decide)
  set s1 := update s rS (y.bits ++ Val.nil.bits) with hs1
  have hf1 : Fits B s1 := fits_upd hfit (by simp; omega)
  have hm := moveTree_run (B := B) (dst := rV) (src := rS) (c := rC) (by decide) (by decide)
    (by decide) (s := s1) (v := y) (rest := Val.nil.bits) (d := []) (by simp [hs1])
    (by simp [hs1, hC]) (by simp [hs1, hV]) hf1 (by simp; omega) hB
  set s2 := upd3 s1 rV ([] ++ y.bits) rC [] rS Val.nil.bits with hs2
  have hf2 := hm.fits_end
  -- halt leaf from `update s2 rS []`
  set s3 := update s2 rS [] with hs3
  have hf3 : Fits B s3 := fits_upd hf2 (by simp)
  have h1 := Runs.append (d := rS) (r := rV) (x := []) (y := y.bits) hf3 (by decide)
    (by simp [hs3]) (by simp [hs3, hs2, upd3]) (by simp; omega)
  have h2 := Runs.clear h1.fits_end rV
  have h3 := Runs.pushBack (r := rH) (w := []) true h2.fits_end (by simp [hs3, hs2, upd3, hs1, hH])
    (by simp; omega)
  have e : update (update (update s3 rS ([] ++ y.bits)) rV []) rH ([] ++ [true]) =
      update (update s rS y.bits) rH [true] := by
    funext q
    by_cases hq1 : q = rH
    · subst hq1; simp
    · by_cases hq2 : q = rV
      · subst hq2; simp [hV]
      · by_cases hq3 : q = rS
        · subst hq3; simp
        · by_cases hq4 : q = rC
          · subst hq4; simp [hs3, hs2, upd3, hC]
          · simp [hs3, hs2, upd3, hs1, hq1, hq2, hq3, hq4]
  rw [e] at h3
  have hleaf : Runs B haltLeaf s3 (update (update s rS y.bits) rH [true]) 3 :=
    h1.seq (h2.seq h3)
  have hw : frameTrie.walk [false] = some haltLeaf := rfl
  have ht := trie_run (src := rS) [false] frameTrie haltLeaf s2 _ [] 3 hw
    (by simp [hs2, upd3, Val.bits]) hf2 hleaf
  have hr := ret_prefix (v := y) (rest := .nil) hfit hS (hm.seq ht)
  exact hr.mono (by simp)

end QecReliability.Interp
