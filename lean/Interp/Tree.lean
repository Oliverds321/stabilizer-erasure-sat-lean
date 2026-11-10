import Interp.Basic
import FL.Encode

/-!
# Tree primitives on registers holding serialized trees

Registers hold preorder serializations `Val.bits` (`cons ↦ true`, `nil ↦ false`). All
operations read trees from the *front* of a source register, one bit at a time.

* `moveTree dst src c`: move the first serialized tree of `src` to the end of `dst`, using the
  register `c` as a unary counter of pending subtrees (`+1` on a `true` bit, `−1` on a `false`
  bit, stop at `0`). `5·|v| + 2` primitives (`moveTree_run`).
* Patterns `Pat` and `parseS`: split a serialized tree into registers (variables), skipping
  wildcards, checking nothing (`parse_run`, `parseL_run`).
* Templates `Tm` and `emitS`: build a serialized tree from constants and register contents
  (`emit_run`), one primitive per template node.
* `clearL`: clear a list of registers.
* `Trie`: dispatch on a fixed bit prefix of a register (`trie_run`), `tagTrie` for unary tags.
* `nthS`: index an encoded list with a unary index (`nthS_run`).
* `leafS`: parse; middle computation; emit; clear (`leaf_run`), the shape of every case of the
  interpreter's step.
-/

set_option autoImplicit false

namespace QecReliability.Interp
open QecReliability.RegMachine QecReliability.FL Function

variable {R B : ℕ}

/-! ## Moving one tree -/

/-- Three updates in the order of the move-loop body. -/
def upd3 (s : Regs R) (a : Fin R) (x : List Bool) (b : Fin R) (y : List Bool) (c : Fin R)
    (z : List Bool) : Regs R :=
  update (update (update s a x) b y) c z

/-- Loop body: move one bit from `src` to `dst`, updating the counter `c`. -/
def moveBody (dst src c : Fin R) : Stmt (Instr R) :=
  .seq (.ite (.headIs src true)
          (.seq (.prim (.pushBack dst true)) (.prim (.pushBack c true)))
          (.seq (.prim (.pushBack dst false)) (.prim (.popFront c))))
       (.prim (.popFront src))

/-- `while c ≠ [] do moveBody`. -/
def moveLoop (dst src c : Fin R) : Stmt (Instr R) :=
  .loop (.isEmpty c) false (moveBody dst src c)

/-- Move the first serialized tree of `src` to the end of `dst` (counter `c`, empty before
and after). -/
def moveTree (dst src c : Fin R) : Stmt (Instr R) :=
  .seq (.prim (.pushBack c true)) (moveLoop dst src c)

section Move
variable {dst src c : Fin R}

theorem upd3_upd3 (hds : dst ≠ src) (hdc : dst ≠ c) (hsc : src ≠ c) (s : Regs R)
    (x y z x' y' z' : List Bool) :
    upd3 (upd3 s dst x c y src z) dst x' c y' src z' = upd3 s dst x' c y' src z' := by
  funext r
  by_cases h1 : r = src
  · subst h1; simp [upd3]
  · by_cases h2 : r = c
    · subst h2; simp [upd3, h1]
    · by_cases h3 : r = dst
      · subst h3; simp [upd3, h1, h2]
      · simp [upd3, h1, h2, h3]

theorem replicate_succ_append (k : ℕ) :
    List.replicate (k + 1) true ++ [true] = List.replicate (k + 2) true := by
  conv_rhs => rw [show k + 2 = (k + 1) + 1 from rfl, List.replicate_succ']

theorem moveLoop_cont (hds : dst ≠ src) (hdc : dst ≠ c) (hsc : src ≠ c) (v : Val) :
    ∀ (k : ℕ) (rest d : List Bool) (s t : Regs R) (n : ℕ),
      s src = v.bits ++ rest → s c = List.replicate (k + 1) true → s dst = d → Fits B s →
      d.length + v.size ≤ B → k + v.size + 1 ≤ B →
      Runs B (moveLoop dst src c) (upd3 s dst (d ++ v.bits) c (List.replicate k true) src rest)
        t n →
      Runs B (moveLoop dst src c) s t (n + 5 * v.size) := by
  have hsd : src ≠ dst := Ne.symm hds
  have hcd : c ≠ dst := Ne.symm hdc
  have hcs : c ≠ src := Ne.symm hsc
  induction v with
  | nil =>
    intro k rest d s t n hs hc hd hfit hb1 hb2 hrun
    simp only [Val.bits, Val.size_nil, List.cons_append, List.nil_append] at hs hb1 hb2 hrun
    have hlen := hfit src
    rw [hs] at hlen
    simp only [List.length_cons] at hlen
    set s1 := update s dst (d ++ [false]) with hs1
    have hf1 : Fits B s1 := fits_upd hfit (by simp; omega)
    have h1 : Runs B (.prim (.pushBack dst false)) s s1 1 := Runs.pushBack false hfit hd (by omega)
    have hc1 : s1 c = true :: List.replicate k true := by
      rw [hs1, update_of_ne hcd, hc, List.replicate_succ]
    set s2 := update s1 c (List.replicate k true) with hs2
    have h2 : Runs B (.prim (.popFront c)) s1 s2 1 := Runs.popFront hf1 hc1
    have hf2 : Fits B s2 := h2.fits_end
    have hsrc2 : s2 src = false :: rest := by rw [hs2, update_of_ne hsc, hs1, update_of_ne hsd, hs]
    have h3 : Runs B (.prim (.popFront src)) s2 (update s2 src rest) 1 := Runs.popFront hf2 hsrc2
    have hbody : Runs B (moveBody dst src c) s
        (upd3 s dst (d ++ [false]) c (List.replicate k true) src rest) (1 + 1 + 1 + 1) := by
      refine Runs.seq (Runs.iteF hfit trivial (by simp [Instr.eval, hs]) (h1.seq h2)) h3
    have := Runs.loopT (tp := .isEmpty c) (pol := false) hfit trivial (by simp [Instr.eval, hc]) hbody hrun
    exact this.mono (by simp only [Val.size_nil]; omega)
  | cons a b iha ihb =>
    intro k rest d s t n hs hc hd hfit hb1 hb2 hrun
    simp only [Val.bits, Val.size_cons, List.cons_append, List.append_assoc] at hs hb1 hb2 hrun
    have ha1 := Val.size_pos a
    have hb1' := Val.size_pos b
    have hlen := hfit src
    rw [hs] at hlen
    simp only [List.length_cons, List.length_append, Val.bits_length] at hlen
    set s1 := update s dst (d ++ [true]) with hs1
    have hf1 : Fits B s1 := fits_upd hfit (by simp; omega)
    have h1 : Runs B (.prim (.pushBack dst true)) s s1 1 := Runs.pushBack true hfit hd (by omega)
    have hc1 : s1 c = List.replicate (k + 1) true := by rw [hs1, update_of_ne hcd, hc]
    set s2 := update s1 c (List.replicate (k + 2) true) with hs2
    have h2 : Runs B (.prim (.pushBack c true)) s1 s2 1 := by
      have := Runs.pushBack true hf1 hc1 (by simp; omega)
      rwa [replicate_succ_append] at this
    have hf2 : Fits B s2 := h2.fits_end
    have hsrc2 : s2 src = true :: (a.bits ++ (b.bits ++ rest)) := by
      rw [hs2, update_of_ne hsc, hs1, update_of_ne hsd, hs]
    have h3 : Runs B (.prim (.popFront src)) s2 (update s2 src (a.bits ++ (b.bits ++ rest))) 1 :=
      Runs.popFront hf2 hsrc2
    set s3 := upd3 s dst (d ++ [true]) c (List.replicate (k + 2) true) src
      (a.bits ++ (b.bits ++ rest)) with hs3
    have hbody : Runs B (moveBody dst src c) s s3 (1 + 1 + 1 + 1) := by
      refine Runs.seq (Runs.iteT hfit trivial (by simp [Instr.eval, hs]) (h1.seq h2)) h3
    have hf3 : Fits B s3 := hbody.fits_end
    -- the right subtree, then the left subtree, by continuation
    set s4 := upd3 s dst (d ++ [true] ++ a.bits) c (List.replicate (k + 1) true) src
      (b.bits ++ rest) with hs4
    have hf4 : Fits B s4 := by
      simp only [hs4, upd3]
      refine fits_upd (fits_upd (fits_upd hfit ?_) ?_) ?_
      · simp; omega
      · simp; omega
      · simp; omega
    have hrunB : Runs B (moveLoop dst src c) s4 t (n + 5 * b.size) := by
      refine ihb k rest (d ++ [true] ++ a.bits) s4 t n ?_ ?_ ?_ hf4 ?_ ?_ ?_
      · simp [hs4, upd3]
      · simp [hs4, upd3, hcs]
      · simp [hs4, upd3, hds, hdc]
      · simp; omega
      · omega
      · rw [hs4, upd3_upd3 hds hdc hsc]
        simpa [List.append_assoc] using hrun
    have hrunA : Runs B (moveLoop dst src c) s3 t (n + 5 * b.size + 5 * a.size) := by
      refine iha (k + 1) (b.bits ++ rest) (d ++ [true]) s3 t _ ?_ ?_ ?_ hf3 ?_ ?_ ?_
      · simp [hs3, upd3]
      · simp [hs3, upd3, hcs]
      · simp [hs3, upd3, hds, hdc]
      · simp; omega
      · omega
      · rw [hs3, upd3_upd3 hds hdc hsc]
        exact hrunB
    have := Runs.loopT (tp := .isEmpty c) (pol := false) hfit trivial (by simp [Instr.eval, hc]) hbody hrunA
    exact this.mono (by simp only [Val.size_cons]; omega)

/-- **Moving a tree.** `src = v.bits ++ rest`, `c = []`, `dst = d` ↦
`dst = d ++ v.bits`, `src = rest`, `c = []`, other registers unchanged; `5|v| + 2` primitives. -/
theorem moveTree_run (hds : dst ≠ src) (hdc : dst ≠ c) (hsc : src ≠ c) {v : Val}
    {rest d : List Bool} {s : Regs R} (hs : s src = v.bits ++ rest) (hc : s c = [])
    (hd : s dst = d) (hfit : Fits B s) (hb1 : d.length + v.size ≤ B) (hb2 : v.size + 1 ≤ B) :
    Runs B (moveTree dst src c) s (upd3 s dst (d ++ v.bits) c [] src rest) (5 * v.size + 2) := by
  have hcd : c ≠ dst := Ne.symm hdc
  have hcs : c ≠ src := Ne.symm hsc
  have hsz := Val.size_pos v
  set s0 := update s c [true] with hs0
  have h0 : Runs B (.prim (.pushBack c true)) s s0 1 := by
    have := Runs.pushBack true hfit hc (by simp; omega)
    simpa using this
  have hf0 : Fits B s0 := h0.fits_end
  have hfin : upd3 s0 dst (d ++ v.bits) c (List.replicate 0 true) src rest =
      upd3 s dst (d ++ v.bits) c [] src rest := by
    funext r
    by_cases h1 : r = src
    · subst h1; simp [upd3]
    · by_cases h2 : r = c
      · subst h2; simp [upd3, h1]
      · by_cases h3 : r = dst
        · subst h3; simp [upd3, hs0, h1, h2]
        · simp [upd3, hs0, h1, h2, h3]
  have hlast : Runs B (moveLoop dst src c)
      (upd3 s0 dst (d ++ v.bits) c (List.replicate 0 true) src rest)
      (upd3 s dst (d ++ v.bits) c [] src rest) 1 := by
    rw [hfin]
    have hf : Fits B (upd3 s dst (d ++ v.bits) c [] src rest) := by
      simp only [upd3]
      refine fits_upd (fits_upd (fits_upd hfit ?_) ?_) ?_
      · simp; omega
      · simp
      · have := hfit src; rw [hs] at this; simp at this; omega
    exact Runs.loopF (tp := .isEmpty c) (pol := false) (c := true) hf trivial (by simp [Instr.eval, upd3, hcs]) (by decide)
  have := moveLoop_cont hds hdc hsc v 0 rest d s0 _ 1 (by simp [hs0, update_of_ne hsc, hs])
    (by simp [hs0]) (by simp [hs0, update_of_ne hdc, hd]) hf0 hb1 (by omega) hlast
  have := h0.seq this
  exact this.mono (by omega)

end Move

end QecReliability.Interp
