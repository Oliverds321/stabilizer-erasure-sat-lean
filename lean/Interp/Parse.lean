import Interp.Tree

/-!
# Patterns, templates, dispatch, list indexing, leaves

* `Pat`, `parseS`, `parse_run`, `parseL_run`: split serialized trees at the front of a register
  into variable registers.
* `Tm`, `emitS`, `emit_run`: append the serialization of a template.
* `clearL`, `clearL_run`.
* `Trie`, `trie_run`, `tagTrie_walk`: dispatch on a fixed bit prefix / a unary tag.
* `nthS`, `nthS_run`: index an encoded list with a unary index.
* `restoreS`, `restore_run`: `S := V ++ S`.
* `leafS`, `leaf_run`, `leaf_run_nop`: parse; compute; emit; clean.
-/

set_option autoImplicit false

namespace QecReliability.Interp
open QecReliability.RegMachine QecReliability.FL Function

variable {R B : ℕ}

/-! ## Patterns: splitting a serialized tree into registers -/

/-- Tree patterns: a variable register receives the subtree, a wildcard skips it, `nil`
consumes a `false` bit, `cons` consumes a `true` bit and two subpatterns. Nothing is checked:
the parse is only specified on matching inputs. -/
inductive Pat (R : ℕ) where
  | var (r : Fin R)
  | wild
  | nil
  | cons (p q : Pat R)

/-- Variables of a pattern, left to right. -/
def Pat.vars : Pat R → List (Fin R)
  | .var r => [r]
  | .wild => []
  | .nil => []
  | .cons p q => p.vars ++ q.vars

/-- `v` matches `p`, the variables taking the values `σ`. -/
inductive PMatch (σ : Fin R → Val) : Pat R → Val → Prop
  | var {r : Fin R} {v : Val} : σ r = v → PMatch σ (.var r) v
  | wild (v : Val) : PMatch σ .wild v
  | nil : PMatch σ .nil .nil
  | cons {p q : Pat R} {a b : Val} : PMatch σ p a → PMatch σ q b → PMatch σ (.cons p q) (.cons a b)

/-- Parse one tree off the front of `src` along a pattern (counter `c`, junk register `j`). -/
def parseS (src c j : Fin R) : Pat R → Stmt (Instr R)
  | .var r => moveTree r src c
  | .wild => .seq (moveTree j src c) (.prim (.clear j))
  | .nil => .prim (.popFront src)
  | .cons p q => .seq (.prim (.popFront src)) (.seq (parseS src c j p) (parseS src c j q))

/-- Register file after a parse: variables hold their values, `src` holds the rest. -/
def parsePost (σ : Fin R → Val) (vars : List (Fin R)) (src : Fin R) (rest : List Bool)
    (s : Regs R) : Regs R :=
  fun r => if r ∈ vars then (σ r).bits else if r = src then rest else s r

theorem parsePost_trans {σ : Fin R → Val} {l1 l2 : List (Fin R)} {src : Fin R}
    (h1 : src ∉ l1) (h2 : src ∉ l2) (rest mid x : List Bool) (s : Regs R) :
    parsePost σ l2 src rest (parsePost σ l1 src mid (update s src x)) =
      parsePost σ (l1 ++ l2) src rest s := by
  funext r
  simp only [parsePost, List.mem_append]
  by_cases hr2 : r ∈ l2
  · simp [hr2]
  · by_cases hrs : r = src
    · subst hrs; simp [h1, h2]
    · by_cases hr1 : r ∈ l1
      · simp [hr1, hr2, hrs]
      · simp [hr1, hr2, hrs]

theorem parse_run {src c j : Fin R} (hsc : src ≠ c) (hsj : src ≠ j) (hcj : c ≠ j)
    {σ : Fin R → Val} {p : Pat R} {v : Val} (hm : PMatch σ p v) :
    ∀ (s : Regs R) (rest : List Bool), s src = v.bits ++ rest → s c = [] → s j = [] →
      (∀ r ∈ p.vars, s r = []) → p.vars.Nodup → src ∉ p.vars → c ∉ p.vars → j ∉ p.vars →
      Fits B s → v.size + 1 ≤ B →
      Runs B (parseS src c j p) s (parsePost σ p.vars src rest s) (5 * v.size + 3) := by
  induction hm with
  | @var r v hr =>
    intro s rest hs hc hj hvars _ hsrc hcv _ hfit hB
    simp only [Pat.vars, List.mem_singleton, forall_eq] at hvars hsrc hcv
    have hrun := moveTree_run (B := B) (dst := r) (src := src) (c := c) (Ne.symm hsrc)
      (Ne.symm hcv) hsc hs hc hvars hfit (by simp; omega) hB
    have e : upd3 s r ([] ++ v.bits) c [] src rest = parsePost σ [r] src rest s := by
      funext q
      by_cases h1 : q = src
      · subst h1; simp [upd3, parsePost, hsrc]
      · by_cases h2 : q = c
        · subst h2; simp [upd3, parsePost, h1, hcv, hc]
        · by_cases h3 : q = r
          · subst h3; simp [upd3, parsePost, h1, h2, hr]
          · simp [upd3, parsePost, h1, h2, h3]
    rw [e] at hrun
    simp only [Pat.vars, parseS]
    exact hrun.mono (by omega)
  | wild v =>
    intro s rest hs hc hj _ _ _ _ _ hfit hB
    have hrun := moveTree_run (B := B) (dst := j) (src := src) (c := c) (Ne.symm hsj)
      (Ne.symm hcj) hsc hs hc hj hfit (by simp; omega) hB
    have hcl := Runs.clear hrun.fits_end j
    have e : update (upd3 s j ([] ++ v.bits) c [] src rest) j [] = parsePost σ [] src rest s := by
      funext q
      by_cases h1 : q = j
      · subst h1; simp [parsePost, hj, Ne.symm hsj]
      · by_cases h2 : q = src
        · subst h2; simp [upd3, parsePost, h1]
        · by_cases h3 : q = c
          · subst h3; simp [upd3, parsePost, h1, h2, hc]
          · simp [upd3, parsePost, h1, h2, h3]
    rw [e] at hcl
    simp only [Pat.vars, parseS]
    exact (hrun.seq hcl).mono (by omega)
  | nil =>
    intro s rest hs _ _ _ _ _ _ _ hfit _
    simp only [Val.bits, List.cons_append, List.nil_append] at hs
    have h := Runs.popFront hfit hs
    have e : update s src rest = parsePost σ [] src rest s := by
      funext q; by_cases h : q = src
      · subst h; simp [parsePost]
      · simp [parsePost, h]
    rw [e] at h
    simp only [Pat.vars, parseS]
    exact h.mono (by simp)
  | @cons p q a b _ _ ihp ihq =>
    intro s rest hs hc hj hvars hnd hsrc hcv hjv hfit hB
    simp only [Pat.vars, List.mem_append, not_or] at hvars hsrc hcv hjv
    simp only [Pat.vars] at hnd
    obtain ⟨hndp, hndq, hdis⟩ := List.nodup_append.mp hnd
    simp only [Val.bits, Val.size_cons, List.cons_append, List.append_assoc] at hs hB
    have h1 := Runs.popFront hfit hs
    have hf1 := h1.fits_end
    have h2 := ihp (update s src (a.bits ++ (b.bits ++ rest))) (b.bits ++ rest) (by simp)
      (by rw [update_of_ne (Ne.symm hsc)]; exact hc) (by rw [update_of_ne (Ne.symm hsj)]; exact hj)
      (fun r hr => by
        rw [update_of_ne (show r ≠ src from fun h => hsrc.1 (h ▸ hr))]
        exact hvars r (Or.inl hr))
      hndp hsrc.1 hcv.1 hjv.1 hf1 (by omega)
    have hf2 := h2.fits_end
    have h3 := ihq
      (parsePost σ p.vars src (b.bits ++ rest) (update s src (a.bits ++ (b.bits ++ rest))))
      rest (by simp [parsePost, hsrc.1])
      (by simp [parsePost, hcv.1, Ne.symm hsc, hc]) (by simp [parsePost, hjv.1, Ne.symm hsj, hj])
      (fun r hr => by
        have hrp : r ∉ p.vars := fun h => hdis r h r hr rfl
        have hrs : r ≠ src := fun h => hsrc.2 (h ▸ hr)
        simp [parsePost, hrp, hrs]; exact hvars r (Or.inr hr))
      hndq hsrc.2 hcv.2 hjv.2 hf2 (by omega)
    rw [parsePost_trans hsrc.1 hsrc.2] at h3
    simp only [Pat.vars, parseS, Val.size_cons]
    exact (h1.seq (h2.seq h3)).mono (by omega)

/-! ### Pattern sequences -/

/-- Variables of a pattern sequence. -/
def Pat.varsL : List (Pat R) → List (Fin R)
  | [] => []
  | p :: ps => p.vars ++ Pat.varsL ps

/-- A sequence of values matches a sequence of patterns. -/
inductive PMatchL (σ : Fin R → Val) : List (Pat R) → List Val → Prop
  | nil : PMatchL σ [] []
  | cons {p : Pat R} {ps : List (Pat R)} {v : Val} {vs : List Val} :
      PMatch σ p v → PMatchL σ ps vs → PMatchL σ (p :: ps) (v :: vs)

/-- Concatenated serializations. -/
def flatBits : List Val → List Bool
  | [] => []
  | v :: vs => v.bits ++ flatBits vs

/-- Parse a sequence of trees off the front of `src`. -/
def parseL (src c j : Fin R) : List (Pat R) → Stmt (Instr R)
  | [] => nop
  | p :: ps => .seq (parseS src c j p) (parseL src c j ps)

theorem parseL_run {src c j : Fin R} (hsc : src ≠ c) (hsj : src ≠ j) (hcj : c ≠ j)
    {σ : Fin R → Val} {ps : List (Pat R)} {vs : List Val} (hm : PMatchL σ ps vs) :
    ∀ (s : Regs R) (rest : List Bool), s src = flatBits vs ++ rest → s c = [] → s j = [] →
      (∀ r ∈ Pat.varsL ps, s r = []) → (Pat.varsL ps).Nodup → src ∉ Pat.varsL ps →
      c ∉ Pat.varsL ps → j ∉ Pat.varsL ps → Fits B s → (flatBits vs).length + 1 ≤ B →
      Runs B (parseL src c j ps) s (parsePost σ (Pat.varsL ps) src rest s)
        (5 * (flatBits vs).length + 3 * ps.length + 1) := by
  induction hm with
  | nil =>
    intro s rest hs _ _ _ _ _ _ _ hfit _
    simp only [flatBits, List.nil_append] at hs
    have e : parsePost σ (Pat.varsL ([] : List (Pat R))) src rest s = s := by
      funext q; by_cases h : q = src
      · subst h; simp [parsePost, Pat.varsL, hs]
      · simp [parsePost, Pat.varsL, h]
    rw [e]
    exact (Runs.nop hfit).mono (by simp)
  | @cons p ps v vs hp _ ih =>
    intro s rest hs hc hj hvars hnd hsrc hcv hjv hfit hB
    simp only [Pat.varsL, List.mem_append, not_or] at hvars hsrc hcv hjv
    simp only [Pat.varsL] at hnd
    obtain ⟨hndp, hndq, hdis⟩ := List.nodup_append.mp hnd
    simp only [flatBits, List.append_assoc, List.length_append, Val.bits_length] at hs hB
    have h1 := parse_run hsc hsj hcj hp s (flatBits vs ++ rest) hs hc hj
      (fun r hr => hvars r (Or.inl hr)) hndp hsrc.1 hcv.1 hjv.1 hfit (by omega)
    have hf1 := h1.fits_end
    have h2 := ih (parsePost σ p.vars src (flatBits vs ++ rest) s) rest
      (by simp [parsePost, hsrc.1])
      (by simp [parsePost, hcv.1, Ne.symm hsc, hc]) (by simp [parsePost, hjv.1, Ne.symm hsj, hj])
      (fun r hr => by
        have hrp : r ∉ p.vars := fun h => hdis r h r hr rfl
        have hrs : r ≠ src := fun h => hsrc.2 (h ▸ hr)
        simp [parsePost, hrp, hrs]; exact hvars r (Or.inr hr))
      hndq hsrc.2 hcv.2 hjv.2 hf1 (by omega)
    have e : parsePost σ (Pat.varsL ps) src rest (parsePost σ p.vars src (flatBits vs ++ rest) s) =
        parsePost σ (p.vars ++ Pat.varsL ps) src rest s := by
      have := parsePost_trans (σ := σ) hsrc.1 hsrc.2 rest (flatBits vs ++ rest) (s src) s
      rwa [update_eq_self] at this
    rw [e] at h2
    simp only [Pat.varsL, parseL, flatBits, List.length_append, Val.bits_length, List.length_cons]
    exact (h1.seq h2).mono (by omega)

/-! ## Templates: building a serialized tree -/

/-- Tree templates over register contents. -/
inductive Tm (R : ℕ) where
  | reg (r : Fin R)
  | nil
  | cons (a b : Tm R)

namespace Tm

def regs : Tm R → List (Fin R)
  | .reg r => [r]
  | .nil => []
  | .cons a b => a.regs ++ b.regs

def eval (σ : Fin R → Val) : Tm R → Val
  | .reg r => σ r
  | .nil => .nil
  | .cons a b => .cons (a.eval σ) (b.eval σ)

def nodes : Tm R → ℕ
  | .reg _ => 1
  | .nil => 1
  | .cons a b => 1 + a.nodes + b.nodes

/-- A constant tree as a template. -/
def ofVal : Val → Tm R
  | .nil => .nil
  | .cons a b => .cons (ofVal a) (ofVal b)

theorem eval_ofVal (σ : Fin R → Val) (v : Val) : (ofVal v : Tm R).eval σ = v := by
  induction v with
  | nil => rfl
  | cons a b iha ihb => simp [ofVal, eval, iha, ihb]

theorem regs_ofVal (v : Val) : (ofVal v : Tm R).regs = [] := by
  induction v with
  | nil => rfl
  | cons a b iha ihb => simp [ofVal, regs, iha, ihb]

theorem nodes_ofVal (v : Val) : (ofVal v : Tm R).nodes = v.size := by
  induction v with
  | nil => rfl
  | cons a b iha ihb => simp [ofVal, nodes, iha, ihb]

end Tm

/-- Append the serialization of a template to `dst`. -/
def emitS (dst : Fin R) : Tm R → Stmt (Instr R)
  | .reg r => .prim (.append dst r)
  | .nil => .prim (.pushBack dst false)
  | .cons a b => .seq (.prim (.pushBack dst true)) (.seq (emitS dst a) (emitS dst b))

theorem emit_run {dst : Fin R} {σ : Fin R → Val} (t : Tm R) :
    ∀ (s : Regs R) (d : List Bool), s dst = d → dst ∉ t.regs →
      (∀ r ∈ t.regs, s r = (σ r).bits) → Fits B s → d.length + (t.eval σ).size ≤ B →
      Runs B (emitS dst t) s (update s dst (d ++ (t.eval σ).bits)) t.nodes := by
  induction t with
  | reg r =>
    intro s d hd hdst hregs hfit hB
    simp only [Tm.regs, List.mem_singleton, forall_eq] at hdst hregs
    exact Runs.append hfit hdst hd hregs (by simpa [Tm.eval] using hB)
  | nil =>
    intro s d hd _ _ hfit hB
    exact Runs.pushBack false hfit hd (by simpa [Tm.eval] using hB)
  | cons a b iha ihb =>
    intro s d hd hdst hregs hfit hB
    simp only [Tm.regs, List.mem_append, not_or] at hdst hregs
    simp only [Tm.eval, Val.size_cons] at hB
    have h1 := Runs.pushBack true hfit hd (by omega)
    have hf1 := h1.fits_end
    have h2 := iha (update s dst (d ++ [true])) (d ++ [true]) (by simp) hdst.1
      (fun r hr => by
        rw [update_of_ne (show r ≠ dst from fun h => hdst.1 (h ▸ hr))]
        exact hregs r (Or.inl hr))
      hf1 (by simp; omega)
    rw [update_idem] at h2
    have hf2 := h2.fits_end
    have h3 := ihb (update s dst (d ++ [true] ++ (a.eval σ).bits)) (d ++ [true] ++ (a.eval σ).bits)
      (update_self _ _ _) hdst.2
      (fun r hr => by
        rw [update_of_ne (show r ≠ dst from fun h => hdst.2 (h ▸ hr))]
        exact hregs r (Or.inr hr))
      hf2 (by simp; omega)
    rw [update_idem] at h3
    have e : d ++ ((Tm.cons a b).eval σ).bits =
        d ++ [true] ++ (a.eval σ).bits ++ (b.eval σ).bits := by
      simp [Tm.eval, Val.bits]
    rw [e]
    simp only [emitS, Tm.nodes]
    exact (h1.seq (h2.seq h3)).mono (by omega)

/-! ## Clearing registers -/

def clearL : List (Fin R) → Stmt (Instr R)
  | [] => nop
  | r :: rs => .seq (.prim (.clear r)) (clearL rs)

theorem clearL_run (l : List (Fin R)) :
    ∀ s : Regs R, Fits B s →
      Runs B (clearL l) s (fun r => if r ∈ l then [] else s r) (l.length + 1) := by
  induction l with
  | nil =>
    intro s hs
    have e : (fun r => if r ∈ ([] : List (Fin R)) then ([] : List Bool) else s r) = s := by
      funext r; simp
    rw [e]
    exact Runs.nop hs
  | cons r rs ih =>
    intro s hs
    have h1 := Runs.clear hs r
    have h2 := ih _ h1.fits_end
    have e : (fun q => if q ∈ rs then [] else update s r [] q) =
        (fun q => if q ∈ r :: rs then [] else s q) := by
      funext q
      by_cases h : q = r
      · subst h; simp
      · simp [h]
    rw [e] at h2
    simp only [clearL, List.length_cons]
    exact (h1.seq h2).mono (by omega)

/-! ## Dispatch on a fixed bit prefix -/

/-- Binary tries over the front bits of a register. -/
inductive Trie (R : ℕ) where
  | leaf (st : Stmt (Instr R))
  | pop (t : Trie R)
  | br (f t : Trie R)
  | fail

/-- `pop`: drop one bit; `br f t`: drop one bit and continue in `f` (bit `false`) or `t`. -/
def Trie.code (src : Fin R) : Trie R → Stmt (Instr R)
  | .leaf st => st
  | .pop t => .seq (.prim (.popFront src)) (t.code src)
  | .br f t => .ite (.headIs src false) (.seq (.prim (.popFront src)) (f.code src))
      (.seq (.prim (.popFront src)) (t.code src))
  | .fail => nop

/-- The leaf reached along a bit path. -/
def Trie.walk : Trie R → List Bool → Option (Stmt (Instr R))
  | .leaf st, [] => some st
  | .pop t, _ :: bs => t.walk bs
  | .br f _, false :: bs => f.walk bs
  | .br _ t, true :: bs => t.walk bs
  | _, _ => none

theorem trie_run {src : Fin R} (path : List Bool) :
    ∀ (T : Trie R) (st : Stmt (Instr R)) (s t : Regs R) (rest : List Bool) (n : ℕ),
      T.walk path = some st → s src = path ++ rest → Fits B s →
      Runs B st (update s src rest) t n → Runs B (T.code src) s t (n + 3 * path.length) := by
  induction path with
  | nil =>
    intro T st s t rest n hw hs hfit hrun
    cases T with
    | leaf st' =>
      simp only [Trie.walk, Option.some.injEq] at hw
      subst hw
      simp only [List.nil_append] at hs
      rw [← hs, update_eq_self] at hrun
      simpa [Trie.code] using hrun
    | pop _ => simp [Trie.walk] at hw
    | br _ _ => simp [Trie.walk] at hw
    | fail => simp [Trie.walk] at hw
  | cons b bs ih =>
    intro T st s t rest n hw hs hfit hrun
    simp only [List.cons_append] at hs
    have h1 := Runs.popFront hfit hs
    have hf1 := h1.fits_end
    have hrun' : Runs B st (update (update s src (bs ++ rest)) src rest) t n := by
      rwa [update_idem]
    cases T with
    | leaf _ => simp [Trie.walk] at hw
    | fail => simp [Trie.walk] at hw
    | pop T' =>
      simp only [Trie.walk] at hw
      have := ih T' st _ t rest n hw (by simp) hf1 hrun'
      simp only [Trie.code, List.length_cons]
      exact (h1.seq this).mono (by omega)
    | br F T' =>
      cases b with
      | false =>
        simp only [Trie.walk] at hw
        have := ih F st _ t rest n hw (by simp) hf1 hrun'
        simp only [Trie.code, List.length_cons]
        exact (Runs.iteT (tp := .headIs src false) hfit trivial (by simp [Instr.eval, hs])
          (h1.seq this)).mono (by omega)
      | true =>
        simp only [Trie.walk] at hw
        have := ih T' st _ t rest n hw (by simp) hf1 hrun'
        simp only [Trie.code, List.length_cons]
        exact (Runs.iteF (tp := .headIs src false) hfit trivial (by simp [Instr.eval, hs])
          (h1.seq this)).mono (by omega)

/-- Dispatch on a unary tag `unary j`: leaf `j` of the list. -/
def tagTrie : List (Stmt (Instr R)) → Trie R
  | [] => .fail
  | l :: ls => .br (.leaf l) (.pop (tagTrie ls))

theorem unary_bits_succ (j : ℕ) :
    (Enc.unary (j + 1)).bits = true :: false :: (Enc.unary j).bits := rfl

theorem tagTrie_walk : ∀ (ls : List (Stmt (Instr R))) (j : ℕ),
    (tagTrie ls).walk (Enc.unary j).bits = ls[j]?
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: ls, j + 1 => by
    rw [unary_bits_succ]
    exact tagTrie_walk ls j

/-! ## Indexing an encoded list -/

/-- One step of `nthS`: drop one digit of the unary index `I` and the first element of `L`. -/
def nthBody (L I c j : Fin R) : Stmt (Instr R) :=
  .seq (.prim (.popFront I)) (.seq (.prim (.popFront I)) (.seq (.prim (.popFront L))
    (.seq (moveTree j L c) (.prim (.clear j)))))

def nthLoop (L I c j : Fin R) : Stmt (Instr R) := .loop (.headIs I true) true (nthBody L I c j)

/-- `W := L[I]` for an encoded list `L` (`Enc.list id`) and a unary index `I`; `L` and `I` are
consumed (left with garbage). -/
def nthS (L I W c j : Fin R) : Stmt (Instr R) :=
  .seq (nthLoop L I c j) (.seq (.prim (.popFront L)) (moveTree W L c))

theorem size_lt_of_getElem? : ∀ (vs : List Val) (i : ℕ) (w : Val), vs[i]? = some w →
    w.size < (Enc.list id vs).size
  | [], _, _, h => by simp at h
  | v :: vs, 0, w, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [Enc.list]; omega
  | v :: vs, i + 1, w, h => by
    simp only [List.getElem?_cons_succ] at h
    have := size_lt_of_getElem? vs i w h
    simp [Enc.list]; omega

theorem nthLoop_run {L I c j : Fin R} (hLI : L ≠ I) (hLc : L ≠ c) (hLj : L ≠ j) (hIc : I ≠ c)
    (hIj : I ≠ j) (hcj : c ≠ j) (i : ℕ) :
    ∀ (vs : List Val) (w : Val) (s : Regs R), vs[i]? = some w → s I = (Enc.unary i).bits →
      s L = (Enc.list id vs).bits → s c = [] → s j = [] → Fits B s →
      (Enc.list id vs).size + 1 ≤ B →
      ∃ t rest, Runs B (nthLoop L I c j) s t (7 * ((Enc.list id vs).size + (Enc.unary i).size)) ∧
        t L = true :: (w.bits ++ rest) ∧ ∀ r, r ≠ L → r ≠ I → t r = s r := by
  induction i with
  | zero =>
    intro vs w s hw hI hL _ _ hfit _
    cases vs with
    | nil => simp at hw
    | cons v vs =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
      subst hw
      refine ⟨s, (Enc.list id vs).bits, ?_, ?_, fun _ _ _ => rfl⟩
      · have := Runs.loopF (tp := .headIs I true) (pol := true) (c := false)
          (body := nthBody L I c j) hfit trivial (by simp [Instr.eval, hI, Enc.unary, Val.bits])
          (by decide)
        exact this.mono (by simp [Enc.list]; omega)
      · simp [hL, Enc.list, Val.bits]
  | succ i ih =>
    intro vs w s hw hI hL hc hj hfit hB
    cases vs with
    | nil => simp at hw
    | cons h vs =>
      simp only [List.getElem?_cons_succ] at hw
      have hhs : h.size + (Enc.list id vs).size + 1 = (Enc.list id (h :: vs)).size := by
        simp [Enc.list]; omega
      rw [unary_bits_succ] at hI
      have h1 := Runs.popFront hfit hI
      have h2 := Runs.popFront h1.fits_end
        (show update s I (false :: (Enc.unary i).bits) I = false :: (Enc.unary i).bits by simp)
      rw [update_idem] at h2
      have hL2 : update s I (Enc.unary i).bits L = true :: (h.bits ++ (Enc.list id vs).bits) := by
        rw [update_of_ne hLI, hL]; simp [Enc.list, Val.bits]
      have h3 := Runs.popFront h2.fits_end hL2
      set s3 := update (update s I (Enc.unary i).bits) L (h.bits ++ (Enc.list id vs).bits)
        with hs3
      have h4 := moveTree_run (B := B) (dst := j) (src := L) (c := c) (Ne.symm hLj) (Ne.symm hcj)
        hLc (v := h) (rest := (Enc.list id vs).bits) (d := [])
        (by rw [hs3, update_self]) (by rw [hs3, update_of_ne (Ne.symm hLc),
          update_of_ne (Ne.symm hIc), hc])
        (by rw [hs3, update_of_ne (Ne.symm hLj), update_of_ne (Ne.symm hIj), hj])
        h3.fits_end (by simp; omega) (by omega)
      have h5 := Runs.clear h4.fits_end j
      set s5 := update (upd3 s3 j ([] ++ h.bits) c [] L (Enc.list id vs).bits) j [] with hs5
      have hs5I : s5 I = (Enc.unary i).bits := by
        simp [hs5, upd3, hs3, hIj, hIc, Ne.symm hLI]
      have hs5L : s5 L = (Enc.list id vs).bits := by simp [hs5, upd3, hLj]
      have hs5c : s5 c = [] := by simp [hs5, upd3, hcj, Ne.symm hLc]
      have hs5j : s5 j = [] := by simp [hs5]
      have hs5r : ∀ r, r ≠ L → r ≠ I → s5 r = s r := by
        intro r hrL hrI
        by_cases hrj : r = j
        · subst hrj; rw [hs5j, hj]
        · by_cases hrc : r = c
          · subst hrc; rw [hs5c, hc]
          · simp [hs5, upd3, hs3, hrj, hrc, hrL, hrI]
      obtain ⟨t, rest, hrun, htL, htr⟩ := ih vs w s5 hw hs5I hs5L hs5c hs5j h5.fits_end
        (by omega)
      refine ⟨t, rest, ?_, htL, fun r hrL hrI => (htr r hrL hrI).trans (hs5r r hrL hrI)⟩
      have hbody : Runs B (nthBody L I c j) s s5 (1 + (1 + (1 + ((5 * h.size + 2) + 1)))) :=
        h1.seq (h2.seq (h3.seq (h4.seq h5)))
      have := Runs.loopT (tp := .headIs I true) (pol := true) hfit trivial
        (by simp [Instr.eval, hI]) hbody hrun
      refine this.mono ?_
      simp only [Enc.unary_size] at *
      omega

theorem nthS_run {L I W c j : Fin R} (hLI : L ≠ I) (hLW : L ≠ W) (hLc : L ≠ c) (hLj : L ≠ j)
    (hIW : I ≠ W) (hIc : I ≠ c) (hIj : I ≠ j) (hWc : W ≠ c) (_hWj : W ≠ j) (hcj : c ≠ j)
    {i : ℕ} {vs : List Val} {w : Val} {s : Regs R} (hw : vs[i]? = some w)
    (hI : s I = (Enc.unary i).bits) (hL : s L = (Enc.list id vs).bits) (hW : s W = [])
    (hc : s c = []) (hj : s j = []) (hfit : Fits B s) (hB : (Enc.list id vs).size + 1 ≤ B) :
    ∃ t, Runs B (nthS L I W c j) s t (12 * ((Enc.list id vs).size + (Enc.unary i).size) + 4) ∧
      t W = w.bits ∧ ∀ r, r ≠ L → r ≠ I → r ≠ W → t r = s r := by
  have hwlt := size_lt_of_getElem? vs i w hw
  obtain ⟨t1, rest, h1, ht1L, ht1r⟩ := nthLoop_run hLI hLc hLj hIc hIj hcj i vs w s hw hI hL hc hj
    hfit hB
  have h2 := Runs.popFront h1.fits_end ht1L
  have ht1c : t1 c = [] := by rw [ht1r c (Ne.symm hLc) (Ne.symm hIc), hc]
  have h3 := moveTree_run (B := B) (dst := W) (src := L) (c := c) (Ne.symm hLW) hWc hLc
    (v := w) (rest := rest) (d := []) (by simp)
    (by rw [update_of_ne (Ne.symm hLc), ht1c])
    (by rw [update_of_ne (Ne.symm hLW), ht1r W (Ne.symm hLW) (Ne.symm hIW), hW])
    h2.fits_end (by simp; omega) (by omega)
  refine ⟨_, (h1.seq (h2.seq h3)).mono ?_, ?_, ?_⟩
  · omega
  · simp [upd3, hWc, Ne.symm hLW]
  · intro r hrL hrI hrW
    by_cases hrc : r = c
    · subst hrc; simp [upd3, hrL, hc]
    · simp [upd3, hrL, hrc, hrW]; exact ht1r r hrL hrI

/-! ## Moving a register back in front of another -/

/-- `S := V ++ S; V := []`. -/
def restoreS (V S : Fin R) : Stmt (Instr R) :=
  .seq (.prim (.append V S)) (.seq (.prim (.clear S)) (.seq (.prim (.append S V))
    (.prim (.clear V))))

theorem restore_run {V S : Fin R} (hVS : V ≠ S) {s : Regs R} {x y : List Bool} (hV : s V = x)
    (hS : s S = y) (hfit : Fits B s) (hl : x.length + y.length ≤ B) :
    Runs B (restoreS V S) s (update (update s V []) S (x ++ y)) 4 := by
  have h1 := Runs.append hfit hVS hV hS hl
  have h2 := Runs.clear h1.fits_end S
  have h3 := Runs.append (x := []) (y := x ++ y) h2.fits_end (Ne.symm hVS) (by simp)
    (by simp [hVS]) (by simpa using hl)
  have h4 := Runs.clear h3.fits_end V
  have e : update (update (update (update s V (x ++ y)) S []) S ([] ++ (x ++ y))) V [] =
      update (update s V []) S (x ++ y) := by
    funext q
    by_cases hqV : q = V
    · subst hqV; simp [hVS]
    · by_cases hqS : q = S
      · subst hqS; simp [hqV]
      · simp [hqV, hqS]
  rw [e] at h4
  exact h1.seq (h2.seq (h3.seq h4))

/-! ## Leaves: parse, compute, emit, clean -/

/-- Parse the sequence `ps` off `S` (which must then be empty), run `mid`, write the template
`tm` into `S`, and clear the registers `clr`. -/
def leafS (S c j : Fin R) (ps : List (Pat R)) (mid : Stmt (Instr R)) (tm : Tm R)
    (clr : List (Fin R)) : Stmt (Instr R) :=
  .seq (parseL S c j ps) (.seq mid (.seq (emitS S tm) (clearL clr)))

theorem leaf_run {S c j : Fin R} (hSc : S ≠ c) (hSj : S ≠ j) (hcj : c ≠ j)
    {ps : List (Pat R)} {mid : Stmt (Instr R)} {tm : Tm R} {clr : List (Fin R)}
    {σ σ' : Fin R → Val} {vs : List Val} {out : Val} {nm : ℕ}
    (hm : PMatchL σ ps vs) (hnd : (Pat.varsL ps).Nodup) (hsub : ∀ r ∈ Pat.varsL ps, r ∈ clr)
    (hSclr : S ∉ clr) (hcclr : c ∉ clr) (hjclr : j ∉ clr) (hStm : S ∉ tm.regs)
    (htm : tm.eval σ' = out)
    {s : Regs R} (hfit : Fits B s) (hS : s S = flatBits vs) (hc : s c = []) (hj : s j = [])
    (hclr : ∀ r ∈ clr, s r = [])
    (hB1 : (flatBits vs).length + 1 ≤ B) (hB2 : out.size ≤ B)
    (hmid : ∀ s1 : Regs R, Fits B s1 → s1 S = [] → (∀ r ∈ Pat.varsL ps, s1 r = (σ r).bits) →
      (∀ r, r ∉ Pat.varsL ps → r ≠ S → s1 r = s r) →
      ∃ s2, Runs B mid s1 s2 nm ∧ (∀ r, r ∉ clr → s2 r = s1 r) ∧
        (∀ r ∈ tm.regs, s2 r = (σ' r).bits)) :
    Runs B (leafS S c j ps mid tm clr) s (update s S out.bits)
      (5 * (flatBits vs).length + 3 * ps.length + 1 + nm + tm.nodes + clr.length + 1) := by
  have hSv : S ∉ Pat.varsL ps := fun h => hSclr (hsub S h)
  have hcv : c ∉ Pat.varsL ps := fun h => hcclr (hsub c h)
  have hjv : j ∉ Pat.varsL ps := fun h => hjclr (hsub j h)
  have h1 := parseL_run hSc hSj hcj hm s [] (by simp [hS]) hc hj
    (fun r hr => hclr r (hsub r hr)) hnd hSv hcv hjv hfit hB1
  set s1 := parsePost σ (Pat.varsL ps) S [] s with hs1
  obtain ⟨s2, h2, hs2r, hs2t⟩ := hmid s1 h1.fits_end (by simp [hs1, parsePost, hSv])
    (fun r hr => by simp [hs1, parsePost, hr])
    (fun r hr hrS => by simp [hs1, parsePost, hr, hrS])
  have hs2S : s2 S = [] := by rw [hs2r S hSclr]; simp [hs1, parsePost, hSv]
  have h3 := emit_run (σ := σ') tm s2 [] hs2S hStm hs2t h2.fits_end (by simp [htm, hB2])
  rw [htm] at h3
  have h4 := clearL_run clr _ h3.fits_end
  have e : (fun r => if r ∈ clr then [] else update s2 S ([] ++ out.bits) r) =
      update s S out.bits := by
    funext r
    by_cases hr : r ∈ clr
    · have hrS : r ≠ S := fun h => hSclr (h ▸ hr)
      simp [hr, hrS, hclr r hr]
    · by_cases hrS : r = S
      · subst hrS; simp [hr]
      · have hrv : r ∉ Pat.varsL ps := fun h => hr (hsub r h)
        simp [hr, hrS, hs2r r hr, hs1, parsePost, hrv]
  rw [e] at h4
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by omega)

/-- Leaves without a middle computation. -/
theorem leaf_run_nop {S c j : Fin R} (hSc : S ≠ c) (hSj : S ≠ j) (hcj : c ≠ j)
    {ps : List (Pat R)} {tm : Tm R} {clr : List (Fin R)} {σ : Fin R → Val} {vs : List Val}
    {out : Val} (hm : PMatchL σ ps vs) (hnd : (Pat.varsL ps).Nodup)
    (hsub : ∀ r ∈ Pat.varsL ps, r ∈ clr) (htreg : ∀ r ∈ tm.regs, r ∈ Pat.varsL ps)
    (hSclr : S ∉ clr) (hcclr : c ∉ clr) (hjclr : j ∉ clr) (htm : tm.eval σ = out)
    {s : Regs R} (hfit : Fits B s) (hS : s S = flatBits vs) (hc : s c = []) (hj : s j = [])
    (hclr : ∀ r ∈ clr, s r = [])
    (hB1 : (flatBits vs).length + 1 ≤ B) (hB2 : out.size ≤ B) :
    Runs B (leafS S c j ps nop tm clr) s (update s S out.bits)
      (5 * (flatBits vs).length + 3 * ps.length + 1 + 1 + tm.nodes + clr.length + 1) := by
  have hStm : S ∉ tm.regs := fun h => hSclr (hsub S (htreg S h))
  exact leaf_run hSc hSj hcj hm hnd hsub hSclr hcclr hjclr hStm htm hfit hS hc hj hclr hB1 hB2
    (fun s1 hf1 _ hv _ => ⟨s1, Runs.nop hf1, fun _ _ => rfl, fun r hr => hv r (htreg r hr)⟩)

end QecReliability.Interp
