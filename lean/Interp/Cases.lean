import Interp.Step

/-!
# Correctness of `stepS`, case by case

`stepS_run`: whenever `FL.step P st = some st'`, the program `stepS` (with `Program.enc P` in
`rP` and all scratch registers empty) turns `rS = st.enc.bits` into `rS = st'.enc.bits`,
leaving every other register unchanged, with at most `stepBound |st.enc| |Program.enc P|`
primitives, inside `Fits B` for `B ≥ |st.enc| + |Program.enc P| + 2` and `B > |st'.enc|`.

Each case of `FL.step` is a lemma `run_*`: dispatch (`eval_case` / `ret_case`) plus one
instance of the generic leaf lemma (`leaf_nop_run`, or `leaf_run` with `nthS` for variables and
calls).
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

/-- Primitive budget of one step on a state of size `a` with an encoded program of size `p`. -/
def stepBound (a p : ℕ) : ℕ := 40 * (a + p) + 200

/-- Finite valuations of the pattern variables. -/
def asg (l : List (Fin 16 × Val)) (r : Fin 16) : Val := (l.lookup r).getD .nil

/-- Decidable side conditions of a leaf without middle computation. -/
def LeafOK (ps : List (Pat 16)) (tm : Tm 16) (clr : List (Fin 16)) : Prop :=
  (Pat.varsL ps).Nodup ∧ (∀ r ∈ Pat.varsL ps, r ∈ clr) ∧ (∀ r ∈ tm.regs, r ∈ Pat.varsL ps) ∧
    (∀ r ∈ clr, 7 ≤ r.val) ∧ tm.nodes + clr.length + 3 * ps.length ≤ 60

instance (ps : List (Pat 16)) (tm : Tm 16) (clr : List (Fin 16)) :
    Decidable (LeafOK ps tm clr) := by
  unfold LeafOK; infer_instance

theorem clean_ne {s : Regs 16} (hc : Clean s) {X : List Bool} {r : Fin 16} (hr : 4 ≤ r.val) :
    update s rS X r = [] := by
  rw [update_of_ne (by intro e; subst e; simp at hr)]
  exact hc r hr

/-! ## Generic leaves -/

theorem leaf_nop_run {ps : List (Pat 16)} {tm : Tm 16} {clr : List (Fin 16)}
    {σ : Fin 16 → Val} {vs : List Val} {out : Val}
    (hm : PMatchL σ ps vs) (hok : LeafOK ps tm clr) (htm : tm.eval σ = out)
    {s : Regs 16} (hc : Clean s) (hfit : Fits B s) (hB1 : (flatBits vs).length + 1 ≤ B)
    (hB2 : out.size ≤ B) :
    Runs B (leaf ps nop tm clr) (update s rS (flatBits vs)) (update s rS out.bits)
      (5 * (flatBits vs).length + 63) := by
  obtain ⟨hnd, hsub, htreg, hclr7, hsz⟩ := hok
  have hnot : ∀ r : Fin 16, r.val < 7 → r ∉ clr := fun r hr hm => by
    have := hclr7 r hm; omega
  have := leaf_run_nop (B := B) (S := rS) (c := rC) (j := rJ) (by decide) (by decide) (by decide)
    hm hnd hsub htreg (hnot _ (by decide)) (hnot _ (by decide)) (hnot _ (by decide)) htm
    (s := update s rS (flatBits vs)) (fits_upd hfit (by omega)) (by simp)
    (clean_ne hc (by decide)) (clean_ne hc (by decide))
    (fun r hr => clean_ne hc (by have := hclr7 r hr; omega)) hB1 hB2
  rw [update_idem] at this
  exact this.mono (by omega)

theorem rleaf_of_leaf {ps : List (Pat 16)} {mid : Stmt (Instr 16)} {tm : Tm 16}
    {clr : List (Fin 16)} {x y : List Bool} {s t : Regs 16} {n : ℕ} (hV : s rV = [])
    (hfit : Fits B s) (hl : x.length + y.length ≤ B)
    (h : Runs B (leaf ps mid tm clr) (update s rS (x ++ y)) t n) :
    Runs B (rleaf ps mid tm clr) (update (update s rV x) rS y) t (n + 4) := by
  have hf0 : Fits B (update (update s rV x) rS y) :=
    fits_upd (fits_upd hfit (by omega)) (by omega)
  have h0 := restore_run (B := B) (V := rV) (S := rS) (by decide) (x := x) (y := y)
    (by simp) (by simp) hf0 hl
  have e : update (update (update (update s rV x) rS y) rV []) rS (x ++ y) =
      update s rS (x ++ y) := by
    funext q
    by_cases hq1 : q = rS
    · subst hq1; simp
    · by_cases hq2 : q = rV
      · subst hq2; simp [hV]
      · simp [hq1, hq2]
  rw [e] at h0
  exact (h0.seq h).mono (by omega)

theorem rleaf_nop_run {ps : List (Pat 16)} {tm : Tm 16} {clr : List (Fin 16)}
    {σ : Fin 16 → Val} {v pay Kv out : Val}
    (hm : PMatchL σ ps [v, pay, Kv]) (hok : LeafOK ps tm clr) (htm : tm.eval σ = out)
    {s : Regs 16} (hc : Clean s) (hfit : Fits B s) (hB1 : (flatBits [v, pay, Kv]).length + 1 ≤ B)
    (hB2 : out.size ≤ B) :
    Runs B (rleaf ps nop tm clr) (update (update s rV v.bits) rS (pay.bits ++ Kv.bits))
      (update s rS out.bits) (5 * (flatBits [v, pay, Kv]).length + 67) := by
  have e : flatBits [v, pay, Kv] = v.bits ++ (pay.bits ++ Kv.bits) := by simp [flatBits]
  have hl := leaf_nop_run hm hok htm hc hfit hB1 hB2
  rw [e] at hl hB1 ⊢
  exact rleaf_of_leaf (hc rV (by decide)) hfit (by simp at hB1 ⊢; omega) hl

theorem ite_nil {a b : Stmt (Instr 16)} {s t : Regs 16} {n : ℕ} (hfit : Fits B s)
    (hV : s rV = Val.nil.bits) (h : Runs B a s t n) :
    Runs B (.ite (.headIs rV false) a b) s t (n + 1) :=
  Runs.iteT hfit trivial (by simp [Instr.eval, hV, Val.bits]) h

theorem ite_cons {a b : Stmt (Instr 16)} {s t : Regs 16} {n : ℕ} {x y : Val} (hfit : Fits B s)
    (hV : s rV = (Val.cons x y).bits) (h : Runs B b s t n) :
    Runs B (.ite (.headIs rV false) a b) s t (n + 1) :=
  Runs.iteF hfit trivial (by simp [Instr.eval, hV, Val.bits]) h

/-! ## Dispatch with budgets -/

theorem eval_case {j : ℕ} {st : Stmt (Instr 16)} (hj : evLeaves[j]? = some st)
    {pay E Kv out : Val} {Psz extra : ℕ} {s : Regs 16} (hfit : Fits B s)
    (hS : s rS = (Val.cons .nil (.cons (.cons (Enc.unary j) pay) (.cons E Kv))).bits)
    (hB1 : (Val.cons .nil (.cons (.cons (Enc.unary j) pay) (.cons E Kv))).size + 1 ≤ B)
    (hj8 : j ≤ 8)
    (hextra : extra ≤ 12 * ((Val.cons .nil (.cons (.cons (Enc.unary j) pay) (.cons E Kv))).size
      + Psz) + 20)
    (h : (flatBits [pay, .cons E Kv]).length + 1 ≤ B →
      Runs B st (update s rS (flatBits [pay, .cons E Kv])) (update s rS out.bits)
        (5 * (flatBits [pay, .cons E Kv]).length + 63 + extra)) :
    Runs B stepS s (update s rS out.bits)
      (stepBound (Val.cons .nil (.cons (.cons (Enc.unary j) pay) (.cons E Kv))).size Psz) := by
  have hsz := eval_size j pay E Kv
  have := eval_dispatch hj hfit hS (h (by omega))
  exact this.mono (by unfold stepBound; omega)

theorem ret_case {j : ℕ} {st : Stmt (Instr 16)} (hj : frLeaves[j]? = some st)
    {v pay Kv out : Val} {Psz extra : ℕ} {s : Regs 16} (hfit : Fits B s) (hc : Clean s)
    (hS : s rS = (Val.cons (Enc.unary 1) (.cons v (.cons (.cons (Enc.unary j) pay) Kv))).bits)
    (hB1 : (Val.cons (Enc.unary 1) (.cons v (.cons (.cons (Enc.unary j) pay) Kv))).size + 1 ≤ B)
    (hj7 : j ≤ 7)
    (hextra : extra ≤ 12 * ((Val.cons (Enc.unary 1) (.cons v (.cons (.cons (Enc.unary j) pay)
      Kv))).size + Psz) + 20)
    (h : (flatBits [v, pay, Kv]).length + 1 ≤ B →
      Runs B st (update (update s rV v.bits) rS (pay.bits ++ Kv.bits)) (update s rS out.bits)
        (5 * (flatBits [v, pay, Kv]).length + 67 + extra)) :
    Runs B stepS s (update s rS out.bits)
      (stepBound (Val.cons (Enc.unary 1) (.cons v (.cons (.cons (Enc.unary j) pay) Kv))).size
        Psz) := by
  have hsz := ret_size j v pay Kv
  have hv : v.size ≤ (flatBits [v, pay, Kv]).length := by simp [flatBits]
  have := ret_dispatch hj hfit hS (hc rV (by decide)) (hc rC (by decide)) (by omega) (h (by omega))
  exact this.mono (by unfold stepBound; omega)

/-! ## Eval mode -/

section Eval
variable {Psz : ℕ} {env : List Val} {k : List Frame} {s : Regs 16}

theorem run_var {i : ℕ} {w : Val} (hw : env[i]? = some w) (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.eval (.var i) env k).enc.bits)
    (hB1 : (State.eval (.var i) env k).enc.size + 1 ≤ B) (hB2 : (State.ret w k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.ret w k).enc.bits)
      (stepBound (State.eval (.var i) env k).enc.size Psz) := by
  have hEL : (envEnc env).size = (Enc.list id env).size := rfl
  refine eval_case (j := 0) (pay := Enc.unary i) (E := envEnc env) (Kv := stackEnc k)
    (extra := 12 * ((envEnc env).size + (Enc.unary i).size) + 4) rfl hfit hS hB1 (by decide)
    ?_ (fun hB => ?_)
  · simp only [Val.size_cons, Val.size_nil, Enc.unary_size] at hEL ⊢; omega
  have hflat : (flatBits [Enc.unary i, Val.cons (envEnc env) (stackEnc k)]).length =
      (Enc.unary i).size + (1 + (envEnc env).size + (stackEnc k).size) := by
    simp [flatBits]
  have := leaf_run (B := B) (S := rS) (c := rC) (j := rJ) (by decide) (by decide) (by decide)
    (ps := [.var rI, .cons (.var rL) (.var rK)]) (mid := nthS rL rI rW rC rJ)
    (tm := tRt (.reg rW) (.reg rK)) (clr := [rI, rL, rK, rW])
    (σ := asg [(rI, Enc.unary i), (rL, envEnc env), (rK, stackEnc k)])
    (σ' := asg [(rW, w), (rK, stackEnc k)])
    (vs := [Enc.unary i, .cons (envEnc env) (stackEnc k)]) (out := (State.ret w k).enc)
    (nm := 12 * ((envEnc env).size + (Enc.unary i).size) + 4)
    (.cons (.var rfl) (.cons (.cons (.var rfl) (.var rfl)) .nil)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) rfl
    (s := update s rS (flatBits [Enc.unary i, .cons (envEnc env) (stackEnc k)]))
    (fits_upd hfit (by omega)) (by simp) (clean_ne hc (by decide)) (clean_ne hc (by decide))
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact clean_ne hc (by decide))
    hB hB2
    (fun s1 hf1 _ hv hrest => by
      obtain ⟨t, ht, htW, htr⟩ := nthS_run (B := B) (L := rL) (I := rI) (W := rW) (c := rC)
        (j := rJ) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (i := i) (vs := env) (w := w) (s := s1)
        hw (hv rI (by decide)) (hv rL (by decide))
        (by rw [hrest rW (by decide) (by decide)]; exact clean_ne hc (by decide))
        (by rw [hrest rC (by decide) (by decide)]; exact clean_ne hc (by decide))
        (by rw [hrest rJ (by decide) (by decide)]; exact clean_ne hc (by decide))
        hf1 (by rw [← hEL]; omega)
      refine ⟨t, ht, fun r hr => ?_, fun r hr => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact htr r hr.2.1 hr.1 hr.2.2.2
      · simp only [tRt, tU, Tm.regs, List.nil_append, List.mem_append, List.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact htW
        · rw [htr _ (by decide) (by decide) (by decide)]; exact hv rK (by decide))
  rw [update_idem] at this
  refine this.mono ?_
  simp only [tRt, tU, Tm.nodes, List.length_cons, List.length_nil]
  omega

theorem run_nil (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.eval .nil env k).enc.bits)
    (hB1 : (State.eval .nil env k).enc.size + 1 ≤ B) (hB2 : (State.ret .nil k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.ret .nil k).enc.bits)
      (stepBound (State.eval .nil env k).enc.size Psz) :=
  eval_case (j := 1) (pay := .nil) (E := envEnc env) (Kv := stackEnc k) (extra := 0) rfl hfit hS
    hB1 (by decide) (by omega) (fun hB =>
      (leaf_nop_run (ps := [.wild, .cons .wild (.var rK)]) (tm := tRt .nil (.reg rK))
        (clr := [rK]) (σ := asg [(rK, stackEnc k)]) (out := (State.ret .nil k).enc)
        (.cons (.wild _) (.cons (.cons (.wild _) (.var rfl)) .nil)) (by decide) rfl hc hfit hB
        hB2))

theorem run_cons {a b : Expr} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.eval (.cons a b) env k).enc.bits)
    (hB1 : (State.eval (.cons a b) env k).enc.size + 1 ≤ B)
    (hB2 : (State.eval a env (.consL b env :: k)).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval a env (.consL b env :: k)).enc.bits)
      (stepBound (State.eval (.cons a b) env k).enc.size Psz) :=
  eval_case (j := 2) (pay := .cons a.enc b.enc) (E := envEnc env) (Kv := stackEnc k) (extra := 0)
    rfl hfit hS hB1 (by decide) (by omega) (fun hB =>
      (leaf_nop_run (ps := [.cons (.var rX) (.var rY), .cons (.var rL) (.var rK)])
        (tm := tEv (.reg rX) (.reg rL) (.cons (tFr 0 (.cons (.reg rY) (.reg rL))) (.reg rK)))
        (clr := [rX, rY, rL, rK])
        (σ := asg [(rX, a.enc), (rY, b.enc), (rL, envEnc env), (rK, stackEnc k)])
        (out := (State.eval a env (.consL b env :: k)).enc)
        (.cons (.cons (.var rfl) (.var rfl)) (.cons (.cons (.var rfl) (.var rfl)) .nil))
        (by decide) rfl hc hfit hB hB2))

theorem run_case {e e₁ e₂ : Expr} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.eval (.case e e₁ e₂) env k).enc.bits)
    (hB1 : (State.eval (.case e e₁ e₂) env k).enc.size + 1 ≤ B)
    (hB2 : (State.eval e env (.caseK e₁ e₂ env :: k)).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval e env (.caseK e₁ e₂ env :: k)).enc.bits)
      (stepBound (State.eval (.case e e₁ e₂) env k).enc.size Psz) :=
  eval_case (j := 3) (pay := .cons e.enc (.cons e₁.enc e₂.enc)) (E := envEnc env)
    (Kv := stackEnc k) (extra := 0) rfl hfit hS hB1 (by decide) (by omega) (fun hB =>
      (leaf_nop_run (ps := [.cons (.var rX) (.cons (.var rY) (.var rZ)), .cons (.var rL) (.var rK)])
        (tm := tEv (.reg rX) (.reg rL)
          (.cons (tFr 2 (.cons (.reg rY) (.cons (.reg rZ) (.reg rL)))) (.reg rK)))
        (clr := [rX, rY, rZ, rL, rK])
        (σ := asg [(rX, e.enc), (rY, e₁.enc), (rZ, e₂.enc), (rL, envEnc env), (rK, stackEnc k)])
        (out := (State.eval e env (.caseK e₁ e₂ env :: k)).enc)
        (.cons (.cons (.var rfl) (.cons (.var rfl) (.var rfl)))
          (.cons (.cons (.var rfl) (.var rfl)) .nil))
        (by decide) rfl hc hfit hB hB2))

theorem run_call {f : ℕ} {a : Expr} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.eval (.call f a) env k).enc.bits)
    (hB1 : (State.eval (.call f a) env k).enc.size + 1 ≤ B)
    (hB2 : (State.eval a env (.callK f :: k)).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval a env (.callK f :: k)).enc.bits)
      (stepBound (State.eval (.call f a) env k).enc.size Psz) :=
  eval_case (j := 4) (pay := .cons (Enc.unary f) a.enc) (E := envEnc env) (Kv := stackEnc k)
    (extra := 0) rfl hfit hS hB1 (by decide) (by omega) (fun hB =>
      (leaf_nop_run (ps := [.cons (.var rX) (.var rY), .cons (.var rL) (.var rK)])
        (tm := tEv (.reg rY) (.reg rL) (.cons (tFr 3 (.reg rX)) (.reg rK)))
        (clr := [rX, rY, rL, rK])
        (σ := asg [(rX, Enc.unary f), (rY, a.enc), (rL, envEnc env), (rK, stackEnc k)])
        (out := (State.eval a env (.callK f :: k)).enc)
        (.cons (.cons (.var rfl) (.var rfl)) (.cons (.cons (.var rfl) (.var rfl)) .nil))
        (by decide) rfl hc hfit hB hB2))

theorem run_letE {a b : Expr} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.eval (.letE a b) env k).enc.bits)
    (hB1 : (State.eval (.letE a b) env k).enc.size + 1 ≤ B)
    (hB2 : (State.eval a env (.letK b env :: k)).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval a env (.letK b env :: k)).enc.bits)
      (stepBound (State.eval (.letE a b) env k).enc.size Psz) :=
  eval_case (j := 5) (pay := .cons a.enc b.enc) (E := envEnc env) (Kv := stackEnc k) (extra := 0)
    rfl hfit hS hB1 (by decide) (by omega) (fun hB =>
      (leaf_nop_run (ps := [.cons (.var rX) (.var rY), .cons (.var rL) (.var rK)])
        (tm := tEv (.reg rX) (.reg rL) (.cons (tFr 4 (.cons (.reg rY) (.reg rL))) (.reg rK)))
        (clr := [rX, rY, rL, rK])
        (σ := asg [(rX, a.enc), (rY, b.enc), (rL, envEnc env), (rK, stackEnc k)])
        (out := (State.eval a env (.letK b env :: k)).enc)
        (.cons (.cons (.var rfl) (.var rfl)) (.cons (.cons (.var rfl) (.var rfl)) .nil))
        (by decide) rfl hc hfit hB hB2))

theorem run_cond {e e₁ e₂ : Expr} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.eval (.cond e e₁ e₂) env k).enc.bits)
    (hB1 : (State.eval (.cond e e₁ e₂) env k).enc.size + 1 ≤ B)
    (hB2 : (State.eval e env (.condK e₁ e₂ env :: k)).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval e env (.condK e₁ e₂ env :: k)).enc.bits)
      (stepBound (State.eval (.cond e e₁ e₂) env k).enc.size Psz) :=
  eval_case (j := 6) (pay := .cons e.enc (.cons e₁.enc e₂.enc)) (E := envEnc env)
    (Kv := stackEnc k) (extra := 0) rfl hfit hS hB1 (by decide) (by omega) (fun hB =>
      (leaf_nop_run (ps := [.cons (.var rX) (.cons (.var rY) (.var rZ)), .cons (.var rL) (.var rK)])
        (tm := tEv (.reg rX) (.reg rL)
          (.cons (tFr 5 (.cons (.reg rY) (.cons (.reg rZ) (.reg rL)))) (.reg rK)))
        (clr := [rX, rY, rZ, rL, rK])
        (σ := asg [(rX, e.enc), (rY, e₁.enc), (rZ, e₂.enc), (rL, envEnc env), (rK, stackEnc k)])
        (out := (State.eval e env (.condK e₁ e₂ env :: k)).enc)
        (.cons (.cons (.var rfl) (.cons (.var rfl) (.var rfl)))
          (.cons (.cons (.var rfl) (.var rfl)) .nil))
        (by decide) rfl hc hfit hB hB2))

theorem run_fst {a : Expr} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.eval (.fst a) env k).enc.bits)
    (hB1 : (State.eval (.fst a) env k).enc.size + 1 ≤ B)
    (hB2 : (State.eval a env (.fstK :: k)).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval a env (.fstK :: k)).enc.bits)
      (stepBound (State.eval (.fst a) env k).enc.size Psz) :=
  eval_case (j := 7) (pay := a.enc) (E := envEnc env) (Kv := stackEnc k) (extra := 0)
    rfl hfit hS hB1 (by decide) (by omega) (fun hB =>
      (leaf_nop_run (ps := [.var rX, .cons (.var rL) (.var rK)])
        (tm := tEv (.reg rX) (.reg rL) (.cons (tFr 6 .nil) (.reg rK)))
        (clr := [rX, rL, rK])
        (σ := asg [(rX, a.enc), (rL, envEnc env), (rK, stackEnc k)])
        (out := (State.eval a env (.fstK :: k)).enc)
        (.cons (.var rfl) (.cons (.cons (.var rfl) (.var rfl)) .nil))
        (by decide) rfl hc hfit hB hB2))

theorem run_snd {a : Expr} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.eval (.snd a) env k).enc.bits)
    (hB1 : (State.eval (.snd a) env k).enc.size + 1 ≤ B)
    (hB2 : (State.eval a env (.sndK :: k)).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval a env (.sndK :: k)).enc.bits)
      (stepBound (State.eval (.snd a) env k).enc.size Psz) :=
  eval_case (j := 8) (pay := a.enc) (E := envEnc env) (Kv := stackEnc k) (extra := 0)
    rfl hfit hS hB1 (by decide) (by omega) (fun hB =>
      (leaf_nop_run (ps := [.var rX, .cons (.var rL) (.var rK)])
        (tm := tEv (.reg rX) (.reg rL) (.cons (tFr 7 .nil) (.reg rK)))
        (clr := [rX, rL, rK])
        (σ := asg [(rX, a.enc), (rL, envEnc env), (rK, stackEnc k)])
        (out := (State.eval a env (.sndK :: k)).enc)
        (.cons (.var rfl) (.cons (.cons (.var rfl) (.var rfl)) .nil))
        (by decide) rfl hc hfit hB hB2))

end Eval

/-! ## Ret mode -/

section Ret
variable {Psz : ℕ} {k : List Frame} {s : Regs 16}

theorem fits_ret {s : Regs 16} (hfit : Fits B s) {v pay Kv : Val}
    (hB : (flatBits [v, pay, Kv]).length + 1 ≤ B) :
    Fits B (update (update s rV v.bits) rS (pay.bits ++ Kv.bits)) := by
  simp only [flatBits, List.length_append, Val.bits_length, List.length_nil] at hB
  exact fits_upd (fits_upd hfit (by simp; omega)) (by simp; omega)

theorem run_consL {v : Val} {b : Expr} {env : List Val} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.ret v (.consL b env :: k)).enc.bits)
    (hB1 : (State.ret v (.consL b env :: k)).enc.size + 1 ≤ B)
    (hB2 : (State.eval b env (.consR v :: k)).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval b env (.consR v :: k)).enc.bits)
      (stepBound (State.ret v (.consL b env :: k)).enc.size Psz) :=
  ret_case (j := 0) (v := v) (pay := .cons b.enc (envEnc env)) (Kv := stackEnc k) (extra := 0)
    rfl hfit hc hS hB1 (by decide) (by omega) (fun hB =>
      rleaf_nop_run (ps := [.var rX, .cons (.var rY) (.var rL), .var rK])
        (tm := tEv (.reg rY) (.reg rL) (.cons (tFr 1 (.reg rX)) (.reg rK)))
        (clr := [rX, rY, rL, rK])
        (σ := asg [(rX, v), (rY, b.enc), (rL, envEnc env), (rK, stackEnc k)])
        (out := (State.eval b env (.consR v :: k)).enc)
        (.cons (.var rfl) (.cons (.cons (.var rfl) (.var rfl)) (.cons (.var rfl) .nil)))
        (by decide) rfl hc hfit hB hB2)

theorem run_consR {v va : Val} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.ret v (.consR va :: k)).enc.bits)
    (hB1 : (State.ret v (.consR va :: k)).enc.size + 1 ≤ B)
    (hB2 : (State.ret (.cons va v) k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.ret (.cons va v) k).enc.bits)
      (stepBound (State.ret v (.consR va :: k)).enc.size Psz) :=
  ret_case (j := 1) (v := v) (pay := va) (Kv := stackEnc k) (extra := 0)
    rfl hfit hc hS hB1 (by decide) (by omega) (fun hB =>
      rleaf_nop_run (ps := [.var rY, .var rX, .var rK])
        (tm := tRt (.cons (.reg rX) (.reg rY)) (.reg rK)) (clr := [rX, rY, rK])
        (σ := asg [(rY, v), (rX, va), (rK, stackEnc k)])
        (out := (State.ret (.cons va v) k).enc)
        (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil)))
        (by decide) rfl hc hfit hB hB2)

theorem run_caseK_nil {e₁ e₂ : Expr} {env : List Val} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.ret .nil (.caseK e₁ e₂ env :: k)).enc.bits)
    (hB1 : (State.ret .nil (.caseK e₁ e₂ env :: k)).enc.size + 1 ≤ B)
    (hB2 : (State.eval e₁ env k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval e₁ env k).enc.bits)
      (stepBound (State.ret .nil (.caseK e₁ e₂ env :: k)).enc.size Psz) :=
  ret_case (j := 2) (v := .nil) (pay := .cons e₁.enc (.cons e₂.enc (envEnc env)))
    (Kv := stackEnc k) (extra := 1) rfl hfit hc hS hB1 (by decide) (by omega) (fun hB =>
      ite_nil (fits_ret hfit hB) (by simp)
        (rleaf_nop_run (ps := [.nil, .cons (.var rX) (.cons .wild (.var rL)), .var rK])
          (tm := tEv (.reg rX) (.reg rL) (.reg rK)) (clr := [rX, rL, rK])
          (σ := asg [(rX, e₁.enc), (rL, envEnc env), (rK, stackEnc k)])
          (out := (State.eval e₁ env k).enc)
          (.cons .nil (.cons (.cons (.var rfl) (.cons (.wild _) (.var rfl))) (.cons (.var rfl) .nil)))
          (by decide) rfl hc hfit hB hB2))

theorem run_caseK_cons {hd tl : Val} {e₁ e₂ : Expr} {env : List Val} (hc : Clean s)
    (hfit : Fits B s)
    (hS : s rS = (State.ret (.cons hd tl) (.caseK e₁ e₂ env :: k)).enc.bits)
    (hB1 : (State.ret (.cons hd tl) (.caseK e₁ e₂ env :: k)).enc.size + 1 ≤ B)
    (hB2 : (State.eval e₂ (hd :: tl :: env) k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval e₂ (hd :: tl :: env) k).enc.bits)
      (stepBound (State.ret (.cons hd tl) (.caseK e₁ e₂ env :: k)).enc.size Psz) :=
  ret_case (j := 2) (v := .cons hd tl) (pay := .cons e₁.enc (.cons e₂.enc (envEnc env)))
    (Kv := stackEnc k) (extra := 1) rfl hfit hc hS hB1 (by decide) (by omega) (fun hB =>
      ite_cons (x := hd) (y := tl) (fits_ret hfit hB) (by simp)
        (rleaf_nop_run
          (ps := [.cons (.var rZ) (.var rU), .cons .wild (.cons (.var rY) (.var rL)), .var rK])
          (tm := tEv (.reg rY) (.cons (.reg rZ) (.cons (.reg rU) (.reg rL))) (.reg rK))
          (clr := [rY, rZ, rU, rL, rK])
          (σ := asg [(rZ, hd), (rU, tl), (rY, e₂.enc), (rL, envEnc env), (rK, stackEnc k)])
          (out := (State.eval e₂ (hd :: tl :: env) k).enc)
          (.cons (.cons (.var rfl) (.var rfl))
            (.cons (.cons (.wild _) (.cons (.var rfl) (.var rfl))) (.cons (.var rfl) .nil)))
          (by decide) rfl hc hfit hB hB2))

theorem run_letK {v : Val} {b : Expr} {env : List Val} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.ret v (.letK b env :: k)).enc.bits)
    (hB1 : (State.ret v (.letK b env :: k)).enc.size + 1 ≤ B)
    (hB2 : (State.eval b (v :: env) k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval b (v :: env) k).enc.bits)
      (stepBound (State.ret v (.letK b env :: k)).enc.size Psz) :=
  ret_case (j := 4) (v := v) (pay := .cons b.enc (envEnc env)) (Kv := stackEnc k) (extra := 0)
    rfl hfit hc hS hB1 (by decide) (by omega) (fun hB =>
      rleaf_nop_run (ps := [.var rX, .cons (.var rY) (.var rL), .var rK])
        (tm := tEv (.reg rY) (.cons (.reg rX) (.reg rL)) (.reg rK))
        (clr := [rX, rY, rL, rK])
        (σ := asg [(rX, v), (rY, b.enc), (rL, envEnc env), (rK, stackEnc k)])
        (out := (State.eval b (v :: env) k).enc)
        (.cons (.var rfl) (.cons (.cons (.var rfl) (.var rfl)) (.cons (.var rfl) .nil)))
        (by decide) rfl hc hfit hB hB2)

theorem run_condK_nil {e₁ e₂ : Expr} {env : List Val} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.ret .nil (.condK e₁ e₂ env :: k)).enc.bits)
    (hB1 : (State.ret .nil (.condK e₁ e₂ env :: k)).enc.size + 1 ≤ B)
    (hB2 : (State.eval e₁ env k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval e₁ env k).enc.bits)
      (stepBound (State.ret .nil (.condK e₁ e₂ env :: k)).enc.size Psz) :=
  ret_case (j := 5) (v := .nil) (pay := .cons e₁.enc (.cons e₂.enc (envEnc env)))
    (Kv := stackEnc k) (extra := 1) rfl hfit hc hS hB1 (by decide) (by omega) (fun hB =>
      ite_nil (fits_ret hfit hB) (by simp)
        (rleaf_nop_run (ps := [.nil, .cons (.var rX) (.cons .wild (.var rL)), .var rK])
          (tm := tEv (.reg rX) (.reg rL) (.reg rK)) (clr := [rX, rL, rK])
          (σ := asg [(rX, e₁.enc), (rL, envEnc env), (rK, stackEnc k)])
          (out := (State.eval e₁ env k).enc)
          (.cons .nil (.cons (.cons (.var rfl) (.cons (.wild _) (.var rfl))) (.cons (.var rfl) .nil)))
          (by decide) rfl hc hfit hB hB2))

theorem run_condK_cons {hd tl : Val} {e₁ e₂ : Expr} {env : List Val} (hc : Clean s)
    (hfit : Fits B s)
    (hS : s rS = (State.ret (.cons hd tl) (.condK e₁ e₂ env :: k)).enc.bits)
    (hB1 : (State.ret (.cons hd tl) (.condK e₁ e₂ env :: k)).enc.size + 1 ≤ B)
    (hB2 : (State.eval e₂ env k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval e₂ env k).enc.bits)
      (stepBound (State.ret (.cons hd tl) (.condK e₁ e₂ env :: k)).enc.size Psz) :=
  ret_case (j := 5) (v := .cons hd tl) (pay := .cons e₁.enc (.cons e₂.enc (envEnc env)))
    (Kv := stackEnc k) (extra := 1) rfl hfit hc hS hB1 (by decide) (by omega) (fun hB =>
      ite_cons (x := hd) (y := tl) (fits_ret hfit hB) (by simp)
        (rleaf_nop_run
          (ps := [.cons .wild .wild, .cons .wild (.cons (.var rY) (.var rL)), .var rK])
          (tm := tEv (.reg rY) (.reg rL) (.reg rK)) (clr := [rY, rL, rK])
          (σ := asg [(rY, e₂.enc), (rL, envEnc env), (rK, stackEnc k)])
          (out := (State.eval e₂ env k).enc)
          (.cons (.cons (.wild _) (.wild _))
            (.cons (.cons (.wild _) (.cons (.var rfl) (.var rfl))) (.cons (.var rfl) .nil)))
          (by decide) rfl hc hfit hB hB2))

theorem run_fstK {a b : Val} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.ret (.cons a b) (.fstK :: k)).enc.bits)
    (hB1 : (State.ret (.cons a b) (.fstK :: k)).enc.size + 1 ≤ B)
    (hB2 : (State.ret a k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.ret a k).enc.bits)
      (stepBound (State.ret (.cons a b) (.fstK :: k)).enc.size Psz) :=
  ret_case (j := 6) (v := .cons a b) (pay := .nil) (Kv := stackEnc k) (extra := 0)
    rfl hfit hc hS hB1 (by decide) (by omega) (fun hB =>
      rleaf_nop_run (ps := [.cons (.var rX) .wild, .nil, .var rK])
        (tm := tRt (.reg rX) (.reg rK)) (clr := [rX, rK])
        (σ := asg [(rX, a), (rK, stackEnc k)]) (out := (State.ret a k).enc)
        (.cons (.cons (.var rfl) (.wild _)) (.cons .nil (.cons (.var rfl) .nil)))
        (by decide) rfl hc hfit hB hB2)

theorem run_sndK {a b : Val} (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.ret (.cons a b) (.sndK :: k)).enc.bits)
    (hB1 : (State.ret (.cons a b) (.sndK :: k)).enc.size + 1 ≤ B)
    (hB2 : (State.ret b k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.ret b k).enc.bits)
      (stepBound (State.ret (.cons a b) (.sndK :: k)).enc.size Psz) :=
  ret_case (j := 7) (v := .cons a b) (pay := .nil) (Kv := stackEnc k) (extra := 0)
    rfl hfit hc hS hB1 (by decide) (by omega) (fun hB =>
      rleaf_nop_run (ps := [.cons .wild (.var rX), .nil, .var rK])
        (tm := tRt (.reg rX) (.reg rK)) (clr := [rX, rK])
        (σ := asg [(rX, b), (rK, stackEnc k)]) (out := (State.ret b k).enc)
        (.cons (.cons (.wild _) (.var rfl)) (.cons .nil (.cons (.var rfl) .nil)))
        (by decide) rfl hc hfit hB hB2)

theorem enc_list_map {α : Type} (f : α → Val) (xs : List α) :
    Enc.list f xs = Enc.list id (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Enc.list, ih]

theorem run_callK {P : Program} {v : Val} {f : ℕ} {body : Expr} (hbody : P[f]? = some body)
    (hc : Clean s) (hfit : Fits B s)
    (hS : s rS = (State.ret v (.callK f :: k)).enc.bits) (hP : s rP = (Program.enc P).bits)
    (hB1 : (State.ret v (.callK f :: k)).enc.size + 1 ≤ B) (hBP : (Program.enc P).size + 1 ≤ B)
    (hB2 : (State.eval body [v] k).enc.size ≤ B) :
    Runs B stepS s (update s rS (State.eval body [v] k).enc.bits)
      (stepBound (State.ret v (.callK f :: k)).enc.size (Program.enc P).size) := by
  have hPv : Program.enc P = Enc.list id (P.map Expr.enc) := enc_list_map _ _
  have hw : (P.map Expr.enc)[f]? = some body.enc := by simp [hbody]
  refine ret_case (j := 3) (v := v) (pay := Enc.unary f) (Kv := stackEnc k)
    (extra := 12 * ((Program.enc P).size + (Enc.unary f).size) + 5) rfl hfit hc hS hB1
    (by decide) ?_ (fun hB => ?_)
  · simp only [Val.size_cons, Enc.unary_size]; omega
  have hflat : (flatBits [v, Enc.unary f, stackEnc k]).length =
      v.size + ((Enc.unary f).size + (stackEnc k).size) := by simp [flatBits]
  have hfl : flatBits [v, Enc.unary f, stackEnc k] = v.bits ++ ((Enc.unary f).bits ++
      (stackEnc k).bits) := by simp [flatBits]
  have := leaf_run (B := B) (S := rS) (c := rC) (j := rJ) (by decide) (by decide) (by decide)
    (ps := [.var rX, .var rI, .var rK])
    (mid := .seq (.prim (.append rL rP)) (nthS rL rI rW rC rJ))
    (tm := tEv (.reg rW) (.cons (.reg rX) .nil) (.reg rK)) (clr := [rX, rI, rK, rL, rW])
    (σ := asg [(rX, v), (rI, Enc.unary f), (rK, stackEnc k)])
    (σ' := asg [(rW, body.enc), (rX, v), (rK, stackEnc k)])
    (vs := [v, Enc.unary f, stackEnc k]) (out := (State.eval body [v] k).enc)
    (nm := 1 + (12 * ((Program.enc P).size + (Enc.unary f).size) + 4))
    (.cons (.var rfl) (.cons (.var rfl) (.cons (.var rfl) .nil))) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) rfl
    (s := update s rS (flatBits [v, Enc.unary f, stackEnc k]))
    (fits_upd hfit (by omega)) (by simp) (clean_ne hc (by decide)) (clean_ne hc (by decide))
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact clean_ne hc (by decide))
    hB hB2
    (fun s1 hf1 _ hv hrest => by
      have hL0 : s1 rL = [] := by
        rw [hrest rL (by decide) (by decide)]; exact clean_ne hc (by decide)
      have hP1 : s1 rP = (Program.enc P).bits := by
        rw [hrest rP (by decide) (by decide), update_of_ne (by decide)]; exact hP
      have h1 := Runs.append (d := rL) (r := rP) hf1 (by decide) hL0 hP1 (by simp; omega)
      obtain ⟨t, ht, htW, htr⟩ := nthS_run (B := B) (L := rL) (I := rI) (W := rW) (c := rC)
        (j := rJ) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (i := f) (vs := P.map Expr.enc)
        (w := body.enc) (s := update s1 rL ([] ++ (Program.enc P).bits))
        hw (by rw [update_of_ne (by decide)]; exact hv rI (by decide))
        (by rw [update_self, List.nil_append, hPv])
        (by rw [update_of_ne (by decide), hrest rW (by decide) (by decide)]
            exact clean_ne hc (by decide))
        (by rw [update_of_ne (by decide), hrest rC (by decide) (by decide)]
            exact clean_ne hc (by decide))
        (by rw [update_of_ne (by decide), hrest rJ (by decide) (by decide)]
            exact clean_ne hc (by decide))
        h1.fits_end (by rw [← hPv]; omega)
      refine ⟨t, h1.seq (ht.mono (le_of_eq (by rw [hPv]))), fun r hr => ?_, fun r hr => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [htr r hr.2.2.2.1 hr.2.1 hr.2.2.2.2, update_of_ne hr.2.2.2.1]
      · simp only [tEv, Tm.regs, List.nil_append, List.mem_append, List.mem_singleton,
          List.append_nil] at hr
        rcases hr with rfl | rfl | rfl
        · exact htW
        · rw [htr _ (by decide) (by decide) (by decide), update_of_ne (by decide)]
          exact hv rX (by decide)
        · rw [htr _ (by decide) (by decide) (by decide), update_of_ne (by decide)]
          exact hv rK (by decide))
  rw [update_idem, hfl] at this
  have := rleaf_of_leaf (hc rV (by decide)) hfit (by simp at hflat ⊢; omega) this
  refine this.mono ?_
  simp only [tEv, Tm.nodes, List.length_cons, List.length_nil, List.length_append,
    Val.bits_length, hflat]
  omega

end Ret

/-! ## The step theorem -/

/-- **One CEK step.** If `FL.step P st = some st'`, `stepS` turns `rS = st.enc.bits` into
`rS = st'.enc.bits` (registers other than `rS` unchanged; scratch registers stay empty), with
at most `stepBound |st.enc| |Program.enc P|` primitives, inside `Fits B`. -/
theorem stepS_run {P : Program} {st st' : State} (h : FL.step P st = some st') {s : Regs 16}
    (hc : Clean s) (hfit : Fits B s) (hS : s rS = st.enc.bits)
    (hP : s rP = (Program.enc P).bits)
    (hB1 : st.enc.size + (Program.enc P).size + 2 ≤ B) (hB2 : st'.enc.size + 1 ≤ B) :
    Runs B stepS s (update s rS st'.enc.bits) (stepBound st.enc.size (Program.enc P).size) := by
  have hB1' : st.enc.size + 1 ≤ B := by omega
  have hB2' : st'.enc.size ≤ B := by omega
  have hBP : (Program.enc P).size + 1 ≤ B := by omega
  rcases st with ⟨e, env, k⟩ | ⟨v, k⟩
  · cases e with
    | var i =>
      simp only [FL.step, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact run_var hw hc hfit hS hB1' hB2'
    | nil =>
      simp only [FL.step, Option.some.injEq] at h; subst h
      exact run_nil hc hfit hS hB1' hB2'
    | cons a b =>
      simp only [FL.step, Option.some.injEq] at h; subst h
      exact run_cons hc hfit hS hB1' hB2'
    | case e e₁ e₂ =>
      simp only [FL.step, Option.some.injEq] at h; subst h
      exact run_case hc hfit hS hB1' hB2'
    | call f a =>
      simp only [FL.step, Option.some.injEq] at h; subst h
      exact run_call hc hfit hS hB1' hB2'
    | letE a b =>
      simp only [FL.step, Option.some.injEq] at h; subst h
      exact run_letE hc hfit hS hB1' hB2'
    | cond e e₁ e₂ =>
      simp only [FL.step, Option.some.injEq] at h; subst h
      exact run_cond hc hfit hS hB1' hB2'
    | fst a =>
      simp only [FL.step, Option.some.injEq] at h; subst h
      exact run_fst hc hfit hS hB1' hB2'
    | snd a =>
      simp only [FL.step, Option.some.injEq] at h; subst h
      exact run_snd hc hfit hS hB1' hB2'
  · cases k with
    | nil => simp [FL.step] at h
    | cons fr k =>
      cases fr with
      | consL b env =>
        simp only [FL.step, Option.some.injEq] at h; subst h
        exact run_consL hc hfit hS hB1' hB2'
      | consR va =>
        simp only [FL.step, Option.some.injEq] at h; subst h
        exact run_consR hc hfit hS hB1' hB2'
      | caseK e₁ e₂ env =>
        cases v with
        | nil =>
          simp only [FL.step, Option.some.injEq] at h; subst h
          exact run_caseK_nil hc hfit hS hB1' hB2'
        | cons hd tl =>
          simp only [FL.step, Option.some.injEq] at h; subst h
          exact run_caseK_cons hc hfit hS hB1' hB2'
      | callK f =>
        simp only [FL.step, Option.map_eq_some_iff] at h
        obtain ⟨body, hb, rfl⟩ := h
        exact run_callK hb hc hfit hS hP hB1' hBP hB2'
      | letK b env =>
        simp only [FL.step, Option.some.injEq] at h; subst h
        exact run_letK hc hfit hS hB1' hB2'
      | condK e₁ e₂ env =>
        cases v with
        | nil =>
          simp only [FL.step, Option.some.injEq] at h; subst h
          exact run_condK_nil hc hfit hS hB1' hB2'
        | cons hd tl =>
          simp only [FL.step, Option.some.injEq] at h; subst h
          exact run_condK_cons hc hfit hS hB1' hB2'
      | fstK =>
        cases v with
        | nil => simp [FL.step] at h
        | cons a b =>
          simp only [FL.step, Option.some.injEq] at h; subst h
          exact run_fstK hc hfit hS hB1' hB2'
      | sndK =>
        cases v with
        | nil => simp [FL.step] at h
        | cons a b =>
          simp only [FL.step, Option.some.injEq] at h; subst h
          exact run_sndK hc hfit hS hB1' hB2'

end QecReliability.Interp
