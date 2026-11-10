import FL.Encode

/-!
# FL library: methodology and basic list functions

Library functions are FL bodies parameterised by the indices of the functions they call
(including themselves). Correctness lemmas are stated for an arbitrary global program `P`
under hypotheses `P[i]? = some body`, so components never need relocation: the final
program is one concrete list, and these hypotheses are discharged by computation.

Conventions: a call `f x` evaluates `P[f]` in the environment `[x]`; several arguments are
passed as a right-nested pair `cons a (cons b c)`.
-/

set_option autoImplicit false

namespace QecReliability.FL

/-- `P` evaluates function `f` on `x` to `y` with cost `t` and depth `d`, all values `≤ m`. -/
def EvalCall (P : Program) (m : ℕ) (f : ℕ) (x y : Val) (t d : ℕ) : Prop :=
  Eval P m [x] (.call f (.var 0)) y t d

namespace EvalCall
variable {P : Program} {m : ℕ}

/-- Unfold a call whose argument is already a value. -/
theorem intro {f : ℕ} {body : Expr} {x y : Val} {t d : ℕ} (hf : P[f]? = some body)
    (h : Eval P m [x] body y t d) : EvalCall P m f x y (t + 2) (d + 1) := by
  have := Eval.call (P := P) (m := m) (env := [x]) (a := .var 0) (Eval.var rfl) hf h
  simpa [EvalCall, Nat.add_comm, Nat.add_left_comm] using this

/-- Use a call result inside another evaluation (argument given by an expression). -/
theorem use {env : List Val} {f : ℕ} {a body : Expr} {x y : Val} {ta da t d : ℕ}
    (ha : Eval P m env a x ta da) (hf : P[f]? = some body) (h : Eval P m [x] body y t d) :
    Eval P m env (.call f a) y (ta + t + 1) (max da (d + 1)) :=
  Eval.call ha hf h

end EvalCall

/-! ## Append -/

/-- `append (cons xs ys) = xs ++ ys` on encoded lists (`Enc.list id`). -/
def appendBody (self : ℕ) : Expr :=
  .case (.var 0) .nil
    (.case (.var 0) (.var 1)
      (.cons (.var 0) (.call self (.cons (.var 1) (.var 3)))))

theorem Enc.list_append_size {α : Type} (f : α → Val) (xs ys : List α) :
    (Enc.list f (xs ++ ys)).size + 1 = (Enc.list f xs).size + (Enc.list f ys).size := by
  induction xs with
  | nil => simp [Enc.list]; omega
  | cons x xs ih => simp only [List.cons_append, Enc.list, Val.size_cons]; omega

/-- Cost of `append` on a first list of length `n`. -/
def appendCost (n : ℕ) : ℕ := 10 * n + 5

theorem append_eval {P : Program} {m : ℕ} {self : ℕ} (hP : P[self]? = some (appendBody self))
    (xs ys : List Val) (hm : (Enc.list id (xs ++ ys)).size + (Enc.list id xs).size + 1 ≤ m)
    : Eval P m [.cons (Enc.list id xs) (Enc.list id ys)] (appendBody self)
        (Enc.list id (xs ++ ys)) (appendCost xs.length) xs.length := by
  induction xs with
  | nil =>
    -- case p of cons xs ys → case xs of nil → ys
    have h := Eval.caseCons (P := P) (m := m) (env := [.cons (Enc.list id []) (Enc.list id ys)])
      (e₁ := .nil)
      (e₂ := .case (.var 0) (.var 1) (.cons (.var 0) (.call self (.cons (.var 1) (.var 3)))))
      (Eval.var (i := 0) rfl)
      (Eval.caseNil (Eval.var (i := 0) rfl) (Eval.var (i := 1) rfl))
    simpa [appendBody, appendCost, Enc.list] using h
  | cons x xs ih =>
    have hm' : (Enc.list id (xs ++ ys)).size + (Enc.list id xs).size + 1 ≤ m := by
      simp only [List.cons_append, Enc.list, Val.size_cons, id] at hm; omega
    have hrec := ih hm'
    have hpair : (Val.cons (Enc.list id xs) (Enc.list id ys)).size ≤ m := by
      have := Enc.list_append_size id xs ys
      simp only [List.cons_append, Enc.list, Val.size_cons, id] at hm
      simp only [Val.size_cons]; omega
    have hout : (Val.cons x (Enc.list id (xs ++ ys))).size ≤ m := by
      simp only [List.cons_append, Enc.list, Val.size_cons, id] at hm ⊢; omega
    have hcall : Eval P m [x, Enc.list id xs, Enc.list id (x :: xs), Enc.list id ys,
        .cons (Enc.list id (x :: xs)) (Enc.list id ys)]
        (.call self (.cons (.var 1) (.var 3))) (Enc.list id (xs ++ ys))
        (3 + appendCost xs.length + 1) (max 0 (xs.length + 1)) :=
      Eval.call (Eval.cons (Eval.var rfl) (Eval.var rfl) hpair) hP hrec
    have h := Eval.caseCons (P := P) (m := m)
      (env := [.cons (Enc.list id (x :: xs)) (Enc.list id ys)]) (e₁ := .nil)
      (e₂ := .case (.var 0) (.var 1) (.cons (.var 0) (.call self (.cons (.var 1) (.var 3)))))
      (Eval.var (i := 0) rfl)
      (Eval.caseCons (Eval.var (i := 0) rfl) (Eval.cons (Eval.var rfl) hcall hout))
    have hc : 1 + (1 + (1 + (3 + appendCost xs.length + 1) + 1) + 1) + 1 =
        appendCost (x :: xs).length := by simp only [appendCost, List.length_cons]; omega
    rw [hc] at h
    simpa [appendBody, Enc.list] using h

end QecReliability.FL
