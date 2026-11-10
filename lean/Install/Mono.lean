import FL.Typed.Fn

/-!
# Install.Mono: evaluation is monotone under program extension

If every body of `P` is also present (at the same index) in `P'`, every evaluation in `P` is
an evaluation in `P'` with the same value, cost and depth. Hence every `FnSig.ValidAt` fact
proved for a sub-program (e.g. `Trans.Query.queryProg`) transfers to the installed program
`queryProg ++ rest`.
-/

set_option autoImplicit false

namespace QecReliability.Install
open QecReliability.FL

/-- `P'` extends `P`: every installed body of `P` is installed at the same index in `P'`. -/
def Extends (P P' : Program) : Prop := ∀ (i : ℕ) (b : Expr), P[i]? = some b → P'[i]? = some b

theorem extends_append (P Q : Program) : Extends P (P ++ Q) := by
  intro i b h
  have hi : i < P.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  rw [List.getElem?_append_left hi]
  exact h

theorem Eval.extend {P P' : Program} (hPP : Extends P P') {m : ℕ} {env : List Val} {e : Expr}
    {v : Val} {t d : ℕ} (h : Eval P m env e v t d) : Eval P' m env e v t d := by
  induction h with
  | var hv => exact .var hv
  | nil => exact .nil
  | cons _ _ hs iha ihb => exact .cons iha ihb hs
  | caseNil _ _ ihs ih₁ => exact .caseNil ihs ih₁
  | caseCons _ _ ihs ih₂ => exact .caseCons ihs ih₂
  | call _ hb _ iha ihb => exact .call iha (hPP _ _ hb) ihb
  | letE _ _ iha ihb => exact .letE iha ihb
  | condNil _ _ ihs ih₁ => exact .condNil ihs ih₁
  | condCons _ _ ihs ih₂ => exact .condCons ihs ih₂
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih

theorem ValidAt.extend {P P' : Program} (hPP : Extends P P') {a b : Ty} {F : FnSig a b}
    {x : a.den} (h : F.ValidAt P x) : F.ValidAt P' x := by
  intro m hm
  obtain ⟨t, d, ht, hd, e⟩ := h m hm
  exact ⟨t, d, ht, hd, Eval.extend hPP e⟩

/-- Placement in an appended program: an index of the second segment. -/
theorem getElem?_append_offset (P Q : Program) (j : ℕ) :
    (P ++ Q)[P.length + j]? = Q[j]? := by
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

end QecReliability.Install
