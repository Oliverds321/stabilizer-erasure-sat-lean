import FL.StepV
import FL.Lib.Basic
import Mathlib.Tactic.Ring

/-!
# Encoded runs: evaluation as a bounded iteration of `stepV`

`Eval.encodedRun`: an evaluation of `f x` with cost `t` and depth `d` is an iteration of
`stepV (Program.enc P)` of at most `3 t` steps, from the encoding of
`eval (call f (var 0)) [x] []` to the encoding of `ret y []` (where `stepV` stops), and
every encoded state along the way has size at most `stateBound W X m (2 + X * (d + 1))`,
where `W` bounds the encoded size of every function body.

This is the complete abstract content of the interpreter: the register-level interpreter
only needs to implement one `stepV` on a register whose length stays below that bound.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace QecReliability.FL

/-! ## Expressions occurring in a state -/

def Frame.exprs : Frame → List Expr
  | .consL b _ => [b]
  | .consR _ => []
  | .caseK e₁ e₂ _ => [e₁, e₂]
  | .callK f => [.call f (.var 0)]
  | .letK b _ => [b]
  | .condK e₁ e₂ _ => [e₁, e₂]
  | .fstK => []
  | .sndK => []

def State.exprs : State → List Expr
  | .eval e _ k => e :: k.flatMap Frame.exprs
  | .ret _ k => k.flatMap Frame.exprs

/-- Every expression in the state has encoding size at most `W`. -/
def ExprInv (W : ℕ) (s : State) : Prop := ∀ e ∈ s.exprs, (Expr.enc e).size ≤ W

theorem tagged_size (j : ℕ) (x : Val) : (tagged j x).size = 2 * j + 2 + x.size := by
  simp [tagged]; omega

theorem Expr.enc_size_ge (e : Expr) : 3 ≤ (Expr.enc e).size := by
  cases e <;> simp [Expr.enc, tagged_size] <;> omega

theorem step_exprInv {P : Program} {W : ℕ} (hP : ∀ b ∈ P, (Expr.enc b).size ≤ W)
    {s s' : State} (hs : ExprInv W s) (h : step P s = some s') : ExprInv W s' := by
  intro e he
  rcases s with ⟨e0, env, k⟩ | ⟨v, k⟩
  · have hroot := hs e0 (by simp [State.exprs])
    have hk : ∀ x ∈ k.flatMap Frame.exprs, (Expr.enc x).size ≤ W :=
      fun x hx => hs x (by simp only [State.exprs, List.mem_cons]; exact Or.inr hx)
    cases e0 with
    | var i =>
      simp only [step, Option.map_eq_some_iff] at h
      obtain ⟨_, -, rfl⟩ := h
      exact hk e (by simpa [State.exprs] using he)
    | nil =>
      simp only [step, Option.some.injEq] at h; subst h
      exact hk e (by simpa [State.exprs] using he)
    | cons a b =>
      simp only [step, Option.some.injEq] at h; subst h
      simp only [Expr.enc, tagged_size, Val.size_cons] at hroot
      simp only [State.exprs, List.flatMap_cons, Frame.exprs, List.cons_append, List.nil_append,
        List.mem_cons] at he
      rcases he with rfl | rfl | he <;> first | omega | exact hk e he
    | case a b c =>
      simp only [step, Option.some.injEq] at h; subst h
      simp only [Expr.enc, tagged_size, Val.size_cons] at hroot
      simp only [State.exprs, List.flatMap_cons, Frame.exprs, List.cons_append, List.nil_append,
        List.mem_cons] at he
      rcases he with rfl | rfl | rfl | he <;> first | omega | exact hk e he
    | call f a =>
      simp only [step, Option.some.injEq] at h; subst h
      have ha3 := Expr.enc_size_ge a
      simp only [Expr.enc, tagged_size, Val.size_cons, Enc.unary_size] at hroot
      simp only [State.exprs, List.flatMap_cons, Frame.exprs, List.cons_append, List.nil_append,
        List.mem_cons] at he
      rcases he with rfl | rfl | he
      · omega
      · simp only [Expr.enc, tagged_size, Val.size_cons, Enc.unary_size]; omega
      · exact hk e he
    | letE a b =>
      simp only [step, Option.some.injEq] at h; subst h
      simp only [Expr.enc, tagged_size, Val.size_cons] at hroot
      simp only [State.exprs, List.flatMap_cons, Frame.exprs, List.cons_append, List.nil_append,
        List.mem_cons] at he
      rcases he with rfl | rfl | he <;> first | omega | exact hk e he
    | cond a b c =>
      simp only [step, Option.some.injEq] at h; subst h
      simp only [Expr.enc, tagged_size, Val.size_cons] at hroot
      simp only [State.exprs, List.flatMap_cons, Frame.exprs, List.cons_append, List.nil_append,
        List.mem_cons] at he
      rcases he with rfl | rfl | rfl | he <;> first | omega | exact hk e he
    | fst a =>
      simp only [step, Option.some.injEq] at h; subst h
      simp only [Expr.enc, tagged_size, Val.size_cons] at hroot
      simp only [State.exprs, List.flatMap_cons, Frame.exprs, List.nil_append,
        List.mem_cons] at he
      rcases he with rfl | he <;> first | omega | exact hk e he
    | snd a =>
      simp only [step, Option.some.injEq] at h; subst h
      simp only [Expr.enc, tagged_size, Val.size_cons] at hroot
      simp only [State.exprs, List.flatMap_cons, Frame.exprs, List.nil_append,
        List.mem_cons] at he
      rcases he with rfl | he <;> first | omega | exact hk e he
  · cases k with
    | nil => simp [step] at h
    | cons fr k =>
      have hfr : ∀ x ∈ fr.exprs, (Expr.enc x).size ≤ W :=
        fun x hx => hs x (by simp only [State.exprs, List.flatMap_cons, List.mem_append]; exact Or.inl hx)
      have hk : ∀ x ∈ k.flatMap Frame.exprs, (Expr.enc x).size ≤ W :=
        fun x hx => hs x (by simp only [State.exprs, List.flatMap_cons, List.mem_append]; exact Or.inr hx)
      cases fr <;> cases v <;> simp only [step, Option.map_eq_some_iff, Option.some.injEq,
        reduceCtorEq] at h
      all_goals first
        | (obtain ⟨body, hb, rfl⟩ := h
           simp only [State.exprs, List.mem_cons] at he
           rcases he with rfl | he
           · exact hP _ (List.mem_of_getElem? hb)
           · exact hk e he)
        | (subst h
           apply hs e
           simp only [State.exprs, List.flatMap_cons, Frame.exprs, List.cons_append,
             List.nil_append, List.mem_cons, List.mem_append, List.mem_nil_iff] at he ⊢
           tauto)

/-! ## Sizes of encoded states -/

theorem envEnc_size_le {env : List Val} {m L : ℕ} (hl : env.length ≤ L)
    (hv : ∀ v ∈ env, v.size ≤ m) : (envEnc env).size ≤ 1 + L * (m + 1) := by
  induction env generalizing L with
  | nil => simp [envEnc, Enc.list]
  | cons v env ih =>
    cases L with
    | zero => simp at hl
    | succ L =>
      have h1 := hv v (by simp)
      have h2 := ih (L := L) (by simpa using hl) (fun w hw => hv w (by simp [hw]))
      simp only [envEnc, Enc.list, Val.size_cons, id] at h2 ⊢
      rw [Nat.succ_mul]
      omega

/-- Common size bound for one encoded frame. -/
def frameBound (W X m : ℕ) : ℕ := 2 * W + (1 + (2 * X + 1) * (m + 1)) + m + 20

theorem Frame.enc_size_le {W X m : ℕ} {fr : Frame} (hok : Frame.OK m X fr)
    (hex : ∀ e ∈ fr.exprs, (Expr.enc e).size ≤ W) : (Frame.enc fr).size ≤ frameBound W X m := by
  unfold frameBound
  cases fr with
  | consL b env =>
    have hb := hex b (by simp [Frame.exprs])
    have he := envEnc_size_le (L := 2 * X + 1) (by have := hok.1; omega) hok.2
    simp only [Frame.enc, tagged_size, Val.size_cons]; omega
  | consR va =>
    have : va.size ≤ m := hok
    simp only [Frame.enc, tagged_size]; omega
  | caseK e₁ e₂ env =>
    have h1 := hex e₁ (by simp [Frame.exprs])
    have h2 := hex e₂ (by simp [Frame.exprs])
    have he := envEnc_size_le (L := 2 * X + 1) (by have := hok.1; omega) hok.2
    simp only [Frame.enc, tagged_size, Val.size_cons]; omega
  | callK f =>
    have h := hex (.call f (.var 0)) (by simp [Frame.exprs])
    simp only [Expr.enc, tagged_size, Val.size_cons, Enc.unary_size] at h
    simp only [Frame.enc, tagged_size, Enc.unary_size]; omega
  | letK b env =>
    have hb := hex b (by simp [Frame.exprs])
    have he := envEnc_size_le (L := 2 * X + 1) (by have := hok.1; omega) hok.2
    simp only [Frame.enc, tagged_size, Val.size_cons]; omega
  | condK e₁ e₂ env =>
    have h1 := hex e₁ (by simp [Frame.exprs])
    have h2 := hex e₂ (by simp [Frame.exprs])
    have he := envEnc_size_le (L := 2 * X + 1) (by have := hok.1; omega) hok.2
    simp only [Frame.enc, tagged_size, Val.size_cons]; omega
  | fstK => simp only [Frame.enc, tagged_size, Val.size_nil]; omega
  | sndK => simp only [Frame.enc, tagged_size, Val.size_nil]; omega

theorem stackEnc_size_le {W X m H : ℕ} {k : List Frame} (hl : k.length ≤ H)
    (hok : ∀ fr ∈ k, Frame.OK m X fr) (hex : ∀ fr ∈ k, ∀ e ∈ fr.exprs, (Expr.enc e).size ≤ W) :
    (stackEnc k).size ≤ 1 + H * (frameBound W X m + 1) := by
  induction k generalizing H with
  | nil => simp [stackEnc, Enc.list]
  | cons fr k ih =>
    cases H with
    | zero => simp at hl
    | succ H =>
      have h1 := Frame.enc_size_le (hok fr (by simp)) (hex fr (by simp))
      have h2 := ih (H := H) (by simpa using hl) (fun g hg => hok g (by simp [hg]))
        (fun g hg => hex g (by simp [hg]))
      simp only [stackEnc, Enc.list, Val.size_cons] at h2 ⊢
      rw [Nat.succ_mul]
      omega

/-- Size bound for every encoded state of a run with at most `H` frames. -/
def stateBound (W X m H : ℕ) : ℕ := (H + 2) * (frameBound W X m + 1)

theorem State.enc_size_le {W X m z d : ℕ} {s : State} (hg : Good m X [] z d s)
    (hex : ExprInv W s) : (State.enc s).size ≤ stateBound W X m (z + X * d) := by
  obtain ⟨hs, k', hk, hl, hf⟩ := hg
  simp only [List.append_nil] at hk
  have hexk : ∀ fr ∈ k', ∀ e ∈ fr.exprs, (Expr.enc e).size ≤ W := by
    intro fr hfr e he
    apply hex e
    rcases s with ⟨e0, env, k⟩ | ⟨v, k⟩ <;> simp only [State.stack] at hk <;> subst hk <;>
      simp only [State.exprs, List.mem_cons, List.mem_flatMap] <;>
      first | exact Or.inr ⟨fr, hfr, he⟩ | exact ⟨fr, hfr, he⟩
  have hst := stackEnc_size_le (H := z + X * d) hl hf hexk
  unfold stateBound
  have hmul : (z + X * d + 2) * (frameBound W X m + 1) =
      (z + X * d) * (frameBound W X m + 1) + 2 * (frameBound W X m + 1) := by ring
  rw [hmul]
  rcases s with ⟨e0, env, k⟩ | ⟨v, k⟩
  · simp only [State.stack] at hk
    subst hk
    have he0 := hex e0 (by simp [State.exprs])
    have henv := envEnc_size_le (L := 2 * X + 1) (by have := hs.1; omega) hs.2
    simp only [State.enc, tagged_size, Val.size_cons]
    unfold frameBound at hst ⊢
    omega
  · simp only [State.stack] at hk
    subst hk
    have hv : v.size ≤ m := hs
    simp only [State.enc, tagged_size, Val.size_cons]
    unfold frameBound at hst ⊢
    omega

/-! ## Encoded runs -/

/-- Runs of a partial function on values, every visited value satisfying `Q`. -/
inductive IterRun (F : Val → Option Val) (Q : Val → Prop) : Val → ℕ → Val → Prop
  | refl {v} : Q v → IterRun F Q v 0 v
  | step {v v' w n} : Q v → F v = some v' → IterRun F Q v' n w → IterRun F Q v (n + 1) w

theorem RunAll.addInv {P : Program} {Q I : State → Prop} {s t : State} {n : ℕ}
    (h : RunAll P Q s n t) (hI : I s) (hpres : ∀ a b, I a → FL.step P a = some b → I b) :
    RunAll P (fun z => Q z ∧ I z) s n t := by
  induction h with
  | refl hq => exact .refl ⟨hq, hI⟩
  | step hq hs _ ih => exact .step ⟨hq, hI⟩ hs (ih (hpres _ _ hI hs))

theorem RunAll.encode {P : Program} {Q : State → Prop} {R : Val → Prop}
    (hQR : ∀ s, Q s → R s.enc) {s t : State} {n : ℕ} (h : RunAll P Q s n t) :
    IterRun (stepV (Program.enc P)) R s.enc n t.enc := by
  induction h with
  | refl hq => exact .refl (hQR _ hq)
  | step hq hs _ ih => exact .step (hQR _ hq) (by rw [stepV_enc, hs]; rfl) ih

/-- **Evaluation as a bounded iteration of `stepV`.** -/
theorem Eval.encodedRun {P : Program} {m X W : ℕ} (hm : 1 ≤ m) (hX3 : 3 ≤ X)
    (hX : ∀ b ∈ P, b.size ≤ X) (hW : ∀ b ∈ P, (Expr.enc b).size ≤ W)
    {f : ℕ} (hf : 2 * f + 15 ≤ W) {x y : Val} {t d : ℕ}
    (h : EvalCall P m f x y t d) (hx : x.size ≤ m) :
    ∃ n ≤ 3 * t,
      IterRun (stepV (Program.enc P)) (fun v => v.size ≤ stateBound W X m (2 + X * d))
        (State.eval (.call f (.var 0)) [x] []).enc n (State.ret y []).enc ∧
      stepV (Program.enc P) (State.ret y []).enc = none := by
  have henv : EnvOK m X [x] (Expr.call f (.var 0)).size :=
    ⟨by simp [Expr.size]; omega, by simpa using hx⟩
  obtain ⟨n, hn, r⟩ := Eval.cek hm hX h henv []
  have hI : ExprInv W (State.eval (.call f (.var 0)) [x] []) := by
    intro e he
    simp only [State.exprs, List.flatMap_nil, List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he
    simp only [Expr.enc, tagged_size, Val.size_cons, Enc.unary_size]
    omega
  have r' := r.addInv hI (fun a b ha hab => step_exprInv hW ha hab)
  refine ⟨n, hn, r'.encode (fun s hs => ?_), ?_⟩
  · have := State.enc_size_le hs.1 hs.2
    simpa [Expr.size] using this
  · rw [stepV_enc]; cases y <;> rfl

end QecReliability.FL
