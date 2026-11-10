import FL.Core

/-!
# CEK machine for FL

A small-step abstract machine with an explicit continuation stack. The register-level
interpreter implements one `step` per bounded block of register code, so its running time
is governed by the step count and its space by the size of the states.

Main result `Eval.cek`: an evaluation of cost `t` and call depth `d` is simulated in at most
`3 * t` steps, and along the run every state keeps the original stack `k` as a suffix,
with at most `e.size + X * d` additional frames, where `X` bounds the size of every
function body. All values stay of size `≤ m` and all environments of length `≤ 2X + 1`
(given the same for the starting state), see `Good`.
-/

set_option autoImplicit false

namespace QecReliability.FL

/-- Continuation frames. -/
inductive Frame where
  | consL (b : Expr) (env : List Val)
  | consR (va : Val)
  | caseK (e₁ e₂ : Expr) (env : List Val)
  | callK (f : ℕ)
  | letK (b : Expr) (env : List Val)
  | condK (e₁ e₂ : Expr) (env : List Val)
  | fstK
  | sndK
  deriving DecidableEq, Repr

inductive State where
  | eval (e : Expr) (env : List Val) (k : List Frame)
  | ret (v : Val) (k : List Frame)
  deriving DecidableEq, Repr

def State.stack : State → List Frame
  | .eval _ _ k => k
  | .ret _ k => k

/-- One machine transition; `none` when halted (`ret v []`) or stuck. -/
def step (P : Program) : State → Option State
  | .eval (.var i) env k => (env[i]?).map (fun v => .ret v k)
  | .eval .nil _ k => some (.ret .nil k)
  | .eval (.cons a b) env k => some (.eval a env (.consL b env :: k))
  | .eval (.case s e₁ e₂) env k => some (.eval s env (.caseK e₁ e₂ env :: k))
  | .eval (.call f a) env k => some (.eval a env (.callK f :: k))
  | .eval (.letE a b) env k => some (.eval a env (.letK b env :: k))
  | .eval (.cond s e₁ e₂) env k => some (.eval s env (.condK e₁ e₂ env :: k))
  | .eval (.fst e) env k => some (.eval e env (.fstK :: k))
  | .eval (.snd e) env k => some (.eval e env (.sndK :: k))
  | .ret _ [] => none
  | .ret va (.consL b env :: k) => some (.eval b env (.consR va :: k))
  | .ret vb (.consR va :: k) => some (.ret (.cons va vb) k)
  | .ret .nil (.caseK e₁ _ env :: k) => some (.eval e₁ env k)
  | .ret (.cons h tl) (.caseK _ e₂ env :: k) => some (.eval e₂ (h :: tl :: env) k)
  | .ret va (.callK f :: k) => (P[f]?).map (fun body => .eval body [va] k)
  | .ret va (.letK b env :: k) => some (.eval b (va :: env) k)
  | .ret .nil (.condK e₁ _ env :: k) => some (.eval e₁ env k)
  | .ret (.cons _ _) (.condK _ e₂ env :: k) => some (.eval e₂ env k)
  | .ret .nil (.fstK :: _) => none
  | .ret (.cons a _) (.fstK :: k) => some (.ret a k)
  | .ret .nil (.sndK :: _) => none
  | .ret (.cons _ b) (.sndK :: k) => some (.ret b k)

/-- `n`-step runs in which every visited state (both ends included) satisfies `Q`. -/
inductive RunAll (P : Program) (Q : State → Prop) : State → ℕ → State → Prop
  | refl {s} : Q s → RunAll P Q s 0 s
  | step {s s' n t} : Q s → step P s = some s' → RunAll P Q s' n t → RunAll P Q s (n + 1) t

namespace RunAll

variable {P : Program} {Q R : State → Prop}

theorem trans {s t u : State} {n n' : ℕ} (h : RunAll P Q s n t) (g : RunAll P Q t n' u) :
    RunAll P Q s (n + n') u := by
  induction h with
  | refl _ => simpa using g
  | step hq hs _ ih => simpa [Nat.add_right_comm] using RunAll.step hq hs (ih g)

theorem mono (hQR : ∀ s, Q s → R s) {s t : State} {n : ℕ} (h : RunAll P Q s n t) :
    RunAll P R s n t := by
  induction h with
  | refl hq => exact .refl (hQR _ hq)
  | step hq hs _ ih => exact .step (hQR _ hq) hs ih

theorem first {s t : State} {n : ℕ} (h : RunAll P Q s n t) : Q s := by
  cases h with
  | refl hq => exact hq
  | step hq _ _ => exact hq

theorem last {s t : State} {n : ℕ} (h : RunAll P Q s n t) : Q t := by
  induction h with
  | refl hq => exact hq
  | step _ _ _ ih => exact ih

/-- Prepend one transition whose source satisfies `Q`. -/
theorem cons {s s' t : State} {n : ℕ} (hq : Q s) (hs : FL.step P s = some s')
    (h : RunAll P Q s' n t) : RunAll P Q s (n + 1) t := .step hq hs h

end RunAll

/-! ## Bounded contents -/

section Bounds
variable (m X : ℕ)

/-- An environment for evaluating an expression of size `z`. -/
def EnvOK (env : List Val) (z : ℕ) : Prop :=
  env.length + 2 * z ≤ 2 * X + 1 ∧ ∀ v ∈ env, v.size ≤ m

def Frame.OK : Frame → Prop
  | .consL b env => EnvOK m X env b.size
  | .consR va => va.size ≤ m
  | .caseK e₁ e₂ env => EnvOK m X env (e₁.size + e₂.size + 1)
  | .callK _ => True
  | .letK b env => env.length + 2 * b.size + 1 ≤ 2 * X + 1 ∧ ∀ v ∈ env, v.size ≤ m
  | .condK e₁ e₂ env => EnvOK m X env (max e₁.size e₂.size)
  | .fstK => True
  | .sndK => True

def State.OK : State → Prop
  | .eval e env _ => EnvOK m X env e.size
  | .ret v _ => v.size ≤ m

/-- The invariant along the simulation of an expression `e` of call depth `d` on top of the
base stack `k`. -/
def Good (k : List Frame) (z d : ℕ) (s : State) : Prop :=
  State.OK m X s ∧ ∃ k', s.stack = k' ++ k ∧ k'.length ≤ z + X * d ∧ ∀ fr ∈ k', Frame.OK m X fr

end Bounds

section Simulation
variable {P : Program} {m X : ℕ}

theorem Eval.size_le {env : List Val} {e : Expr} {v : Val} {t d : ℕ}
    (h : Eval P m env e v t d) (hm : 1 ≤ m) (henv : ∀ x ∈ env, x.size ≤ m) : v.size ≤ m := by
  induction h with
  | var hv => exact henv _ (List.mem_of_getElem? hv)
  | nil => simpa using hm
  | cons _ _ hs _ _ => exact hs
  | caseNil _ _ _ ih₁ => exact ih₁ henv
  | caseCons _ _ ihs ih₂ =>
    have hc := ihs henv
    simp only [Val.size_cons] at hc
    apply ih₂
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · omega
    · omega
    · exact henv x hx
  | call _ _ _ iha ihb =>
    apply ihb
    intro x hx
    simp only [List.mem_singleton] at hx
    exact hx ▸ iha henv
  | letE _ _ iha ihb =>
    apply ihb
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact iha henv
    · exact henv x hx
  | condNil _ _ _ ih₁ => exact ih₁ henv
  | condCons _ _ _ ih₂ => exact ih₂ henv
  | fst _ ih => have := ih henv; simp only [Val.size_cons] at this; omega
  | snd _ ih => have := ih henv; simp only [Val.size_cons] at this; omega

/-- Weaken `Good` by pushing one OK frame from the base into the extra stack. -/
theorem Good.push {k : List Frame} {fr : Frame} {z z' d d' : ℕ} (hfr : Frame.OK m X fr)
    (hz : z + 1 + X * d ≤ z' + X * d') {s : State} (h : Good m X (fr :: k) z d s) :
    Good m X k z' d' s := by
  obtain ⟨hs, k', hk, hl, hf⟩ := h
  refine ⟨hs, k' ++ [fr], by simp [hk], ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hf x hx
    · exact hfr

/-- Weaken `Good` to a larger budget. -/
theorem Good.weaken {k : List Frame} {z z' d d' : ℕ} (hz : z + X * d ≤ z' + X * d')
    {s : State} (h : Good m X k z d s) : Good m X k z' d' s := by
  obtain ⟨hs, k', hk, hl, hf⟩ := h
  exact ⟨hs, k', hk, by omega, hf⟩

theorem Good.here {k : List Frame} {z d : ℕ} {s : State} (hs : State.OK m X s)
    (hk : s.stack = k) : Good m X k z d s :=
  ⟨hs, [], by simp [hk], by simp, by simp⟩

/-- **Simulation.** Every evaluation is realized by a CEK run of at most `3 * t` steps whose
states all satisfy the `Good` invariant for base stack `k`. -/
theorem Eval.cek (hm : 1 ≤ m) (hX : ∀ b ∈ P, b.size ≤ X)
    {env : List Val} {e : Expr} {v : Val} {t d : ℕ} (h : Eval P m env e v t d)
    (henv : EnvOK m X env e.size) (k : List Frame) :
    ∃ n ≤ 3 * t, RunAll P (Good m X k e.size d) (.eval e env k) n (.ret v k) := by
  induction h generalizing k with
  | @var env i v hv =>
    refine ⟨1, by omega, .step (Good.here (s := .eval (.var i) env k) henv rfl) (by simp [step, hv])
      (.refl (Good.here (s := .ret v k) ?_ rfl))⟩
    exact henv.2 _ (List.mem_of_getElem? hv)
  | nil =>
    exact ⟨1, by omega, .step (Good.here (s := .eval .nil _ k) henv rfl) (by simp [step])
      (.refl (Good.here (s := .ret .nil k) (by simpa [State.OK] using hm) rfl))⟩
  | @cons env a b va vb ta tb da db ha hb hs iha ihb =>
    have hea : EnvOK m X env a.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have heb : EnvOK m X env b.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    obtain ⟨na, hna, ra⟩ := iha hea (.consL b env :: k)
    obtain ⟨nb, hnb, rb⟩ := ihb heb (.consR va :: k)
    have hva : va.size ≤ m := by simp only [Val.size_cons] at hs; omega
    have ra' := ra.mono (fun s hs' => Good.push (z' := (Expr.cons a b).size) (d' := max da db)
      (show Frame.OK m X (.consL b env) from heb)
      (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_left da db); omega) hs')
    have rb' := rb.mono (fun s hs' => Good.push (z' := (Expr.cons a b).size) (d' := max da db)
      (show Frame.OK m X (.consR va) from hva)
      (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_right da db); omega) hs')
    have r := RunAll.cons (Good.here (s := .eval (.cons a b) env k) henv rfl) (by simp [step])
      (RunAll.trans ra' (RunAll.cons ra'.last (by simp [step])
        (RunAll.trans rb' (RunAll.cons rb'.last (by simp [step])
          (.refl (Good.here (s := .ret (.cons va vb) k) hs rfl))))))
    exact ⟨_, by omega, r⟩
  | @caseNil env s e₁ e₂ v ts t₁ ds d₁ hs h₁ ihs ih₁ =>
    have hes : EnvOK m X env s.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have he₁ : EnvOK m X env e₁.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have hfr : Frame.OK m X (.caseK e₁ e₂ env) :=
      ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    obtain ⟨ns, hns, rs⟩ := ihs hes (.caseK e₁ e₂ env :: k)
    obtain ⟨n₁, hn₁, r₁⟩ := ih₁ he₁ k
    have rs' := rs.mono (fun st hst => Good.push (z' := (Expr.case s e₁ e₂).size) (d' := max ds d₁)
      hfr (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_left ds d₁); omega) hst)
    have r₁' := r₁.mono (fun st hst => Good.weaken (z' := (Expr.case s e₁ e₂).size)
      (d' := max ds d₁)
      (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_right ds d₁); omega) hst)
    have r := RunAll.cons (Good.here (s := .eval (.case s e₁ e₂) env k) henv rfl) (by simp [step])
      (RunAll.trans rs' (RunAll.cons rs'.last (by simp [step]) r₁'))
    exact ⟨_, by omega, r⟩
  | @caseCons env s e₁ e₂ hd tl v ts t₂ ds d₂ hs h₂ ihs ih₂ =>
    have hes : EnvOK m X env s.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have hfr : Frame.OK m X (.caseK e₁ e₂ env) :=
      ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have hsz := hs.size_le hm henv.2
    simp only [Val.size_cons] at hsz
    have he₂ : EnvOK m X (hd :: tl :: env) e₂.size := by
      refine ⟨by have := henv.1; simp [Expr.size] at this ⊢; omega, ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · omega
      · omega
      · exact henv.2 x hx
    obtain ⟨ns, hns, rs⟩ := ihs hes (.caseK e₁ e₂ env :: k)
    obtain ⟨n₂, hn₂, r₂⟩ := ih₂ he₂ k
    have rs' := rs.mono (fun st hst => Good.push (z' := (Expr.case s e₁ e₂).size) (d' := max ds d₂)
      hfr (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_left ds d₂); omega) hst)
    have r₂' := r₂.mono (fun st hst => Good.weaken (z' := (Expr.case s e₁ e₂).size)
      (d' := max ds d₂)
      (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_right ds d₂); omega) hst)
    have r := RunAll.cons (Good.here (s := .eval (.case s e₁ e₂) env k) henv rfl) (by simp [step])
      (RunAll.trans rs' (RunAll.cons rs'.last (by simp [step]) r₂'))
    exact ⟨_, by omega, r⟩
  | @call env f a body va v ta tb da db ha hbody hb iha ihb =>
    have hea : EnvOK m X env a.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have hva : va.size ≤ m := ha.size_le hm henv.2
    have hbX : body.size ≤ X := hX body (List.mem_of_getElem? hbody)
    have heb : EnvOK m X [va] body.size := ⟨by simp; omega, by simpa using hva⟩
    obtain ⟨na, hna, ra⟩ := iha hea (.callK f :: k)
    obtain ⟨nb, hnb, rb⟩ := ihb heb k
    have ra' := ra.mono (fun st hst => Good.push (z' := (Expr.call f a).size) (d' := max da (db + 1))
      (show Frame.OK m X (.callK f) from trivial)
      (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_left da (db + 1)); omega) hst)
    have rb' := rb.mono (fun st hst => Good.weaken (z' := (Expr.call f a).size)
      (d' := max da (db + 1))
      (by
        simp only [Expr.size]
        have := Nat.mul_le_mul_left X (Nat.le_max_right da (db + 1))
        rw [Nat.mul_add] at this
        omega) hst)
    have r := RunAll.cons (Good.here (s := .eval (.call f a) env k) henv rfl) (by simp [step])
      (RunAll.trans ra' (RunAll.cons ra'.last (by simp [step, hbody]) rb'))
    exact ⟨_, by omega, r⟩
  | @letE env a b va v ta tb da db ha hb iha ihb =>
    have hea : EnvOK m X env a.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have hva : va.size ≤ m := ha.size_le hm henv.2
    have hfr : Frame.OK m X (.letK b env) :=
      ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have heb : EnvOK m X (va :: env) b.size := by
      refine ⟨by have := henv.1; simp [Expr.size] at this ⊢; omega, ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hva
      · exact henv.2 x hx
    obtain ⟨na, hna, ra⟩ := iha hea (.letK b env :: k)
    obtain ⟨nb, hnb, rb⟩ := ihb heb k
    have ra' := ra.mono (fun st hst => Good.push (z' := (Expr.letE a b).size) (d' := max da db)
      hfr (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_left da db); omega) hst)
    have rb' := rb.mono (fun st hst => Good.weaken (z' := (Expr.letE a b).size) (d' := max da db)
      (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_right da db); omega) hst)
    have r := RunAll.cons (Good.here (s := .eval (.letE a b) env k) henv rfl) (by simp [step])
      (RunAll.trans ra' (RunAll.cons ra'.last (by simp [step]) rb'))
    exact ⟨_, by omega, r⟩

  | @condNil env s e₁ e₂ v ts t₁ ds d₁ hs h₁ ihs ih₁ =>
    have hes : EnvOK m X env s.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have he₁ : EnvOK m X env e₁.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have hfr : Frame.OK m X (.condK e₁ e₂ env) :=
      ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    obtain ⟨ns, hns, rs⟩ := ihs hes (.condK e₁ e₂ env :: k)
    obtain ⟨n₁, hn₁, r₁⟩ := ih₁ he₁ k
    have rs' := rs.mono (fun st hst => Good.push (z' := (Expr.cond s e₁ e₂).size) (d' := max ds d₁)
      hfr (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_left ds d₁); omega) hst)
    have r₁' := r₁.mono (fun st hst => Good.weaken (z' := (Expr.cond s e₁ e₂).size)
      (d' := max ds d₁)
      (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_right ds d₁); omega) hst)
    have r := RunAll.cons (Good.here (s := .eval (.cond s e₁ e₂) env k) henv rfl) (by simp [step])
      (RunAll.trans rs' (RunAll.cons rs'.last (by simp [step]) r₁'))
    exact ⟨_, by omega, r⟩
  | @condCons env s e₁ e₂ hd tl v ts t₂ ds d₂ hs h₂ ihs ih₂ =>
    have hes : EnvOK m X env s.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have he₂ : EnvOK m X env e₂.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have hfr : Frame.OK m X (.condK e₁ e₂ env) :=
      ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    obtain ⟨ns, hns, rs⟩ := ihs hes (.condK e₁ e₂ env :: k)
    obtain ⟨n₂, hn₂, r₂⟩ := ih₂ he₂ k
    have rs' := rs.mono (fun st hst => Good.push (z' := (Expr.cond s e₁ e₂).size) (d' := max ds d₂)
      hfr (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_left ds d₂); omega) hst)
    have r₂' := r₂.mono (fun st hst => Good.weaken (z' := (Expr.cond s e₁ e₂).size)
      (d' := max ds d₂)
      (by simp only [Expr.size]; have := Nat.mul_le_mul_left X (Nat.le_max_right ds d₂); omega) hst)
    have r := RunAll.cons (Good.here (s := .eval (.cond s e₁ e₂) env k) henv rfl) (by simp [step])
      (RunAll.trans rs' (RunAll.cons rs'.last (by simp [step]) r₂'))
    exact ⟨_, by omega, r⟩
  | @fst env e a b t d he ih =>
    have he' : EnvOK m X env e.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have hab := he.size_le hm henv.2
    simp only [Val.size_cons] at hab
    obtain ⟨n, hn, r⟩ := ih he' (.fstK :: k)
    have r' := r.mono (fun st hst => Good.push (z' := (Expr.fst e).size) (d' := d)
      (show Frame.OK m X .fstK from trivial) (by simp only [Expr.size]; omega) hst)
    have rr := RunAll.cons (Good.here (s := .eval (.fst e) env k) henv rfl) (by simp [step])
      (RunAll.trans r' (RunAll.cons r'.last (by simp [step])
        (.refl (Good.here (s := .ret a k) (show a.size ≤ m by omega) rfl))))
    exact ⟨_, by omega, rr⟩
  | @snd env e a b t d he ih =>
    have he' : EnvOK m X env e.size := ⟨by have := henv.1; simp [Expr.size] at this; omega, henv.2⟩
    have hab := he.size_le hm henv.2
    simp only [Val.size_cons] at hab
    obtain ⟨n, hn, r⟩ := ih he' (.sndK :: k)
    have r' := r.mono (fun st hst => Good.push (z' := (Expr.snd e).size) (d' := d)
      (show Frame.OK m X .sndK from trivial) (by simp only [Expr.size]; omega) hst)
    have rr := RunAll.cons (Good.here (s := .eval (.snd e) env k) henv rfl) (by simp [step])
      (RunAll.trans r' (RunAll.cons r'.last (by simp [step])
        (.refl (Good.here (s := .ret b k) (show b.size ≤ m by omega) rfl))))
    exact ⟨_, by omega, rr⟩

end Simulation

end QecReliability.FL
