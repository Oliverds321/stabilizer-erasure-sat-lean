import FL.Lib.Basic

/-!
# FL.Typed: typed terms compiling to FL with automatic evaluation proofs

`Tm Γ t` are simply typed, first-order terms whose compilation `Tm.compile` is an FL
expression (no de Bruijn shifting is ever needed: binders are introduced exactly where FL
introduces them). Their Lean meaning is `Tm.den`, and the single theorem `Tm.eval` turns any
well-typed term into an `Eval` derivation, with cost/depth bounded by the compositional
`Tm.cost`/`Tm.depth`, for every size budget `m ≥ Tm.msize`.

`Tm.lit x` is a literal of any type (compiled to the tree `t.enc x`).

Calls go to global functions through `FnSig` (index, meaning, bounds). A function's
contract `FnSig.ValidAt P F x` is checked per argument, so recursive functions are handled by
`FnSig.valid_of_body` in `FL/Typed/Fn.lean` (strong induction on a measure).
-/

set_option autoImplicit false

namespace QecReliability.FL

inductive Ty where
  | val | unit | bool | nat
  | list (t : Ty)
  | prod (a b : Ty)
  deriving DecidableEq, Repr

namespace Ty

@[reducible] def den : Ty → Type
  | .val => Val
  | .unit => Unit
  | .bool => Bool
  | .nat => ℕ
  | .list t => List t.den
  | .prod a b => a.den × b.den

def enc : (t : Ty) → t.den → Val
  | .val, v => v
  | .unit, _ => .nil
  | .bool, b => Enc.bool b
  | .nat, n => Enc.nat n
  | .list t, xs => Enc.list (enc t) xs
  | .prod a b, p => .cons (enc a p.1) (enc b p.2)

end Ty

/-- Typed de Bruijn indices. -/
inductive Idx : List Ty → Ty → Type
  | zero {Γ : List Ty} {t : Ty} : Idx (t :: Γ) t
  | succ {Γ : List Ty} {s t : Ty} : Idx Γ t → Idx (s :: Γ) t

def Idx.toNat {Γ : List Ty} {t : Ty} : Idx Γ t → ℕ
  | .zero => 0
  | .succ i => i.toNat + 1

/-- Typed environments. -/
inductive Env : List Ty → Type
  | nil : Env []
  | cons {t : Ty} {Γ : List Ty} : t.den → Env Γ → Env (t :: Γ)

namespace Env

def get {Γ : List Ty} {t : Ty} : Env Γ → Idx Γ t → t.den
  | .cons x _, .zero => x
  | .cons _ ρ, .succ i => ρ.get i

def enc : {Γ : List Ty} → Env Γ → List Val
  | [], .nil => []
  | _ :: _, .cons x ρ => Ty.enc _ x :: ρ.enc

theorem enc_get {Γ : List Ty} {t : Ty} (ρ : Env Γ) (i : Idx Γ t) :
    ρ.enc[i.toNat]? = some (t.enc (ρ.get i)) := by
  induction i with
  | zero => cases ρ; rfl
  | succ i ih => cases ρ; simp [enc, get, Idx.toNat, ih]

end Env

/-- A global function: its index in the program, its meaning, and its resource bounds. -/
structure FnSig (a b : Ty) where
  idx : ℕ
  den : a.den → b.den
  cost : a.den → ℕ
  depth : a.den → ℕ
  msize : a.den → ℕ

/-- The contract of `F` at the argument `x`: for every budget `m ≥ F.msize x`, the call
evaluates to the encoded result within the bounds. -/
def FnSig.ValidAt {a b : Ty} (P : Program) (F : FnSig a b) (x : a.den) : Prop :=
  ∀ m, F.msize x ≤ m → ∃ t d, t ≤ F.cost x ∧ d ≤ F.depth x ∧
    EvalCall P m F.idx (a.enc x) (b.enc (F.den x)) t d

/-- Typed terms. `ite c x y` is `if c then x else y`; `lcase` and `ncase` bind
(head, tail) and (low bit, half) respectively. -/
inductive Tm : List Ty → Ty → Type
  | var {Γ : List Ty} {t : Ty} : Idx Γ t → Tm Γ t
  | val {Γ : List Ty} : Val → Tm Γ .val
  | lit {Γ : List Ty} {t : Ty} : t.den → Tm Γ t
  | unit {Γ : List Ty} : Tm Γ .unit
  | ff {Γ : List Ty} : Tm Γ .bool
  | tt {Γ : List Ty} : Tm Γ .bool
  | zero {Γ : List Ty} : Tm Γ .nat
  | pair {Γ : List Ty} {a b : Ty} : Tm Γ a → Tm Γ b → Tm Γ (.prod a b)
  | fst {Γ : List Ty} {a b : Ty} : Tm Γ (.prod a b) → Tm Γ a
  | snd {Γ : List Ty} {a b : Ty} : Tm Γ (.prod a b) → Tm Γ b
  | ite {Γ : List Ty} {t : Ty} : Tm Γ .bool → Tm Γ t → Tm Γ t → Tm Γ t
  | lnil {Γ : List Ty} {t : Ty} : Tm Γ (.list t)
  | lcons {Γ : List Ty} {t : Ty} : Tm Γ t → Tm Γ (.list t) → Tm Γ (.list t)
  | lcase {Γ : List Ty} {t u : Ty} :
      Tm Γ (.list t) → Tm Γ u → Tm (t :: .list t :: Γ) u → Tm Γ u
  | ncase {Γ : List Ty} {u : Ty} : Tm Γ .nat → Tm Γ u → Tm (.bool :: .nat :: Γ) u → Tm Γ u
  | bit {Γ : List Ty} : Tm Γ .bool → Tm Γ .nat → Tm Γ .nat
  | letE {Γ : List Ty} {s t : Ty} : Tm Γ s → Tm (s :: Γ) t → Tm Γ t
  | app {Γ : List Ty} {a b : Ty} : FnSig a b → Tm Γ a → Tm Γ b

/-- `bit b n = 2 n + b`, normalised so that `0` stays `0` (the encoding has no trailing
zero digit). -/
def bitNat (b : Bool) (n : ℕ) : ℕ := 2 * n + (if b then 1 else 0)

/-- A literal value as an FL expression. -/
def Val.expr : Val → Expr
  | .nil => .nil
  | .cons a b => .cons a.expr b.expr

namespace Tm

def compile {Γ : List Ty} {t : Ty} : Tm Γ t → Expr
  | var i => .var i.toNat
  | val v => v.expr
  | lit x => (Ty.enc _ x).expr
  | unit => .nil
  | ff => .nil
  | tt => .cons .nil .nil
  | zero => .nil
  | pair a b => .cons a.compile b.compile
  | fst p => .fst p.compile
  | snd p => .snd p.compile
  | ite c x y => .cond c.compile y.compile x.compile
  | lnil => .nil
  | lcons h tl => .cons h.compile tl.compile
  | lcase s e₁ e₂ => .case s.compile e₁.compile e₂.compile
  | ncase s e₁ e₂ => .case s.compile e₁.compile e₂.compile
  | bit b n => .cond n.compile (.cond b.compile .nil (.cons (.cons .nil .nil) .nil))
      (.cons b.compile n.compile)
  | letE a b => .letE a.compile b.compile
  | app F a => .call F.idx a.compile

end Tm

namespace Tm

/-! ## Meaning and bounds -/

def den {Γ : List Ty} {t : Ty} : Tm Γ t → Env Γ → t.den
  | var i, ρ => ρ.get i
  | val v, _ => v
  | lit x, _ => x
  | unit, _ => ()
  | ff, _ => false
  | tt, _ => true
  | zero, _ => (0 : ℕ)
  | pair a b, ρ => (a.den ρ, b.den ρ)
  | fst p, ρ => (p.den ρ).1
  | snd p, ρ => (p.den ρ).2
  | ite c x y, ρ => if c.den ρ then x.den ρ else y.den ρ
  | lnil, _ => []
  | lcons h tl, ρ => h.den ρ :: tl.den ρ
  | lcase s e₁ e₂, ρ =>
      match s.den ρ with
      | [] => e₁.den ρ
      | h :: tl => e₂.den (.cons h (.cons tl ρ))
  | ncase s e₁ e₂, ρ =>
      if s.den ρ = 0 then e₁.den ρ
      else e₂.den (.cons (decide (s.den ρ % 2 = 1)) (.cons (s.den ρ / 2) ρ))
  | bit b n, ρ => bitNat (b.den ρ) (n.den ρ)
  | letE a b, ρ => b.den (.cons (a.den ρ) ρ)
  | app F a, ρ => F.den (a.den ρ)

/-- Upper bound on the evaluation cost. -/
def cost {Γ : List Ty} {t : Ty} : Tm Γ t → Env Γ → ℕ
  | var _, _ => 1
  | val v, _ => v.size
  | lit x, _ => (Ty.enc _ x).size
  | unit, _ => 1
  | ff, _ => 1
  | tt, _ => 3
  | zero, _ => 1
  | pair a b, ρ => a.cost ρ + b.cost ρ + 1
  | fst p, ρ => p.cost ρ + 1
  | snd p, ρ => p.cost ρ + 1
  | ite c x y, ρ => c.cost ρ + (if c.den ρ then x.cost ρ else y.cost ρ) + 1
  | lnil, _ => 1
  | lcons h tl, ρ => h.cost ρ + tl.cost ρ + 1
  | lcase s e₁ e₂, ρ =>
      s.cost ρ + (match s.den ρ with
        | [] => e₁.cost ρ
        | h :: tl => e₂.cost (.cons h (.cons tl ρ))) + 1
  | ncase s e₁ e₂, ρ =>
      s.cost ρ + (if s.den ρ = 0 then e₁.cost ρ
        else e₂.cost (.cons (decide (s.den ρ % 2 = 1)) (.cons (s.den ρ / 2) ρ))) + 1
  | bit b n, ρ => 2 * n.cost ρ + b.cost ρ + 8
  | letE a b, ρ => a.cost ρ + b.cost (.cons (a.den ρ) ρ) + 1
  | app F a, ρ => a.cost ρ + F.cost (a.den ρ)

/-- Upper bound on the call depth. -/
def depth {Γ : List Ty} {t : Ty} : Tm Γ t → Env Γ → ℕ
  | var _, _ => 0
  | val _, _ => 0
  | lit _, _ => 0
  | unit, _ => 0
  | ff, _ => 0
  | tt, _ => 0
  | zero, _ => 0
  | pair a b, ρ => max (a.depth ρ) (b.depth ρ)
  | fst p, ρ => p.depth ρ
  | snd p, ρ => p.depth ρ
  | ite c x y, ρ => max (c.depth ρ) (if c.den ρ then x.depth ρ else y.depth ρ)
  | lnil, _ => 0
  | lcons h tl, ρ => max (h.depth ρ) (tl.depth ρ)
  | lcase s e₁ e₂, ρ =>
      max (s.depth ρ) (match s.den ρ with
        | [] => e₁.depth ρ
        | h :: tl => e₂.depth (.cons h (.cons tl ρ)))
  | ncase s e₁ e₂, ρ =>
      max (s.depth ρ) (if s.den ρ = 0 then e₁.depth ρ
        else e₂.depth (.cons (decide (s.den ρ % 2 = 1)) (.cons (s.den ρ / 2) ρ)))
  | bit b n, ρ => max (b.depth ρ) (n.depth ρ)
  | letE a b, ρ => max (a.depth ρ) (b.depth (.cons (a.den ρ) ρ))
  | app F a, ρ => max (a.depth ρ) (F.depth (a.den ρ))

/-- Size budget sufficient for the evaluation. -/
def msize {Γ : List Ty} {t : Ty} : Tm Γ t → Env Γ → ℕ
  | var _, _ => 0
  | val v, _ => v.size
  | lit x, _ => (Ty.enc _ x).size
  | unit, _ => 0
  | ff, _ => 0
  | tt, _ => 3
  | zero, _ => 0
  | pair a b, ρ => max (max (a.msize ρ) (b.msize ρ)) ((Ty.enc _ ((pair a b).den ρ)).size)
  | fst p, ρ => p.msize ρ
  | snd p, ρ => p.msize ρ
  | ite c x y, ρ => max (c.msize ρ) (if c.den ρ then x.msize ρ else y.msize ρ)
  | lnil, _ => 0
  | lcons h tl, ρ => max (max (h.msize ρ) (tl.msize ρ)) ((Ty.enc _ ((lcons h tl).den ρ)).size)
  | lcase s e₁ e₂, ρ =>
      max (s.msize ρ) (match s.den ρ with
        | [] => e₁.msize ρ
        | h :: tl => e₂.msize (.cons h (.cons tl ρ)))
  | ncase s e₁ e₂, ρ =>
      max (s.msize ρ) (if s.den ρ = 0 then e₁.msize ρ
        else e₂.msize (.cons (decide (s.den ρ % 2 = 1)) (.cons (s.den ρ / 2) ρ)))
  | bit b n, ρ => max (max (b.msize ρ) (n.msize ρ)) (max 5 (Enc.nat (bitNat (b.den ρ) (n.den ρ))).size)
  | letE a b, ρ => max (a.msize ρ) (b.msize (.cons (a.den ρ) ρ))
  | app F a, ρ => max (a.msize ρ) (F.msize (a.den ρ))

/-- Every call made while evaluating the term satisfies its contract at its actual argument. -/
def CallsOK (P : Program) {Γ : List Ty} {t : Ty} : Tm Γ t → Env Γ → Prop
  | var _, _ => True
  | val _, _ => True
  | lit _, _ => True
  | unit, _ => True
  | ff, _ => True
  | tt, _ => True
  | zero, _ => True
  | pair a b, ρ => a.CallsOK P ρ ∧ b.CallsOK P ρ
  | fst p, ρ => p.CallsOK P ρ
  | snd p, ρ => p.CallsOK P ρ
  | ite c x y, ρ => c.CallsOK P ρ ∧ (if c.den ρ then x.CallsOK P ρ else y.CallsOK P ρ)
  | lnil, _ => True
  | lcons h tl, ρ => h.CallsOK P ρ ∧ tl.CallsOK P ρ
  | lcase s e₁ e₂, ρ =>
      s.CallsOK P ρ ∧ (match s.den ρ with
        | [] => e₁.CallsOK P ρ
        | h :: tl => e₂.CallsOK P (.cons h (.cons tl ρ)))
  | ncase s e₁ e₂, ρ =>
      s.CallsOK P ρ ∧ (if s.den ρ = 0 then e₁.CallsOK P ρ
        else e₂.CallsOK P (.cons (decide (s.den ρ % 2 = 1)) (.cons (s.den ρ / 2) ρ)))
  | bit b n, ρ => b.CallsOK P ρ ∧ n.CallsOK P ρ
  | letE a b, ρ => a.CallsOK P ρ ∧ b.CallsOK P (.cons (a.den ρ) ρ)
  | app F a, ρ => a.CallsOK P ρ ∧ F.ValidAt P (a.den ρ)

end Tm

/-! ## The evaluation theorem -/

theorem Val.expr_eval {P : Program} {m : ℕ} {env : List Val} (v : Val) (hv : v.size ≤ m) :
    Eval P m env v.expr v v.size 0 := by
  induction v with
  | nil => exact .nil
  | cons a b iha ihb =>
    have ha : a.size ≤ m := by simp at hv; omega
    have hb : b.size ≤ m := by simp at hv; omega
    have h := Eval.cons (iha ha) (ihb hb) hv
    have e : a.size + b.size + 1 = (Val.cons a b).size := by simp; omega
    rw [e] at h
    simpa [Val.expr] using h

theorem Enc.nat_bitNat (b : Bool) (n : ℕ) :
    Enc.nat (bitNat b n) =
      if n = 0 then (if b then .cons (.cons .nil .nil) .nil else .nil)
      else .cons (Enc.bool b) (Enc.nat n) := by
  by_cases hn : n = 0
  · subst hn
    cases b
    · simp [bitNat, Enc.nat_zero]
    · rw [show bitNat true 0 = 1 by rfl, Enc.nat_pos (by omega)]
      simp [Enc.nat_zero, Enc.bool]
  · have hpos : bitNat b n ≠ 0 := by unfold bitNat; omega
    rw [Enc.nat_pos hpos, if_neg hn]
    have h1 : bitNat b n / 2 = n := by unfold bitNat; split <;> omega
    have h2 : decide (bitNat b n % 2 = 1) = b := by unfold bitNat; cases b <;> simp
    rw [h1, h2]

namespace Tm
variable {P : Program}

theorem eval {Γ : List Ty} {t : Ty} (tm : Tm Γ t) (ρ : Env Γ) (m : ℕ)
    (hok : tm.CallsOK P ρ) (hm : tm.msize ρ ≤ m) :
    ∃ c d, c ≤ tm.cost ρ ∧ d ≤ tm.depth ρ ∧
      Eval P m ρ.enc tm.compile (t.enc (tm.den ρ)) c d := by
  induction tm generalizing m with
  | var i => exact ⟨1, 0, (by simp only [cost]; exact Nat.le_refl _), Nat.zero_le _, Eval.var (Env.enc_get ρ i)⟩
  | val v => exact ⟨v.size, 0, (by simp only [cost]; exact Nat.le_refl _), Nat.zero_le _, Val.expr_eval v hm⟩
  | lit x => exact ⟨_, 0, (by simp only [cost]; exact Nat.le_refl _), Nat.zero_le _, Val.expr_eval (Ty.enc _ x) hm⟩
  | unit => exact ⟨1, 0, (by simp only [cost]; exact Nat.le_refl _), Nat.zero_le _, Eval.nil⟩
  | ff => exact ⟨1, 0, (by simp only [cost]; exact Nat.le_refl _), Nat.zero_le _, Eval.nil⟩
  | tt => exact ⟨3, 0, (by simp only [cost]; exact Nat.le_refl _), Nat.zero_le _, Eval.cons Eval.nil Eval.nil (by simpa [msize] using hm)⟩
  | zero =>
    refine ⟨1, 0, (by simp only [cost]; exact Nat.le_refl _), Nat.zero_le _, ?_⟩
    simp only [den, Ty.enc, compile, Enc.nat_zero]
    exact Eval.nil
  | pair a b iha ihb =>
    simp only [msize, Nat.max_le] at hm
    obtain ⟨ca, da, hca, hda, ea⟩ := iha ρ m hok.1 hm.1.1
    obtain ⟨cb, db, hcb, hdb, eb⟩ := ihb ρ m hok.2 hm.1.2
    exact ⟨ca + cb + 1, max da db, by simp [cost]; omega, by simp [depth]; omega,
      Eval.cons ea eb hm.2⟩
  | fst p ih =>
    obtain ⟨c, d, hc, hd, e⟩ := ih ρ m hok hm
    exact ⟨c + 1, d, by simp [cost]; omega, by simpa [depth] using hd, Eval.fst e⟩
  | snd p ih =>
    obtain ⟨c, d, hc, hd, e⟩ := ih ρ m hok hm
    exact ⟨c + 1, d, by simp [cost]; omega, by simpa [depth] using hd, Eval.snd e⟩
  | ite c x y ihc ihx ihy =>
    simp only [msize, Nat.max_le] at hm
    obtain ⟨cc, dc, hcc, hdc, ec⟩ := ihc ρ m hok.1 hm.1
    have hok2 := hok.2
    cases hb : c.den ρ
    · simp only [hb] at hm hok2 ec
      obtain ⟨cy, dy, hcy, hdy, ey⟩ := ihy ρ m hok2 (by simpa using hm.2)
      refine ⟨cc + cy + 1, max dc dy, by simp [cost, hb]; omega, by simp [depth, hb]; omega, ?_⟩
      simpa [den, hb, compile] using Eval.condNil (e₂ := x.compile) ec ey
    · simp only [hb] at hm hok2 ec
      obtain ⟨cx, dx, hcx, hdx, ex⟩ := ihx ρ m hok2 (by simpa using hm.2)
      refine ⟨cc + cx + 1, max dc dx, by simp [cost, hb]; omega, by simp [depth, hb]; omega, ?_⟩
      simpa [den, hb, compile] using Eval.condCons (e₁ := y.compile) ec ex
  | lnil => exact ⟨1, 0, (by simp only [cost]; exact Nat.le_refl _), Nat.zero_le _, Eval.nil⟩
  | lcons h tl ihh iht =>
    simp only [msize, Nat.max_le] at hm
    obtain ⟨ch, dh, hch, hdh, eh⟩ := ihh ρ m hok.1 hm.1.1
    obtain ⟨ct, dt, hct, hdt, et⟩ := iht ρ m hok.2 hm.1.2
    exact ⟨ch + ct + 1, max dh dt, by simp [cost]; omega, by simp [depth]; omega,
      Eval.cons eh et hm.2⟩
  | lcase s e₁ e₂ ihs ih₁ ih₂ =>
    simp only [msize, Nat.max_le] at hm
    obtain ⟨cs, ds, hcs, hds, es⟩ := ihs ρ m hok.1 hm.1
    have hok2 := hok.2
    cases hl : s.den ρ with
    | nil =>
      simp only [hl] at hm hok2 es
      obtain ⟨c₁, d₁, hc₁, hd₁, ev₁⟩ := ih₁ ρ m hok2 hm.2
      refine ⟨cs + c₁ + 1, max ds d₁, by simp [cost, hl]; omega, by simp [depth, hl]; omega, ?_⟩
      simpa [den, hl, compile] using Eval.caseNil (e₂ := e₂.compile) es ev₁
    | cons h tl =>
      simp only [hl] at hm hok2 es
      obtain ⟨c₂, d₂, hc₂, hd₂, ev₂⟩ := ih₂ (.cons h (.cons tl ρ)) m hok2 hm.2
      refine ⟨cs + c₂ + 1, max ds d₂, by simp [cost, hl]; omega, by simp [depth, hl]; omega, ?_⟩
      simpa [den, hl, compile] using Eval.caseCons (e₁ := e₁.compile) es ev₂
  | ncase s e₁ e₂ ihs ih₁ ih₂ =>
    simp only [msize, Nat.max_le] at hm
    obtain ⟨cs, ds, hcs, hds, es⟩ := ihs ρ m hok.1 hm.1
    have hok2 := hok.2
    by_cases hn : s.den ρ = 0
    · simp only [hn, if_true] at hm hok2
      obtain ⟨c₁, d₁, hc₁, hd₁, ev₁⟩ := ih₁ ρ m hok2 hm.2
      have es' : Eval P m ρ.enc s.compile .nil cs ds := by
        simpa [Ty.enc, hn, Enc.nat_zero] using es
      refine ⟨cs + c₁ + 1, max ds d₁, by simp [cost, hn]; omega, by simp [depth, hn]; omega, ?_⟩
      simpa [den, hn, compile] using Eval.caseNil (e₂ := e₂.compile) es' ev₁
    · simp only [hn, if_false] at hm hok2
      obtain ⟨c₂, d₂, hc₂, hd₂, ev₂⟩ := ih₂ _ m hok2 hm.2
      have es' : Eval P m ρ.enc s.compile
          (.cons (Enc.bool (decide (s.den ρ % 2 = 1))) (Enc.nat (s.den ρ / 2))) cs ds := by
        simpa [Ty.enc, Enc.nat_pos hn] using es
      refine ⟨cs + c₂ + 1, max ds d₂, by simp [cost, hn]; omega, by simp [depth, hn]; omega, ?_⟩
      simpa [den, hn, compile] using Eval.caseCons (e₁ := e₁.compile) es' ev₂
  | bit b n ihb ihn =>
    simp only [msize, Nat.max_le] at hm
    obtain ⟨cb, db, hcb, hdb, eb⟩ := ihb ρ m hok.1 hm.1.1
    obtain ⟨cn, dn, hcn, hdn, en⟩ := ihn ρ m hok.2 hm.1.2
    by_cases hn : n.den ρ = 0
    · have en' : Eval P m ρ.enc n.compile .nil cn dn := by
        simpa [Ty.enc, hn, Enc.nat_zero] using en
      cases hbv : b.den ρ
      · have eb' : Eval P m ρ.enc b.compile .nil cb db := by simpa [Ty.enc, hbv, Enc.bool] using eb
        have inner := Eval.condNil (e₂ := Expr.cons (.cons .nil .nil) .nil) eb' (Eval.nil (P := P)
          (m := m) (env := ρ.enc))
        have h := Eval.condNil (e₂ := Expr.cons b.compile n.compile) en' inner
        refine ⟨cn + (cb + 1 + 1) + 1, max dn (max db 0), by simp [cost]; omega,
          by simp [depth]; omega, ?_⟩
        simpa [den, compile, hn, hbv, Enc.nat_bitNat, Ty.enc] using h
      · have eb' : Eval P m ρ.enc b.compile (.cons .nil .nil) cb db := by
          simpa [Ty.enc, hbv, Enc.bool] using eb
        have h5 : (Val.cons (.cons .nil .nil) .nil).size ≤ m := by simp; omega
        have h3 : (Val.cons .nil .nil).size ≤ m := by simp; omega
        have lit : Eval P m ρ.enc (Expr.cons (.cons .nil .nil) .nil) (.cons (.cons .nil .nil) .nil)
            5 0 := by
          simpa using Eval.cons (Eval.cons Eval.nil Eval.nil h3) Eval.nil h5
        have inner := Eval.condCons (e₁ := Expr.nil) eb' lit
        have h := Eval.condNil (e₂ := Expr.cons b.compile n.compile) en' inner
        refine ⟨cn + (cb + 5 + 1) + 1, max dn (max db 0), by simp [cost]; omega,
          by simp [depth]; omega, ?_⟩
        simpa [den, compile, hn, hbv, Enc.nat_bitNat, Ty.enc] using h
    · have hval : Ty.enc .nat (bitNat (b.den ρ) (n.den ρ)) =
          .cons (Ty.enc .bool (b.den ρ)) (Ty.enc .nat (n.den ρ)) := by
        simp [Ty.enc, Enc.nat_bitNat, hn]
      have en' : Eval P m ρ.enc n.compile
          (.cons (Enc.bool (decide (n.den ρ % 2 = 1))) (Enc.nat (n.den ρ / 2))) cn dn := by
        simpa [Ty.enc, Enc.nat_pos hn] using en
      have hsz : (Val.cons (Ty.enc .bool (b.den ρ)) (Ty.enc .nat (n.den ρ))).size ≤ m := by
        rw [← hval]; exact hm.2.2
      have h := Eval.condCons
        (e₁ := Expr.cond b.compile .nil (.cons (.cons .nil .nil) .nil)) en' (Eval.cons eb en hsz)
      refine ⟨cn + (cb + cn + 1) + 1, max dn (max db dn), by simp [cost]; omega,
        by simp [depth]; omega, ?_⟩
      rw [show (bit b n).den ρ = bitNat (b.den ρ) (n.den ρ) from rfl, hval]; exact h
  | letE a b iha ihb =>
    simp only [msize, Nat.max_le] at hm
    obtain ⟨ca, da, hca, hda, ea⟩ := iha ρ m hok.1 hm.1
    obtain ⟨cb, db, hcb, hdb, eb⟩ := ihb (.cons (a.den ρ) ρ) m hok.2 hm.2
    exact ⟨ca + cb + 1, max da db, by simp [cost]; omega, by simp [depth]; omega, Eval.letE ea eb⟩
  | app F a iha =>
    simp only [msize, Nat.max_le] at hm
    obtain ⟨ca, da, hca, hda, ea⟩ := iha ρ m hok.1 hm.1
    obtain ⟨c, d, hc, hd, ecall⟩ := hok.2 m hm.2
    cases ecall with
    | @call _ _ _ body va _ ta tb da' db hv hbody hb =>
      cases hv with
      | var hx =>
        simp at hx
        subst hx
        refine ⟨ca + tb + 1, max da (db + 1), by simp [cost]; omega, ?_, Eval.call ea hbody hb⟩
        simp only [depth]
        omega

end Tm

end QecReliability.FL
