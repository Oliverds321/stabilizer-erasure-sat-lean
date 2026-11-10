import Trans.Control.Types

/-!
# Trans.Control.Base: body signatures, term helpers, field accessors

* `bodySig i body`: the signature whose meaning *is* the body's denotation and whose bounds
  are exactly the body's compositional bounds (`cost = body.cost + 2`, …). Its contract only
  needs the body's calls (`bodySig_valid`); the meaning is related to the Lean controller by
  separate correctness theorems, and closed-form bounds by separate lemmas.
* Tuple helpers `mk5 … mk8`, positional projections `p0 … p7`.
* The context `TCtx TX = (q, r, B, m) × X` (`X : TX` is the external data, opaque here).
* Field accessors `F.pc … F.mad` on a configuration term, and record builders
  `g0With … g6With`, `cfgWith` with defaults = the old fields (so a body lists only the
  fields it changes).
-/

set_option autoImplicit false

/-- Simp set unfolding the controller transcription (bodies, encodings, the Lean step). -/
register_simp_attr ctl_simp

namespace QecReliability.Trans.Control
open QecReliability.FL

/-! ## Signatures given by their bodies -/

def bodySig {a b : Ty} (i : ℕ) (body : Tm [a] b) : FnSig a b where
  idx := i
  den x := body.den (Env.one x)
  cost x := body.cost (Env.one x) + 2
  depth x := body.depth (Env.one x) + 1
  msize x := body.msize (Env.one x)

@[simp] theorem bodySig_idx {a b : Ty} (i : ℕ) (body : Tm [a] b) : (bodySig i body).idx = i := rfl
theorem bodySig_den {a b : Ty} (i : ℕ) (body : Tm [a] b) (x : a.den) :
    (bodySig i body).den x = body.den (Env.one x) := rfl
theorem bodySig_cost {a b : Ty} (i : ℕ) (body : Tm [a] b) (x : a.den) :
    (bodySig i body).cost x = body.cost (Env.one x) + 2 := rfl
theorem bodySig_depth {a b : Ty} (i : ℕ) (body : Tm [a] b) (x : a.den) :
    (bodySig i body).depth x = body.depth (Env.one x) + 1 := rfl
theorem bodySig_msize {a b : Ty} (i : ℕ) (body : Tm [a] b) (x : a.den) :
    (bodySig i body).msize x = body.msize (Env.one x) := rfl

theorem bodySig_valid {a b : Ty} {P : Program} {i : ℕ} {body : Tm [a] b}
    (hP : P[i]? = some body.compile) {x : a.den} (h : body.CallsOK P (Env.one x)) :
    (bodySig i body).ValidAt P x :=
  FnSig.validAt_of_bodyOK hP ⟨h, rfl, le_refl _, le_refl _, le_refl _⟩

/-! ## Tuples -/

namespace Tm
variable {Γ : List Ty}

abbrev mk5 {a b c d e : Ty} (x₀ : Tm Γ a) (x₁ : Tm Γ b) (x₂ : Tm Γ c) (x₃ : Tm Γ d)
    (x₄ : Tm Γ e) : Tm Γ (.prod a (.prod b (.prod c (.prod d e)))) :=
  .pair x₀ (.pair x₁ (.pair x₂ (.pair x₃ x₄)))
abbrev mk6 {a b c d e f : Ty} (x₀ : Tm Γ a) (x₁ : Tm Γ b) (x₂ : Tm Γ c) (x₃ : Tm Γ d)
    (x₄ : Tm Γ e) (x₅ : Tm Γ f) : Tm Γ (.prod a (.prod b (.prod c (.prod d (.prod e f))))) :=
  .pair x₀ (mk5 x₁ x₂ x₃ x₄ x₅)
abbrev mk7 {a b c d e f g : Ty} (x₀ : Tm Γ a) (x₁ : Tm Γ b) (x₂ : Tm Γ c) (x₃ : Tm Γ d)
    (x₄ : Tm Γ e) (x₅ : Tm Γ f) (x₆ : Tm Γ g) :
    Tm Γ (.prod a (.prod b (.prod c (.prod d (.prod e (.prod f g)))))) :=
  .pair x₀ (mk6 x₁ x₂ x₃ x₄ x₅ x₆)
abbrev mk8 {a b c d e f g h : Ty} (x₀ : Tm Γ a) (x₁ : Tm Γ b) (x₂ : Tm Γ c) (x₃ : Tm Γ d)
    (x₄ : Tm Γ e) (x₅ : Tm Γ f) (x₆ : Tm Γ g) (x₇ : Tm Γ h) :
    Tm Γ (.prod a (.prod b (.prod c (.prod d (.prod e (.prod f (.prod g h))))))) :=
  .pair x₀ (mk7 x₁ x₂ x₃ x₄ x₅ x₆ x₇)

/-- `k`-th component of a right-nested tuple, and the last components `q1 … q7`. -/
abbrev p0 {a b : Ty} (x : Tm Γ (.prod a b)) : Tm Γ a := .fst x
abbrev q1 {a b : Ty} (x : Tm Γ (.prod a b)) : Tm Γ b := .snd x
abbrev p1 {a b c : Ty} (x : Tm Γ (.prod a (.prod b c))) : Tm Γ b := .fst (.snd x)
abbrev q2 {a b c : Ty} (x : Tm Γ (.prod a (.prod b c))) : Tm Γ c := .snd (.snd x)
abbrev p2 {a b c d : Ty} (x : Tm Γ (.prod a (.prod b (.prod c d)))) : Tm Γ c := .fst (q2 x)
abbrev q3 {a b c d : Ty} (x : Tm Γ (.prod a (.prod b (.prod c d)))) : Tm Γ d := .snd (q2 x)
abbrev p3 {a b c d e : Ty} (x : Tm Γ (.prod a (.prod b (.prod c (.prod d e))))) : Tm Γ d :=
  .fst (q3 x)
abbrev q4 {a b c d e : Ty} (x : Tm Γ (.prod a (.prod b (.prod c (.prod d e))))) : Tm Γ e :=
  .snd (q3 x)
abbrev p4 {a b c d e f : Ty} (x : Tm Γ (.prod a (.prod b (.prod c (.prod d (.prod e f)))))) :
    Tm Γ e := .fst (q4 x)
abbrev q5 {a b c d e f : Ty} (x : Tm Γ (.prod a (.prod b (.prod c (.prod d (.prod e f)))))) :
    Tm Γ f := .snd (q4 x)
abbrev p5 {a b c d e f g : Ty}
    (x : Tm Γ (.prod a (.prod b (.prod c (.prod d (.prod e (.prod f g))))))) : Tm Γ f :=
  .fst (q5 x)
abbrev q6 {a b c d e f g : Ty}
    (x : Tm Γ (.prod a (.prod b (.prod c (.prod d (.prod e (.prod f g))))))) : Tm Γ g :=
  .snd (q5 x)
abbrev p6 {a b c d e f g h : Ty}
    (x : Tm Γ (.prod a (.prod b (.prod c (.prod d (.prod e (.prod f (.prod g h)))))))) :
    Tm Γ g := .fst (q6 x)
abbrev q7 {a b c d e f g h : Ty}
    (x : Tm Γ (.prod a (.prod b (.prod c (.prod d (.prod e (.prod f (.prod g h)))))))) :
    Tm Γ h := .snd (q6 x)

end Tm

/-! ## Context and arguments -/

/-- Context: `((q, r, B, m), X)`. -/
abbrev TCtx (TX : Ty) : Ty := .prod (.prod .nat (.prod .nat (.prod .nat .nat))) TX
/-- Argument of a controller step: `(context, configuration)`. -/
abbrev TArg (TX : Ty) : Ty := .prod (TCtx TX) TCfg

/-! ## Field accessors on configuration terms -/

namespace F
open Tm
variable {Γ : List Ty} (c : Tm Γ TCfg)

abbrev g0 : Tm Γ TG0 := p0 c
abbrev g1 : Tm Γ TG1 := p1 c
abbrev g2 : Tm Γ TG2 := p2 c
abbrev g3 : Tm Γ TG3 := p3 c
abbrev g4 : Tm Γ TG4 := p4 c
abbrev g5 : Tm Γ TG5 := p5 c
abbrev g6 : Tm Γ TG6 := q6 c

abbrev pc : Tm Γ .nat := p0 (g0 c)
abbrev code : Tm Γ (.list TOp) := p1 (g0 c)
abbrev good : Tm Γ .bool := p2 (g0 c)
abbrev coef : Tm Γ .nat := p3 (g0 c)
abbrev rep : Tm Γ .nat := p4 (g0 c)
abbrev scale : Tm Γ .nat := p5 (g0 c)
abbrev nonempty : Tm Γ .bool := p6 (g0 c)
abbrev tag : Tm Γ .bool := q7 (g0 c)

abbrev request : Tm Γ TKey := p0 (g1 c)
abbrev query : Tm Γ (.list .bool) := p1 (g1 c)
abbrev reply : Tm Γ .bool := p2 (g1 c)
abbrev pre : Tm Γ TPre := p3 (g1 c)
abbrev cellCalls : Tm Γ .nat := p4 (g1 c)
abbrev trialCalls : Tm Γ .nat := p5 (g1 c)
abbrev coefCalls : Tm Γ .nat := q6 (g1 c)

abbrev cellsRev : Tm Γ (.list TEnt) := p0 (g2 c)
abbrev pairSrc : Tm Γ (.list TEnt) := p1 (g2 c)
abbrev pairDst : Tm Γ (.list TEnt) := p2 (g2 c)
abbrev trialsRev : Tm Γ (.list TEnt) := p3 (g2 c)
abbrev selected : Tm Γ .nat := p4 (g2 c)
abbrev selectIndex : Tm Γ .nat := p5 (g2 c)
abbrev scaleFactor : Tm Γ .nat := q6 (g2 c)

abbrev sortTodo : Tm Γ (.list .nat) := p0 (g3 c)
abbrev sorted : Tm Γ (.list .nat) := p1 (g3 c)
abbrev insertValue : Tm Γ .nat := p2 (g3 c)
abbrev insertLeftRev : Tm Γ (.list .nat) := p3 (g3 c)
abbrev insertRight : Tm Γ (.list .nat) := p4 (g3 c)
abbrev insertResult : Tm Γ (.list .nat) := p5 (g3 c)
abbrev lookupRemaining : Tm Γ .nat := q6 (g3 c)

abbrev goodRev : Tm Γ (.list TEnt) := p0 (g4 c)
abbrev badRev : Tm Γ (.list TEnt) := p1 (g4 c)
abbrev goodTable : Tm Γ (.list TEnt) := p2 (g4 c)
abbrev badTable : Tm Γ (.list TEnt) := p3 (g4 c)
abbrev repairGood : Tm Γ (.list TEnt) := p4 (g4 c)
abbrev repairBad : Tm Γ (.list TEnt) := q5 (g4 c)

abbrev endpoint0 : Tm Γ TR := p0 (g5 c)
abbrev endpoint1 : Tm Γ TR := p1 (g5 c)
abbrev previous : Tm Γ TR := p2 (g5 c)
abbrev repairIndex : Tm Γ .nat := p3 (g5 c)
abbrev outputRev : Tm Γ (.list TR) := p4 (g5 c)
abbrev output : Tm Γ (.list TR) := q5 (g5 c)

abbrev pairVisits : Tm Γ .nat := p0 (g6 c)
abbrev ratioBuilds : Tm Γ .nat := p1 (g6 c)
abbrev orderComparisons : Tm Γ .nat := p2 (g6 c)
abbrev endpointTests : Tm Γ .nat := p3 (g6 c)
abbrev mad : Tm Γ .nat := q4 (g6 c)

/-! Record builders: every field defaults to the old one. -/

abbrev g0With (pc : Tm Γ .nat := pc c) (code : Tm Γ (.list TOp) := code c)
    (good : Tm Γ .bool := good c) (coef : Tm Γ .nat := coef c) (rep : Tm Γ .nat := rep c)
    (scale : Tm Γ .nat := scale c) (nonempty : Tm Γ .bool := nonempty c)
    (tag : Tm Γ .bool := tag c) : Tm Γ TG0 :=
  mk8 pc code good coef rep scale nonempty tag

abbrev g1With (request : Tm Γ TKey := request c) (query : Tm Γ (.list .bool) := query c)
    (reply : Tm Γ .bool := reply c) (pre : Tm Γ TPre := pre c)
    (cellCalls : Tm Γ .nat := cellCalls c) (trialCalls : Tm Γ .nat := trialCalls c)
    (coefCalls : Tm Γ .nat := coefCalls c) : Tm Γ TG1 :=
  mk7 request query reply pre cellCalls trialCalls coefCalls

abbrev g2With (cellsRev : Tm Γ (.list TEnt) := cellsRev c)
    (pairSrc : Tm Γ (.list TEnt) := pairSrc c) (pairDst : Tm Γ (.list TEnt) := pairDst c)
    (trialsRev : Tm Γ (.list TEnt) := trialsRev c) (selected : Tm Γ .nat := selected c)
    (selectIndex : Tm Γ .nat := selectIndex c) (scaleFactor : Tm Γ .nat := scaleFactor c) :
    Tm Γ TG2 :=
  mk7 cellsRev pairSrc pairDst trialsRev selected selectIndex scaleFactor

abbrev g3With (sortTodo : Tm Γ (.list .nat) := sortTodo c)
    (sorted : Tm Γ (.list .nat) := sorted c) (insertValue : Tm Γ .nat := insertValue c)
    (insertLeftRev : Tm Γ (.list .nat) := insertLeftRev c)
    (insertRight : Tm Γ (.list .nat) := insertRight c)
    (insertResult : Tm Γ (.list .nat) := insertResult c)
    (lookupRemaining : Tm Γ .nat := lookupRemaining c) : Tm Γ TG3 :=
  mk7 sortTodo sorted insertValue insertLeftRev insertRight insertResult lookupRemaining

abbrev g4With (goodRev : Tm Γ (.list TEnt) := goodRev c)
    (badRev : Tm Γ (.list TEnt) := badRev c) (goodTable : Tm Γ (.list TEnt) := goodTable c)
    (badTable : Tm Γ (.list TEnt) := badTable c)
    (repairGood : Tm Γ (.list TEnt) := repairGood c)
    (repairBad : Tm Γ (.list TEnt) := repairBad c) : Tm Γ TG4 :=
  mk6 goodRev badRev goodTable badTable repairGood repairBad

abbrev g5With (endpoint0 : Tm Γ TR := endpoint0 c) (endpoint1 : Tm Γ TR := endpoint1 c)
    (previous : Tm Γ TR := previous c) (repairIndex : Tm Γ .nat := repairIndex c)
    (outputRev : Tm Γ (.list TR) := outputRev c) (output : Tm Γ (.list TR) := output c) :
    Tm Γ TG5 :=
  mk6 endpoint0 endpoint1 previous repairIndex outputRev output

abbrev g6With (pairVisits : Tm Γ .nat := pairVisits c)
    (ratioBuilds : Tm Γ .nat := ratioBuilds c)
    (orderComparisons : Tm Γ .nat := orderComparisons c)
    (endpointTests : Tm Γ .nat := endpointTests c) (mad : Tm Γ .nat := mad c) : Tm Γ TG6 :=
  mk5 pairVisits ratioBuilds orderComparisons endpointTests mad

abbrev cfgWith (g0 : Tm Γ TG0 := g0 c) (g1 : Tm Γ TG1 := g1 c) (g2 : Tm Γ TG2 := g2 c)
    (g3 : Tm Γ TG3 := g3 c) (g4 : Tm Γ TG4 := g4 c) (g5 : Tm Γ TG5 := g5 c)
    (g6 : Tm Γ TG6 := g6 c) : Tm Γ TCfg :=
  mk7 g0 g1 g2 g3 g4 g5 g6

end F

/-! ## Context accessors on argument terms -/

namespace A
open Tm
variable {Γ : List Ty} {TX : Ty} (a : Tm Γ (TArg TX))

abbrev q : Tm Γ .nat := p0 (p0 (p0 a))
abbrev r : Tm Γ .nat := p1 (p0 (p0 a))
abbrev B : Tm Γ .nat := p2 (p0 (p0 a))
abbrev m : Tm Γ .nat := q3 (p0 (p0 a))
abbrev X : Tm Γ TX := q1 (p0 a)
abbrev cfg : Tm Γ TCfg := q1 a

end A

/-- The encoded context. -/
def encCtx {TX : Ty} (q r B m : ℕ) (X : TX.den) : (TCtx TX).den := ((q, r, B, m), X)

end QecReliability.Trans.Control

/-! ## Excess of the size budget over the result

`Tm.ex` collects the budgets of the *side* computations of a term (callee budgets, conditions,
scrutinees, let-bound values); constructing the result itself needs at most its own size:
`Tm.msize_le_ex : tm.msize ρ ≤ (t.enc (tm.den ρ)).size + tm.ex ρ`. For a body that builds its
result from projections, literals and calls, `ex` only sees the calls. -/

namespace QecReliability.Trans.Control
open QecReliability.FL

namespace Tm'
open Tm

def ex {Γ : List Ty} {t : Ty} : Tm Γ t → Env Γ → ℕ
  | .var _, _ => 0
  | .val _, _ => 0
  | .lit _, _ => 0
  | .unit, _ => 0
  | .ff, _ => 0
  | .tt, _ => 0
  | .zero, _ => 0
  | .pair a b, ρ => max (ex a ρ) (ex b ρ)
  | .fst p, ρ => p.msize ρ
  | .snd p, ρ => p.msize ρ
  | .ite c x y, ρ => max (c.msize ρ) (if c.den ρ then ex x ρ else ex y ρ)
  | .lnil, _ => 0
  | .lcons h tl, ρ => max (ex h ρ) (ex tl ρ)
  | .lcase s e₁ e₂, ρ =>
      max (s.msize ρ) (match s.den ρ with
        | [] => ex e₁ ρ
        | h :: tl => ex e₂ (.cons h (.cons tl ρ)))
  | .ncase s e₁ e₂, ρ =>
      max (s.msize ρ) (if s.den ρ = 0 then ex e₁ ρ
        else ex e₂ (.cons (decide (s.den ρ % 2 = 1)) (.cons (s.den ρ / 2) ρ)))
  | .bit b n, ρ => max (max (b.msize ρ) (n.msize ρ)) (max 5 (Enc.nat (bitNat (b.den ρ) (n.den ρ))).size)
  | .letE a b, ρ => max (a.msize ρ) (ex b (.cons (a.den ρ) ρ))
  | .app F a, ρ => max (a.msize ρ) (F.msize (a.den ρ))

theorem msize_le_ex {Γ : List Ty} {t : Ty} (tm : Tm Γ t) (ρ : Env Γ) :
    tm.msize ρ ≤ (t.enc (tm.den ρ)).size + ex tm ρ := by
  induction tm with
  | var => simp [msize, ex]
  | val v => simp [msize, ex, den]
  | lit x => simp [msize, ex, den]
  | unit => simp [msize, ex]
  | ff => simp [msize, ex]
  | tt => simp [msize, ex, den, Enc.bool]
  | zero => simp [msize, ex]
  | pair a b iha ihb =>
    have h1 := iha ρ; have h2 := ihb ρ
    simp only [msize, ex, den, Ty.enc_prod, Val.size_cons] at h1 h2 ⊢
    omega
  | fst p ih => simp [msize, ex]
  | snd p ih => simp [msize, ex]
  | ite c x y ihc ihx ihy =>
    have h1 := ihx ρ; have h2 := ihy ρ
    simp only [msize, ex, den]
    split <;> omega
  | lnil => simp [msize, ex]
  | lcons h tl ihh iht =>
    have h1 := ihh ρ; have h2 := iht ρ
    simp only [msize, ex, den, Ty.enc_list_cons, Val.size_cons] at h1 h2 ⊢
    omega
  | lcase s e₁ e₂ ihs ih₁ ih₂ =>
    rcases hs : s.den ρ with _ | ⟨h, tl⟩
    · have := ih₁ ρ; simp only [msize, ex, den, hs]; omega
    · have := ih₂ (.cons h (.cons tl ρ)); simp only [msize, ex, den, hs]; omega
  | ncase s e₁ e₂ ihs ih₁ ih₂ =>
    by_cases hs : s.den ρ = 0
    · have := ih₁ ρ; simp only [msize, ex, den, hs, if_true]; omega
    · have := ih₂ (.cons (decide (s.den ρ % 2 = 1)) (.cons (s.den ρ / 2) ρ))
      simp only [msize, ex, den, hs, if_false]; omega
  | bit b n ihb ihn => simp only [msize, ex]; omega
  | letE a b iha ihb =>
    have := ihb (.cons (a.den ρ) ρ)
    simp only [msize, ex, den]; omega
  | app F a iha => simp only [msize, ex]; omega

attribute [tm_simp] ex

end Tm'

theorem bodySig_msize_le {a b : Ty} (i : ℕ) (body : Tm [a] b) (x : a.den) :
    (bodySig i body).msize x ≤ (b.enc ((bodySig i body).den x)).size + Tm'.ex body (Env.one x) :=
  Tm'.msize_le_ex body (Env.one x)

/-- Bit length is at most the encoded size. -/
theorem size_le_enc (n : ℕ) : n.size ≤ (Enc.nat n).size := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp
    · rw [Enc.nat_pos hn]
      have h1 := ih (n / 2) (by omega)
      have h2 := NatSize.size_half hn
      simp only [Val.size_cons]
      omega

end QecReliability.Trans.Control
