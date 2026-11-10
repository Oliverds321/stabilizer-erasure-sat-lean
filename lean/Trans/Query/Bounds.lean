import FL.Typed.Syntax

/-!
# Trans.Query.Bounds: generic polynomial-iterate bounds for typed FL terms

* `mag t x`: magnitude of a typed value (nat ↦ value, bool ↦ 1, list ↦ Σ(mag + 1) + 1,
  pair ↦ sum + 1); `size_le_mag : (t.enc x).size ≤ 5 * mag t x + 1`.
* `FnB B F`: cost, depth, msize and the magnitude of the result of `F` are `≤ B (mag arg)`.
* `Tm.bound`: if every callee of a term satisfies `FnB B` for a monotone `B` with
  `B m ≥ 5 m + 16`, and the literals of the term are bounded by `c`, then its cost, depth,
  msize and result magnitude are `≤ B^[tm.nodes] (ρ.mag + c)`.
* `exact_bounded`: hence a non-recursive function with exact bounds (`FnSig.exact`-style
  `cost = body.cost + 2` etc.) satisfies `FnB (B^[nodes + 1] ∘ (· + c))`.

With `B` a polynomial, every iterate `B^[k]` is a polynomial: this reduces closed-form
polynomial bounds of the whole transcription to (i) library/recursive base cases and
(ii) bookkeeping of the iteration counts.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Query.Bound
open QecReliability.FL

/-! ## Magnitude -/

def magL {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 1
  | x :: xs => f x + 1 + magL f xs

def mag : (t : Ty) → t.den → ℕ
  | .val, v => v.size
  | .unit, _ => 0
  | .bool, _ => 1
  | .nat, n => n
  | .list t, xs => magL (mag t) xs
  | .prod a b, p => mag a p.1 + mag b p.2 + 1

@[simp] theorem mag_nat (n : ℕ) : mag .nat n = n := rfl
@[simp] theorem mag_prod (a b : Ty) (p : (Ty.prod a b).den) : mag (.prod a b) p = mag a p.1 + mag b p.2 + 1 := rfl
@[simp] theorem mag_bool (b : Bool) : mag .bool b = 1 := rfl
@[simp] theorem mag_unit (u : Unit) : mag .unit u = 0 := rfl
@[simp] theorem mag_val (v : Val) : mag .val v = v.size := rfl
@[simp] theorem mag_nil (t : Ty) : mag (.list t) [] = 1 := rfl
@[simp] theorem mag_cons (t : Ty) (x : t.den) (xs : List t.den) :
    mag (.list t) (x :: xs) = mag t x + 1 + mag (.list t) xs := rfl

theorem size_le_mag : ∀ (t : Ty) (x : t.den), (t.enc x).size ≤ 5 * mag t x + 1
  | .val, v => by simp only [Ty.enc, mag]; omega
  | .unit, _ => by simp [Ty.enc, mag]
  | .bool, b => by have := Enc.bool_size b; simp only [Ty.enc, mag]; omega
  | .nat, n => by
      have h1 := Enc.nat_size_le n
      have h2 := NatSize.size_le_self n
      simp only [Ty.enc, mag]; omega
  | .list t, xs => by
      induction xs with
      | nil => simp [Ty.enc, Enc.list, mag, magL]
      | cons x xs ih =>
        have hx := size_le_mag t x
        have e := Ty.sz_list_cons t x xs
        rw [e]
        simp only [mag, magL] at ih ⊢
        omega
  | .prod a b, p => by
      have ha := size_le_mag a p.1
      have hb := size_le_mag b p.2
      rw [Ty.sz_prod]; simp only [mag]; omega

/-- Magnitude of an environment. -/
def envMag : {Γ : List Ty} → Env Γ → ℕ
  | [], .nil => 0
  | _ :: _, .cons x ρ => mag _ x + envMag ρ

@[simp] theorem envMag_cons {Γ : List Ty} {t : Ty} (x : t.den) (ρ : Env Γ) :
    envMag (.cons x ρ) = mag t x + envMag ρ := rfl

theorem mag_get {Γ : List Ty} {t : Ty} (ρ : Env Γ) (i : Idx Γ t) : mag t (ρ.get i) ≤ envMag ρ := by
  induction i with
  | zero => cases ρ; simp only [Env.get, envMag_cons]; omega
  | succ i ih =>
    cases ρ with
    | cons y ρ => simp only [Env.get, envMag_cons]; have := ih ρ; omega

/-! ## Bounding functions -/

/-- Admissible bounding functions. -/
structure Adm (B : ℕ → ℕ) : Prop where
  mono : Monotone B
  big : ∀ m, 5 * m + 16 ≤ B m

theorem Adm.le {B : ℕ → ℕ} (h : Adm B) (m : ℕ) : m ≤ B m := by have := h.big m; omega

theorem Adm.iter_mono {B : ℕ → ℕ} (h : Adm B) (k : ℕ) : Monotone (B^[k]) := h.mono.iterate k

theorem Adm.le_iter {B : ℕ → ℕ} (h : Adm B) (k m : ℕ) : m ≤ B^[k] m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply]; exact (h.le m).trans (ih (B m))

theorem Adm.iter_le_iter {B : ℕ → ℕ} (h : Adm B) {a b : ℕ} (hab : a ≤ b) (m : ℕ) :
    B^[a] m ≤ B^[b] m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_comm a d, Function.iterate_add_apply]
  exact h.le_iter d _

theorem Adm.succ_iter {B : ℕ → ℕ} (h : Adm B) (k m : ℕ) : 5 * B^[k] m + 16 ≤ B^[k + 1] m := by
  rw [Function.iterate_succ_apply']; exact h.big _

theorem Adm.lift {B : ℕ → ℕ} (h : Adm B) {a b : ℕ} (hab : a ≤ b) (m : ℕ) : B^[a] m ≤ B^[b] m :=
  h.iter_le_iter hab m

theorem Adm.step {B : ℕ → ℕ} (h : Adm B) {k j : ℕ} (hkj : k + 1 ≤ j) (m : ℕ) :
    5 * B^[k] m + 16 ≤ B^[j] m :=
  (h.succ_iter k m).trans (h.lift hkj m)

theorem Adm.step2 {B : ℕ → ℕ} (h : Adm B) {k j : ℕ} (hkj : k + 2 ≤ j) (m : ℕ) :
    25 * B^[k] m + 96 ≤ B^[j] m := by
  have h1 := h.succ_iter k m
  have h2 : 5 * B^[k + 1] m + 16 ≤ B^[k + 2] m := h.succ_iter (k + 1) m
  have h3 := h.lift hkj m
  omega

theorem Adm.comp {B : ℕ → ℕ} (h : Adm B) {a b m m' : ℕ} (hm : m' ≤ B^[b] m) :
    B^[a] m' ≤ B^[a + b] m := by
  rw [Function.iterate_add_apply]; exact h.iter_mono a hm

/-- `F`'s bounds and result magnitude are `≤ B (mag arg)`. -/
def FnB (B : ℕ → ℕ) {a b : Ty} (F : FnSig a b) : Prop :=
  ∀ y, F.cost y ≤ B (mag a y) ∧ F.depth y ≤ B (mag a y) ∧ F.msize y ≤ B (mag a y) ∧
    mag b (F.den y) ≤ B (mag a y)

/-! ## Terms -/

namespace Tm

/-- Node count (with slack for the arithmetic of each constructor). -/
def nodes {Γ : List Ty} {t : Ty} : Tm Γ t → ℕ
  | .var _ => 1
  | .val _ => 1
  | .lit _ => 1
  | .unit => 1
  | .ff => 1
  | .tt => 1
  | .zero => 1
  | .pair a b => (nodes a) + (nodes b) + 2
  | .fst p => (nodes p) + 1
  | .snd p => (nodes p) + 1
  | .ite c x y => (nodes c) + (nodes x) + (nodes y) + 2
  | .lnil => 1
  | .lcons h tl => (nodes h) + (nodes tl) + 2
  | .lcase s e₁ e₂ => (nodes s) + (nodes e₁) + (nodes e₂) + 3
  | .ncase s e₁ e₂ => (nodes s) + (nodes e₁) + (nodes e₂) + 3
  | .bit b n => (nodes b) + (nodes n) + 2
  | .letE a b => (nodes a) + (nodes b) + 3
  | .app _ a => (nodes a) + 2

/-- Literal sizes. -/
def litc {Γ : List Ty} {t : Ty} : Tm Γ t → ℕ
  | .val v => 5 * v.size + 1
  | .lit x => 5 * mag _ x + 1
  | .pair a b => max (litc a) (litc b)
  | .fst p => (litc p)
  | .snd p => (litc p)
  | .ite c x y => max (litc c) (max (litc x) (litc y))
  | .lcons h tl => max (litc h) (litc tl)
  | .lcase s e₁ e₂ => max (litc s) (max (litc e₁) (litc e₂))
  | .ncase s e₁ e₂ => max (litc s) (max (litc e₁) (litc e₂))
  | .bit b n => max (litc b) (litc n)
  | .letE a b => max (litc a) (litc b)
  | .app _ a => (litc a)
  | _ => 0

/-- Every callee is bounded by `B`. -/
def CallsB (B : ℕ → ℕ) {Γ : List Ty} {t : Ty} : Tm Γ t → Prop
  | .pair a b => (CallsB B a) ∧ (CallsB B b)
  | .fst p => (CallsB B p)
  | .snd p => (CallsB B p)
  | .ite c x y => (CallsB B c) ∧ (CallsB B x) ∧ (CallsB B y)
  | .lcons h tl => (CallsB B h) ∧ (CallsB B tl)
  | .lcase s e₁ e₂ => (CallsB B s) ∧ (CallsB B e₁) ∧ (CallsB B e₂)
  | .ncase s e₁ e₂ => (CallsB B s) ∧ (CallsB B e₁) ∧ (CallsB B e₂)
  | .bit b n => (CallsB B b) ∧ (CallsB B n)
  | .letE a b => (CallsB B a) ∧ (CallsB B b)
  | .app F a => FnB B F ∧ (CallsB B a)
  | _ => True

/-- The four quantities bounded by `M`. -/
def AllLe {Γ : List Ty} {t : Ty} (tm : Tm Γ t) (ρ : Env Γ) (M : ℕ) : Prop :=
  tm.cost ρ ≤ M ∧ tm.depth ρ ≤ M ∧ tm.msize ρ ≤ M ∧ mag t (tm.den ρ) ≤ M


theorem bitNat_le (b : Bool) (n : ℕ) : bitNat b n ≤ 2 * n + 1 := by
  unfold bitNat; split <;> omega

/-- **Generic bound.** All four quantities of a term are bounded by an iterate of `B`. -/
theorem bound {B : ℕ → ℕ} (hB : Adm B) {Γ : List Ty} {t : Ty} (tm : Tm Γ t)
    (hc : CallsB B tm) (c : ℕ) (hlit : litc tm ≤ c) (ρ : Env Γ) :
    AllLe tm ρ (B^[nodes tm] (envMag ρ + c)) := by
  induction tm with
  | var i =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    have h2 := mag_get ρ i
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes] <;> omega
  | val v =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [litc] at hlit
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_val] <;>
      omega
  | lit x =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    have h2 := size_le_mag _ x
    simp only [litc] at hlit
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes] <;> omega
  | unit =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_unit] <;>
      omega
  | ff =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_bool] <;>
      omega
  | tt =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_bool] <;>
      omega
  | zero =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_nat] <;>
      omega
  | lnil =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_nil] <;>
      omega
  | pair a b iha ihb =>
    simp only [CallsB, litc, max_le_iff] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := iha hc.1 hlit.1 ρ
    obtain ⟨c2, d2, m2, g2⟩ := ihb hc.2 hlit.2 ρ
    have l1 := hB.lift (show nodes a ≤ nodes a + nodes b by omega) (envMag ρ + c)
    have l2 := hB.lift (show nodes b ≤ nodes a + nodes b by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes a + nodes b) (j := nodes (Tm.pair a b)) (by simp [nodes])
      (envMag ρ + c)
    have sz := size_le_mag _ ((Tm.pair a b).den ρ)
    simp only [Tm.den, mag_prod] at sz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, mag_prod] <;> omega
  | fst p ih =>
    simp only [CallsB, litc] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ih hc hlit ρ
    have st := hB.step (k := nodes p) (j := nodes (Tm.fst p)) (by simp [nodes]) (envMag ρ + c)
    simp only [mag_prod] at g1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega
  | snd p ih =>
    simp only [CallsB, litc] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ih hc hlit ρ
    have st := hB.step (k := nodes p) (j := nodes (Tm.snd p)) (by simp [nodes]) (envMag ρ + c)
    simp only [mag_prod] at g1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega
  | ite cnd x y ihc ihx ihy =>
    simp only [CallsB, litc, max_le_iff] at hc hlit
    obtain ⟨c0, d0, m0, g0⟩ := ihc hc.1 hlit.1 ρ
    obtain ⟨c1, d1, m1, g1⟩ := ihx hc.2.1 hlit.2.1 ρ
    obtain ⟨c2, d2, m2, g2⟩ := ihy hc.2.2 hlit.2.2 ρ
    have l0 := hB.lift (show nodes cnd ≤ nodes cnd + nodes x + nodes y by omega) (envMag ρ + c)
    have l1 := hB.lift (show nodes x ≤ nodes cnd + nodes x + nodes y by omega) (envMag ρ + c)
    have l2 := hB.lift (show nodes y ≤ nodes cnd + nodes x + nodes y by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes cnd + nodes x + nodes y) (j := nodes (Tm.ite cnd x y))
      (by simp [nodes]) (envMag ρ + c)
    cases hcd : cnd.den ρ <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hcd] <;> simp <;> omega
  | lcons h tl ihh iht =>
    simp only [CallsB, litc, max_le_iff] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ihh hc.1 hlit.1 ρ
    obtain ⟨c2, d2, m2, g2⟩ := iht hc.2 hlit.2 ρ
    have l1 := hB.lift (show nodes h ≤ nodes h + nodes tl by omega) (envMag ρ + c)
    have l2 := hB.lift (show nodes tl ≤ nodes h + nodes tl by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes h + nodes tl) (j := nodes (Tm.lcons h tl)) (by simp [nodes])
      (envMag ρ + c)
    have sz := size_le_mag _ ((Tm.lcons h tl).den ρ)
    simp only [Tm.den, mag_cons] at sz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, mag_cons] <;> omega
  | @lcase _ te _ sc e₁ e₂ ihs ih₁ ih₂ =>
    simp only [CallsB, litc, max_le_iff] at hc hlit
    obtain ⟨cs, ds, ms, gs⟩ := ihs hc.1 hlit.1 ρ
    have l0 := hB.lift (show nodes sc ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes sc + nodes e₁ + nodes e₂ + 1) (j := nodes (Tm.lcase sc e₁ e₂))
      (by simp [nodes]) (envMag ρ + c)
    cases hd : sc.den ρ with
    | nil =>
      obtain ⟨c1, d1, m1, g1⟩ := ih₁ hc.2.1 hlit.2.1 ρ
      have l1 := hB.lift (show nodes e₁ ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega) (envMag ρ + c)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hd] <;> omega
    | cons hh tt =>
      rw [hd] at gs
      simp only [mag_cons] at gs
      have hX : envMag (Env.cons (t := te) hh (Env.cons (t := .list te) tt ρ)) + c ≤ B^[nodes sc + 1] (envMag ρ + c) := by
        have := hB.step (k := nodes sc) (j := nodes sc + 1) le_rfl (envMag ρ + c)
        have := hB.le_iter (nodes sc) (envMag ρ + c)
        simp only [envMag_cons]; omega
      obtain ⟨c2, d2, m2, g2⟩ := ih₂ hc.2.2 hlit.2.2 (Env.cons (t := te) hh (Env.cons (t := .list te) tt ρ))
      have cmp := hB.comp (a := nodes e₂) hX
      have l2 := hB.lift (show nodes e₂ + (nodes sc + 1) ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega)
        (envMag ρ + c)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hd] <;> omega
  | ncase sc e₁ e₂ ihs ih₁ ih₂ =>
    simp only [CallsB, litc, max_le_iff] at hc hlit
    obtain ⟨cs, ds, ms, gs⟩ := ihs hc.1 hlit.1 ρ
    have l0 := hB.lift (show nodes sc ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes sc + nodes e₁ + nodes e₂ + 1) (j := nodes (Tm.ncase sc e₁ e₂))
      (by simp [nodes]) (envMag ρ + c)
    by_cases hn : sc.den ρ = 0
    · obtain ⟨c1, d1, m1, g1⟩ := ih₁ hc.2.1 hlit.2.1 ρ
      have l1 := hB.lift (show nodes e₁ ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega) (envMag ρ + c)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hn, if_true] <;> omega
    · simp only [mag_nat] at gs
      have hX : envMag (Env.cons (t := .bool) (decide (sc.den ρ % 2 = 1)) (Env.cons (t := .nat) (sc.den ρ / 2) ρ)) + c ≤
          B^[nodes sc + 1] (envMag ρ + c) := by
        have := hB.step (k := nodes sc) (j := nodes sc + 1) le_rfl (envMag ρ + c)
        have := hB.le_iter (nodes sc) (envMag ρ + c)
        simp only [envMag_cons, mag_bool, mag_nat]; omega
      obtain ⟨c2, d2, m2, g2⟩ := ih₂ hc.2.2 hlit.2.2
        (Env.cons (t := .bool) (decide (sc.den ρ % 2 = 1)) (Env.cons (t := .nat) (sc.den ρ / 2) ρ))
      have cmp := hB.comp (a := nodes e₂) hX
      have l2 := hB.lift (show nodes e₂ + (nodes sc + 1) ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega)
        (envMag ρ + c)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hn, if_false] <;> omega
  | bit b n ihb ihn =>
    simp only [CallsB, litc, max_le_iff] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ihb hc.1 hlit.1 ρ
    obtain ⟨c2, d2, m2, g2⟩ := ihn hc.2 hlit.2 ρ
    have l1 := hB.lift (show nodes b ≤ nodes b + nodes n by omega) (envMag ρ + c)
    have l2 := hB.lift (show nodes n ≤ nodes b + nodes n by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes b + nodes n) (j := nodes (Tm.bit b n)) (by simp [nodes])
      (envMag ρ + c)
    have hb := bitNat_le (b.den ρ) (n.den ρ)
    have sz := size_le_mag .nat (bitNat (b.den ρ) (n.den ρ))
    simp only [Ty.enc_nat, mag_nat] at sz g2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, mag_nat] <;> omega
  | letE a b iha ihb =>
    simp only [CallsB, litc, max_le_iff] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := iha hc.1 hlit.1 ρ
    have hX : envMag (Env.cons (a.den ρ) ρ) + c ≤ B^[nodes a + 1] (envMag ρ + c) := by
      have := hB.step (k := nodes a) (j := nodes a + 1) le_rfl (envMag ρ + c)
      have := hB.le_iter (nodes a) (envMag ρ + c)
      simp only [envMag_cons]; omega
    obtain ⟨c2, d2, m2, g2⟩ := ihb hc.2 hlit.2 (Env.cons (a.den ρ) ρ)
    have cmp := hB.comp (a := nodes b) hX
    have l1 := hB.lift (show nodes a ≤ nodes b + (nodes a + 1) by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes b + (nodes a + 1)) (j := nodes (Tm.letE a b)) (by simp [nodes]; omega)
      (envMag ρ + c)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega
  | app F a iha =>
    simp only [CallsB, litc] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := iha hc.2 hlit ρ
    obtain ⟨f1, f2, f3, f4⟩ := hc.1 (a.den ρ)
    have hm : B (mag _ (a.den ρ)) ≤ B^[nodes a + 1] (envMag ρ + c) := by
      rw [Function.iterate_succ_apply']; exact hB.mono g1
    have st := hB.step (k := nodes a + 1) (j := nodes (Tm.app F a)) (by simp [nodes]) (envMag ρ + c)
    have st0 := hB.step (k := nodes a) (j := nodes a + 1) le_rfl (envMag ρ + c)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega

end Tm

/-! ## Functions, admissibility of iterates, and the closed form -/

theorem FnB.mono {B B' : ℕ → ℕ} (hBB : ∀ m, B m ≤ B' m) {a b : Ty} {F : FnSig a b} (h : FnB B F) :
    FnB B' F := fun y => by
  obtain ⟨h1, h2, h3, h4⟩ := h y
  have := hBB (mag a y)
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem Tm.CallsB.mono {B B' : ℕ → ℕ} (hBB : ∀ m, B m ≤ B' m) {Γ : List Ty} {t : Ty} (tm : Tm Γ t)
    (h : Tm.CallsB B tm) : Tm.CallsB B' tm := by
  induction tm with
  | app F a ih => exact ⟨h.1.mono hBB, ih h.2⟩
  | pair a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | fst p ih => exact ih h
  | snd p ih => exact ih h
  | ite c x y ihc ihx ihy => exact ⟨ihc h.1, ihx h.2.1, ihy h.2.2⟩
  | lcons a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | lcase s e₁ e₂ ihs ih₁ ih₂ => exact ⟨ihs h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | ncase s e₁ e₂ ihs ih₁ ih₂ => exact ⟨ihs h.1, ih₁ h.2.1, ih₂ h.2.2⟩
  | bit a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | letE a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | _ => trivial

/-- Iterates of an admissible function, shifted by a constant, are admissible. -/
theorem Adm.iterShift {B : ℕ → ℕ} (hB : Adm B) {k : ℕ} (hk : 1 ≤ k) (c : ℕ) :
    Adm (fun m => B^[k] (m + c)) where
  mono := fun x y hxy => hB.iter_mono k (by omega)
  big := fun m => by
    have h1 := hB.step (k := 0) (j := k) (by omega) (m + c)
    simp only [Function.iterate_zero, id] at h1
    omega

/-- **Signatures with body bounds.** A function whose bounds are those of its body (as for
`FnSig.exact`) is bounded by `B^[nodes body + 1] (· + c)` when its callees are bounded by `B`. -/
theorem body_bounded {B : ℕ → ℕ} (hB : Adm B) {a b : Ty} (F : FnSig a b) (body : Tm [a] b)
    (hcost : ∀ x, F.cost x ≤ body.cost (Env.one x) + 2)
    (hdepth : ∀ x, F.depth x ≤ body.depth (Env.one x) + 1)
    (hmsize : ∀ x, F.msize x ≤ body.msize (Env.one x))
    (hden : ∀ x, F.den x = body.den (Env.one x))
    (hc : Tm.CallsB B body) (c : ℕ) (hlit : Tm.litc body ≤ c) :
    FnB (fun m => B^[Tm.nodes body + 1] (m + c)) F := fun x => by
  obtain ⟨h1, h2, h3, h4⟩ := Tm.bound hB body hc c hlit (Env.one x)
  have hst := hB.step (k := Tm.nodes body) (j := Tm.nodes body + 1) le_rfl (mag a x + c)
  have he : envMag (Env.one x) = mag a x := by simp [envMag]
  rw [he] at h1 h2 h3 h4
  have := hcost x; have := hdepth x; have := hmsize x
  rw [hden x]
  dsimp only
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The base bounding function: a quadratic. -/
def B0 (m : ℕ) : ℕ := 25 * (m + 4) ^ 2

theorem adm_B0 : Adm B0 where
  mono := fun x y h => by unfold B0; have := Nat.pow_le_pow_left (show x + 4 ≤ y + 4 by omega) 2; omega
  big := fun m => by unfold B0; nlinarith

/-- **Closed form**: the `k`-th iterate of `B0` is a polynomial of degree `2^k`. -/
theorem B0_iter_le (k m : ℕ) : B0^[k] m + 4 ≤ 26 ^ (2 ^ k - 1) * (m + 4) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set y := B0^[k] m
    set A := 26 ^ (2 ^ k - 1) * (m + 4) ^ (2 ^ k)
    have hA : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hpow : 26 ^ (2 ^ (k + 1) - 1) * (m + 4) ^ (2 ^ (k + 1)) = 26 * A ^ 2 := by
      have e1 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      have e2 : 2 ^ (k + 1) - 1 = (2 ^ k - 1) * 2 + 1 := by
        have := Nat.one_le_two_pow (n := k); rw [e1]; omega
      rw [e2, e1, pow_succ, pow_mul, pow_mul]
      simp only [A, mul_pow]
      ring
    rw [hpow]
    unfold B0
    have h1 : (y + 4) ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left ih 2
    have h2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
    nlinarith

end QecReliability.Trans.Query.Bound
