import RegMachine.Struct
import RegMachine.RegMap
import Mathlib.Tactic.Linarith

/-!
# Interpreter toolkit: bounded big-step runs of basic register programs

* `Runs B st s t n`: the statement `st` runs (big-step, `basicSem`) from `s` to `t` executing at
  most `n` primitives, every visited register file satisfying `Fits B`. Costs are not tracked
  here: `BigStep.cost_le_fits` bounds the abstract cost of any run inside `Fits B` by
  `N * (2B + 1)`, so it suffices to count primitives.
* Combinators for `Runs` (sequencing, branching, loops, single primitives).
* Register renaming (`renameS`, `bigStep_rename_ext`): a program over a small register file
  `Fin K` placed into a larger file `Fin R` by an injective map; registers outside the image
  are untouched.
* `toOracle`: basic programs are oracle programs (`OInstr.basic`), with the same runs.
-/

set_option autoImplicit false

namespace QecReliability.Interp
open QecReliability.RegMachine Function

variable {R : ℕ}

/-- The no-op statement (answers the constant `true`, one primitive). -/
def nop : Stmt (Instr R) := .prim (.const true)

theorem fits_upd {B : ℕ} {s : Regs R} (h : Fits B s) {r : Fin R} {l : List Bool}
    (hl : l.length ≤ B) : Fits B (update s r l) := by
  intro r'
  by_cases hr : r' = r
  · subst hr; simpa using hl
  · rw [update_of_ne hr]; exact h r'

theorem fits_mono {B B' : ℕ} {s : Regs R} (h : Fits B s) (hB : B ≤ B') : Fits B' s :=
  fun r => (h r).trans hB

/-! ## Cost from primitive counts -/

theorem Instr.cost_le_fits {B : ℕ} {s : Regs R} (hs : Fits B s) (p : Instr R) :
    p.cost s ≤ 2 * B + 1 := by
  cases p with
  | clear r => have := hs r; simp only [Instr.cost]; omega
  | pushBack r _ => have := hs r; simp only [Instr.cost]; omega
  | popFront r => have := hs r; simp only [Instr.cost]; omega
  | append d r => have := hs d; have := hs r; simp only [Instr.cost]; omega
  | isEmpty _ => simp only [Instr.cost]; omega
  | headIs _ _ => simp only [Instr.cost]; omega
  | const _ => simp only [Instr.cost]; omega
  | pushFront r _ => have := hs r; simp only [Instr.cost]; omega

/-- Inside `Fits B`, every primitive costs at most `2B + 1`. -/
theorem BigStep.cost_le_fits {B : ℕ} {st : Stmt (Instr R)} {s t : Regs R} {N C : ℕ}
    (h : Stmt.BigStep (basicSem R) (Fits B) st s N C t) : C ≤ N * (2 * B + 1) := by
  induction h with
  | @prim p _ _ _ hs _ _ _ =>
    have := Instr.cost_le_fits hs p
    simp only [basicSem] at this ⊢
    omega
  | seq _ _ ih1 ih2 => rw [Nat.add_mul]; omega
  | @iteT tp _ _ _ _ _ _ _ hs _ _ _ ih =>
    have := Instr.cost_le_fits hs tp
    simp only [basicSem] at this ⊢
    rw [Nat.add_mul]; omega
  | @iteF tp _ _ _ _ _ _ _ hs _ _ _ ih =>
    have := Instr.cost_le_fits hs tp
    simp only [basicSem] at this ⊢
    rw [Nat.add_mul]; omega
  | @loopF tp _ _ _ _ _ hs _ _ _ _ =>
    have := Instr.cost_le_fits hs tp
    simp only [basicSem] at this ⊢
    omega
  | @loopT tp _ _ _ _ _ _ _ _ _ _ hs _ _ _ _ ih1 ih2 =>
    have := Instr.cost_le_fits hs tp
    simp only [basicSem] at this ⊢
    rw [Nat.add_mul, Nat.add_mul]; omega

theorem BigStep.mono_inv {S : Type} {σ : PrimSem (Instr R) S} {Inv Inv' : S → Prop}
    (hI : ∀ s, Inv s → Inv' s) {st : Stmt (Instr R)} {s t : S} {N C : ℕ}
    (h : Stmt.BigStep σ Inv st s N C t) : Stmt.BigStep σ Inv' st s N C t := by
  induction h with
  | prim hs hp he ht => exact .prim (hI _ hs) hp he (hI _ ht)
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | iteT hs hp he _ ih => exact .iteT (hI _ hs) hp he ih
  | iteF hs hp he _ ih => exact .iteF (hI _ hs) hp he ih
  | loopF hs hp he hb ht => exact .loopF (hI _ hs) hp he hb (hI _ ht)
  | loopT hs hp he _ _ ih1 ih2 => exact .loopT (hI _ hs) hp he ih1 ih2

/-! ## Bounded runs -/

/-- `st` runs from `s` to `t` with at most `n` primitives, inside `Fits B`. -/
def Runs (B : ℕ) (st : Stmt (Instr R)) (s t : Regs R) (n : ℕ) : Prop :=
  ∃ N C, Stmt.BigStep (basicSem R) (Fits B) st s N C t ∧ N ≤ n

namespace Runs
variable {B : ℕ} {st a b body : Stmt (Instr R)} {s s1 s2 t : Regs R} {n n1 n2 : ℕ}

theorem mono (h : Runs B st s t n) {n' : ℕ} (hn : n ≤ n') : Runs B st s t n' := by
  obtain ⟨N, C, h, hN⟩ := h
  exact ⟨N, C, h, hN.trans hn⟩

theorem fits_end (h : Runs B st s t n) : Fits B t := by
  obtain ⟨N, C, h, -⟩ := h
  exact h.inv_end

/-- Primitive count and abstract cost of a bounded run. -/
theorem cost (h : Runs B st s t n) :
    ∃ N C, Stmt.BigStep (basicSem R) (Fits B) st s N C t ∧ N ≤ n ∧ C ≤ n * (2 * B + 1) := by
  obtain ⟨N, C, h, hN⟩ := h
  exact ⟨N, C, h, hN, (BigStep.cost_le_fits h).trans (Nat.mul_le_mul_right _ hN)⟩

theorem seq (h1 : Runs B a s s1 n1) (h2 : Runs B b s1 s2 n2) :
    Runs B (.seq a b) s s2 (n1 + n2) := by
  obtain ⟨N1, C1, h1, hN1⟩ := h1
  obtain ⟨N2, C2, h2, hN2⟩ := h2
  exact ⟨_, _, .seq h1 h2, by omega⟩

theorem prim {p : Instr R} {c : Bool} (hs : Fits B s) (hp : p.pre s) (he : p.eval s = (t, c))
    (ht : Fits B t) : Runs B (.prim p) s t 1 :=
  ⟨1, _, Stmt.BigStep.prim (σ := basicSem R) hs hp he ht, le_rfl⟩

theorem iteT {tp : Instr R} (hs : Fits B s) (hp : tp.pre s) (he : tp.eval s = (s, true))
    (h : Runs B a s t n) : Runs B (.ite tp a b) s t (n + 1) := by
  obtain ⟨N, C, h, hN⟩ := h
  exact ⟨_, _, Stmt.BigStep.iteT (σ := basicSem R) hs hp he h, by omega⟩

theorem iteF {tp : Instr R} (hs : Fits B s) (hp : tp.pre s) (he : tp.eval s = (s, false))
    (h : Runs B b s t n) : Runs B (.ite tp a b) s t (n + 1) := by
  obtain ⟨N, C, h, hN⟩ := h
  exact ⟨_, _, Stmt.BigStep.iteF (σ := basicSem R) hs hp he h, by omega⟩

theorem loopF {tp : Instr R} {pol c : Bool} (hs : Fits B s) (hp : tp.pre s)
    (he : tp.eval s = (s, c)) (hc : c ≠ pol) : Runs B (.loop tp pol body) s s 1 :=
  ⟨1, _, Stmt.BigStep.loopF (σ := basicSem R) hs hp he hc hs, le_rfl⟩

theorem loopT {tp : Instr R} {pol : Bool} (hs : Fits B s) (hp : tp.pre s)
    (he : tp.eval s = (s, pol)) (hb : Runs B body s s1 n1)
    (hl : Runs B (.loop tp pol body) s1 t n2) : Runs B (.loop tp pol body) s t (n1 + n2 + 1) := by
  obtain ⟨N1, C1, h1, hN1⟩ := hb
  obtain ⟨N2, C2, h2, hN2⟩ := hl
  exact ⟨_, _, Stmt.BigStep.loopT (σ := basicSem R) hs hp he h1 h2, by omega⟩

/-! ### Single primitives -/

theorem clear (hs : Fits B s) (r : Fin R) : Runs B (.prim (.clear r)) s (update s r []) 1 :=
  prim hs trivial rfl (fits_upd hs (by simp))

theorem pushBack {r : Fin R} {w : List Bool} (c : Bool) (hs : Fits B s) (hr : s r = w)
    (hl : w.length + 1 ≤ B) : Runs B (.prim (.pushBack r c)) s (update s r (w ++ [c])) 1 :=
  prim (c := true) hs trivial (by simp [Instr.eval, hr]) (fits_upd hs (by simpa using hl))

theorem popFront {r : Fin R} {c : Bool} {w : List Bool} (hs : Fits B s) (hr : s r = c :: w) :
    Runs B (.prim (.popFront r)) s (update s r w) 1 :=
  prim (c := true) hs trivial (by simp [Instr.eval, hr])
    (fits_upd hs (by have := hs r; rw [hr] at this; simp at this; omega))

theorem append {d r : Fin R} {x y : List Bool} (hs : Fits B s) (hne : d ≠ r) (hd : s d = x)
    (hr : s r = y) (hl : x.length + y.length ≤ B) :
    Runs B (.prim (.append d r)) s (update s d (x ++ y)) 1 :=
  prim (c := true) hs hne (by simp [Instr.eval, hd, hr]) (fits_upd hs (by simpa using hl))

theorem nop (hs : Fits B s) : Runs B (Interp.nop (R := R)) s s 1 :=
  prim hs trivial rfl hs

end Runs

/-! ## Register renaming -/

/-- Rename the registers of a structured basic program. -/
def renameS {K R' : ℕ} (f : Fin K → Fin R') : Stmt (Instr K) → Stmt (Instr R')
  | .prim p => .prim (p.map f)
  | .seq a b => .seq (renameS f a) (renameS f b)
  | .ite t a b => .ite (t.map f) (renameS f a) (renameS f b)
  | .loop t pol b => .loop (t.map f) pol (renameS f b)

section Rename
variable {K : ℕ} {ρ : Fin K → Fin R}

theorem extend_update (hρ : Injective ρ) (s : Regs K) (t0 : Regs R) (r : Fin K) (w : List Bool) :
    extend ρ (update s r w) t0 = update (extend ρ s t0) (ρ r) w := by
  funext q
  by_cases hq : ∃ a, ρ a = q
  · obtain ⟨a, rfl⟩ := hq
    rw [hρ.extend_apply]
    by_cases ha : a = r
    · subst ha; simp
    · rw [update_of_ne ha, update_of_ne (fun h => ha (hρ h)), hρ.extend_apply]
  · rw [extend_apply' _ _ _ hq]
    have : q ≠ ρ r := fun h => hq ⟨r, h.symm⟩
    rw [update_of_ne this, extend_apply' _ _ _ hq]

theorem eval_rename (hρ : Injective ρ) (p : Instr K) (s : Regs K) (t0 : Regs R) :
    Instr.eval (p.map ρ) (extend ρ s t0) = (extend ρ (p.eval s).1 t0, (p.eval s).2) := by
  cases p <;> simp [Instr.map, Instr.eval, extend_update hρ, hρ.extend_apply]

theorem cost_rename (hρ : Injective ρ) (p : Instr K) (s : Regs K) (t0 : Regs R) :
    Instr.cost (p.map ρ) (extend ρ s t0) = Instr.cost p s := by
  cases p <;> simp [Instr.map, Instr.cost, hρ.extend_apply]

theorem pre_rename (hρ : Injective ρ) (p : Instr K) (s : Regs K) (t0 : Regs R) (h : p.pre s) :
    Instr.pre (p.map ρ) (extend ρ s t0) := by
  cases p with
  | append d r =>
    show ρ d ≠ ρ r
    exact fun hh => (show d ≠ r from h) (hρ hh)
  | _ => trivial

theorem fits_extend (hρ : Injective ρ) {B : ℕ} {s : Regs K} {t0 : Regs R} (hs : Fits B s)
    (ht : Fits B t0) : Fits B (extend ρ s t0) := by
  intro q
  by_cases hq : ∃ a, ρ a = q
  · obtain ⟨a, rfl⟩ := hq
    rw [hρ.extend_apply]; exact hs a
  · rw [extend_apply' _ _ _ hq]; exact ht q

/-- Runs transport along an injective register placement; the background file `t0` provides
the contents of the registers outside the image (which are never touched). -/
theorem bigStep_rename (hρ : Injective ρ) {B : ℕ} (t0 : Regs R) (ht0 : Fits B t0)
    {st : Stmt (Instr K)} {s u : Regs K} {N C : ℕ}
    (h : Stmt.BigStep (basicSem K) (Fits B) st s N C u) :
    Stmt.BigStep (basicSem R) (Fits B) (renameS ρ st) (extend ρ s t0) N C (extend ρ u t0) := by
  induction h with
  | @prim p s s' b hs hp he ht =>
    have h1 := Stmt.BigStep.prim (σ := basicSem R) (Inv := Fits B) (p := p.map ρ)
      (s := extend ρ s t0) (s' := extend ρ s' t0) (b := b) (fits_extend hρ hs ht0)
      (pre_rename hρ p s t0 hp)
      (by show Instr.eval _ _ = _
          rw [eval_rename hρ]; simp only [basicSem] at he; rw [he])
      (fits_extend hρ ht ht0)
    simpa [renameS, basicSem, cost_rename hρ] using h1
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | @iteT tp a b s s' s'' n c hs hp he _ ih =>
    have he' : (basicSem R).eval (tp.map ρ) (extend ρ s t0) = (extend ρ s' t0, true) := by
      show Instr.eval _ _ = _
      rw [eval_rename hρ]; simp only [basicSem] at he; rw [he]
    have h1 := Stmt.BigStep.iteT (σ := basicSem R) (Inv := Fits B) (b := renameS ρ b)
      (fits_extend hρ hs ht0) (pre_rename hρ tp s t0 hp) he' ih
    simpa [renameS, basicSem, cost_rename hρ] using h1
  | @iteF tp a b s s' s'' n c hs hp he _ ih =>
    have he' : (basicSem R).eval (tp.map ρ) (extend ρ s t0) = (extend ρ s' t0, false) := by
      show Instr.eval _ _ = _
      rw [eval_rename hρ]; simp only [basicSem] at he; rw [he]
    have h1 := Stmt.BigStep.iteF (σ := basicSem R) (Inv := Fits B) (a := renameS ρ a)
      (fits_extend hρ hs ht0) (pre_rename hρ tp s t0 hp) he' ih
    simpa [renameS, basicSem, cost_rename hρ] using h1
  | @loopF tp pol b body s s' hs hp he hne ht =>
    have he' : (basicSem R).eval (tp.map ρ) (extend ρ s t0) = (extend ρ s' t0, b) := by
      show Instr.eval _ _ = _
      rw [eval_rename hρ]; simp only [basicSem] at he; rw [he]
    have h1 := Stmt.BigStep.loopF (σ := basicSem R) (Inv := Fits B) (body := renameS ρ body)
      (pol := pol) (fits_extend hρ hs ht0) (pre_rename hρ tp s t0 hp) he' hne
      (fits_extend hρ ht ht0)
    simpa [renameS, basicSem, cost_rename hρ] using h1
  | @loopT tp pol body s s' s1 s2 n1 n2 c1 c2 hs hp he _ _ ih1 ih2 =>
    have he' : (basicSem R).eval (tp.map ρ) (extend ρ s t0) = (extend ρ s' t0, pol) := by
      show Instr.eval _ _ = _
      rw [eval_rename hρ]; simp only [basicSem] at he; rw [he]
    have h1 := Stmt.BigStep.loopT (σ := basicSem R) (Inv := Fits B)
      (fits_extend hρ hs ht0) (pre_rename hρ tp s t0 hp) he' ih1 ih2
    simpa [renameS, basicSem, cost_rename hρ] using h1

theorem extend_restrict (hρ : Injective ρ) (t : Regs R) : extend ρ (fun i => t (ρ i)) t = t := by
  funext q
  by_cases hq : ∃ a, ρ a = q
  · obtain ⟨a, rfl⟩ := hq; rw [hρ.extend_apply]
  · rw [extend_apply' _ _ _ hq]

/-- **Placement of a local program.** A run of `st` on the local view `t ∘ ρ` of a register file
`t` gives a run of `renameS ρ st` on `t` itself: the image registers end as in the local run,
all other registers are unchanged, with the same primitive count and cost. -/
theorem bigStep_rename_ext (hρ : Injective ρ) {B : ℕ} (t : Regs R) (ht : Fits B t)
    {st : Stmt (Instr K)} {u : Regs K} {N C : ℕ}
    (h : Stmt.BigStep (basicSem K) (Fits B) st (fun i => t (ρ i)) N C u) :
    ∃ t', Stmt.BigStep (basicSem R) (Fits B) (renameS ρ st) t N C t' ∧
      (∀ i, t' (ρ i) = u i) ∧ (∀ q, (∀ i, ρ i ≠ q) → t' q = t q) := by
  have h' := bigStep_rename hρ t ht h
  rw [extend_restrict hρ] at h'
  refine ⟨_, h', fun i => hρ.extend_apply _ _ _, fun q hq => ?_⟩
  exact extend_apply' _ _ _ (fun ⟨a, ha⟩ => hq a ha)

end Rename

/-! ## Basic programs are oracle programs -/

/-- View a basic program as an oracle program (no calls). -/
def toOracle : Stmt (Instr R) → Stmt (OInstr R)
  | .prim p => .prim (.basic p)
  | .seq a b => .seq (toOracle a) (toOracle b)
  | .ite t a b => .ite (.basic t) (toOracle a) (toOracle b)
  | .loop t pol b => .loop (.basic t) pol (toOracle b)

theorem bigStep_toOracle (O : OracleSpec) (callOK : Fin R → Prop) {Inv : Regs R → Prop}
    {st : Stmt (Instr R)} {s t : Regs R} {N C : ℕ}
    (h : Stmt.BigStep (basicSem R) Inv st s N C t) :
    Stmt.BigStep (oracleSem O R callOK) Inv (toOracle st) s N C t := by
  induction h with
  | prim hs hp he ht => exact .prim (σ := oracleSem O R callOK) hs hp he ht
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | iteT hs hp he _ ih => exact .iteT (σ := oracleSem O R callOK) hs hp he ih
  | iteF hs hp he _ ih => exact .iteF (σ := oracleSem O R callOK) hs hp he ih
  | loopF hs hp he hb ht => exact .loopF (σ := oracleSem O R callOK) hs hp he hb ht
  | loopT hs hp he _ _ ih1 ih2 => exact .loopT (σ := oracleSem O R callOK) hs hp he ih1 ih2

end QecReliability.Interp
