import Interp.Loop
import FL.EncodedRun

/-!
# The FL interpreter as a register program: `flCall`

`flCallLocal P f` (16 local registers, see `Interp/Step.lean`):

1. `rB := []`;
2. load the constant `Program.enc P` into `rP` (one `pushBack` per bit);
3. write the initial state `State.enc (eval (call f (var 0)) [x] [])` into `rS`: a constant
   prefix, the argument register `rA` (`= x.bits`), a constant suffix (`initTm`);
4. `interpLoop` (one `stepS` per CEK step, until the final state `ret y []`);
5. `rB := rS` (`= y.bits`), clear `rS`, `rP`, `rH`.

`flCall P f ρ = renameS ρ (flCallLocal P f)` places it on any 16 distinct registers `ρ i` of a
larger register file. Main theorems: `flCallLocal_eval` and `flCall_eval` (and
`flCall_eval_oracle` for oracle programs).
-/

set_option autoImplicit false

namespace QecReliability.Interp
open QecReliability.RegMachine QecReliability.FL Function

local notation "rA" => (0 : Fin 16)
local notation "rB" => (1 : Fin 16)
local notation "rS" => (2 : Fin 16)
local notation "rP" => (3 : Fin 16)
local notation "rH" => (4 : Fin 16)

variable {B : ℕ}

/-- Template of the initial state `eval (call f (var 0)) [x] []`, `x` read from `rA`. -/
def initTm (f : ℕ) : Tm 16 :=
  tEv (Tm.ofVal (Expr.enc (.call f (.var 0)))) (.cons (.reg rA) .nil) .nil

theorem initTm_eval (f : ℕ) (x : Val) :
    (initTm f).eval (fun _ => x) = (State.eval (.call f (.var 0)) [x] []).enc := by
  simp [initTm, tEv, Tm.eval, Tm.eval_ofVal, State.enc, tagged, envEnc, stackEnc, Enc.list,
    Enc.unary]

theorem initTm_regs (f : ℕ) : (initTm f).regs = [rA] := by
  simp [initTm, tEv, Tm.regs, Tm.regs_ofVal]

theorem initTm_nodes (f : ℕ) :
    (initTm f).nodes = (Expr.enc (.call f (.var 0))).size + 8 := by
  simp [initTm, tEv, Tm.nodes, Tm.nodes_ofVal]; omega

/-- The interpreter on the local register file `Fin 16`: argument `x.bits` in register `0`,
result `y.bits` in register `1`. -/
def flCallLocal (P : Program) (f : ℕ) : Stmt (Instr 16) :=
  .seq (.prim (.clear rB)) (.seq (emitS rP (Tm.ofVal (Program.enc P)))
    (.seq (emitS rS (initTm f)) (.seq interpLoop
      (.seq (.prim (.append rB rS)) (clearL [rS, rP, rH])))))

/-- Primitive budget of `flCallLocal` for a CEK run of `n` steps, states of size `≤ SB`, and an
encoded program of size `p`. -/
def callBound (n SB p : ℕ) : ℕ := (n + 2) * (stepBound SB p + 1) + p + SB + 20

theorem flCallLocal_run {P : Program} {f SB n : ℕ} {x y : Val}
    (hr : RunAll P (fun z => z.enc.size ≤ SB) (State.eval (.call f (.var 0)) [x] []) n
      (.ret y []))
    {s : Regs 16} (hs0 : ∀ r : Fin 16, 2 ≤ r.val → s r = []) (hA : s rA = x.bits)
    (hfit : Fits B s) (hB : SB + (Program.enc P).size + 2 ≤ B) :
    Runs B (flCallLocal P f) s (update s rB y.bits) (callBound n SB (Program.enc P).size) := by
  have hq0 : (State.eval (.call f (.var 0)) [x] []).enc.size ≤ SB := hr.first
  have hq1 : (State.ret y []).enc.size ≤ SB := hr.last
  have hysz : (State.ret y []).enc.size = y.size + 6 := by
    simp [State.enc, tagged, stackEnc, Enc.list, Enc.unary]; omega
  have hEsz : (Expr.enc (.call f (.var 0))).size + 4 ≤
      (State.eval (.call f (.var 0)) [x] []).enc.size := by
    simp [State.enc, tagged, envEnc, stackEnc, Enc.list, Enc.unary]; omega
  -- 1. clear rB
  have h1 := Runs.clear hfit rB
  set s1 := update s rB [] with hs1
  -- 2. load the program
  have h2 := emit_run (B := B) (dst := rP) (σ := fun _ => x) (Tm.ofVal (Program.enc P)) s1 []
    (by simp [hs1, hs0 rP (by decide)]) (by simp [Tm.regs_ofVal])
    (by simp [Tm.regs_ofVal]) h1.fits_end (by simp [Tm.eval_ofVal]; omega)
  rw [Tm.eval_ofVal, Tm.nodes_ofVal] at h2
  set s2 := update s1 rP ([] ++ (Program.enc P).bits) with hs2
  -- 3. the initial state
  have h3 := emit_run (B := B) (dst := rS) (σ := fun _ => x) (initTm f) s2 []
    (by simp [hs2, hs1, hs0 rS (by decide)]) (by simp [initTm_regs])
    (by intro r hr; simp [initTm_regs] at hr; subst hr; simp [hs2, hs1, hA])
    h2.fits_end (by rw [initTm_eval]; simp; omega)
  rw [initTm_eval, initTm_nodes] at h3
  set s3 := update s2 rS ([] ++ (State.eval (.call f (.var 0)) [x] []).enc.bits) with hs3
  -- 4. the loop
  have hc3 : Clean s3 := by
    intro r hr
    have hrS : r ≠ rS := by intro e; subst e; simp at hr
    have hrP : r ≠ rP := by intro e; subst e; simp at hr
    have hrB : r ≠ rB := by intro e; subst e; simp at hr
    simp [hs3, hs2, hs1, hrS, hrP, hrB, hs0 r (by omega)]
  have h4 := interpLoop_run hr s3 hc3 h3.fits_end (by simp [hs3])
    (by simp [hs3, hs2]) hB
  set s4 := update (update s3 rS y.bits) rH [true] with hs4
  -- 5. copy out and clean
  have h5 := Runs.append (d := rB) (r := rS) (x := []) (y := y.bits) h4.fits_end (by decide)
    (by simp [hs4, hs3, hs2, hs1]) (by simp [hs4]) (by simp; omega)
  have h6 := clearL_run [rS, rP, rH] _ h5.fits_end
  have e : (fun r => if r ∈ [rS, rP, rH] then [] else update s4 rB ([] ++ y.bits) r) =
      update s rB y.bits := by
    funext r
    by_cases hr : r ∈ [rS, rP, rH]
    · have hrB : r ≠ rB := by
        intro e; subst e; simp at hr
      have hr2 : 2 ≤ r.val := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide
      simp [hr, hrB, hs0 r hr2]
    · by_cases hrB : r = rB
      · subst hrB; simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hr.1, hr.2.1, hr.2.2, hrB, hs4, hs3, hs2, hs1]
  rw [e] at h6
  refine (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono ?_
  unfold callBound
  have e2 : (n + 2) * (stepBound SB (Program.enc P).size + 1) =
      (n + 1) * (stepBound SB (Program.enc P).size + 1) + (stepBound SB (Program.enc P).size + 1) := by
    ring
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## From an FL evaluation -/

/-- An FL call `f x = y` of cost `t` and depth `d` is a CEK run of at most `3t` steps through
states whose encodings have size at most `stateBound W X m (2 + X * d)`
(`Eval.encodedRun`, stated on CEK states). -/
theorem evalCall_runAll {P : Program} {m X W : ℕ} (hm : 1 ≤ m) (hX3 : 3 ≤ X)
    (hX : ∀ b ∈ P, b.size ≤ X)
    (hW : ∀ b ∈ P, (Expr.enc b).size ≤ W) {f : ℕ} (hf : 2 * f + 15 ≤ W) {x y : Val} {t d : ℕ}
    (h : EvalCall P m f x y t d) (hx : x.size ≤ m) :
    ∃ n ≤ 3 * t, RunAll P (fun z => z.enc.size ≤ stateBound W X m (2 + X * d))
      (State.eval (.call f (.var 0)) [x] []) n (State.ret y []) := by
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
  refine ⟨n, hn, r'.mono (fun s hs => ?_)⟩
  have := State.enc_size_le hs.1 hs.2
  simpa [Expr.size] using this

/-- Primitive budget of an FL call of cost `t`, state bound `SB`, encoded program size `p`. -/
def flBound (t SB p : ℕ) : ℕ := callBound (3 * t) SB p

theorem flBound_le (t SB p : ℕ) : flBound t SB p ≤ 700 * (t + 1) * (SB + p + 1) := by
  unfold flBound callBound stepBound
  have h1 : (3 * t + 2) * (40 * (SB + p) + 200 + 1) ≤ (3 * t + 3) * (40 * (SB + p) + 201) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (3 * t + 3) * (40 * (SB + p) + 201) = 3 * (t + 1) * (40 * (SB + p) + 201) := by
    ring
  have h3 : 3 * (t + 1) * (40 * (SB + p) + 201) ≤ 3 * (t + 1) * (201 * (SB + p + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : 3 * (t + 1) * (201 * (SB + p + 1)) = 603 * ((t + 1) * (SB + p + 1)) := by ring
  have h5 : 700 * (t + 1) * (SB + p + 1) = 700 * ((t + 1) * (SB + p + 1)) := by ring
  have h6 : SB + p + 1 ≤ (t + 1) * (SB + p + 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **The FL interpreter (local registers).** If `P` evaluates `f x = y` with cost `t`, depth
`d` and value bound `m` (side conditions of `Eval.encodedRun`), then from any register file with
`x.bits` in register `0` and registers `2..15` empty, `flCallLocal P f` runs to the same file
with register `1` set to `y.bits` (register `0` unchanged, scratch registers empty again),
executing `N ≤ flBound t SB |Pv|` primitives of total abstract cost `C ≤ N·(2B+1)`, with every
visited register file inside `Fits B`, for any `B ≥ SB + |Pv| + 2`, where
`SB = stateBound W X m (2 + X·d)` and `Pv = Program.enc P`. -/
theorem flCallLocal_eval {P : Program} {m X W f : ℕ} (hm : 1 ≤ m) (hX3 : 3 ≤ X)
    (hX : ∀ b ∈ P, b.size ≤ X) (hW : ∀ b ∈ P, (Expr.enc b).size ≤ W) (hf : 2 * f + 15 ≤ W)
    {x y : Val} {t d : ℕ} (h : EvalCall P m f x y t d) (hx : x.size ≤ m)
    {s : Regs 16} (hs0 : ∀ r : Fin 16, 2 ≤ r.val → s r = []) (hA : s rA = x.bits)
    (hfit : Fits B s)
    (hB : stateBound W X m (2 + X * d) + (Program.enc P).size + 2 ≤ B) :
    ∃ N C, Stmt.BigStep (basicSem 16) (Fits B) (flCallLocal P f) s N C (update s rB y.bits) ∧
      N ≤ flBound t (stateBound W X m (2 + X * d)) (Program.enc P).size ∧
      C ≤ N * (2 * B + 1) := by
  obtain ⟨n, hn, hr⟩ := evalCall_runAll hm hX3 hX hW hf h hx
  have hrun := flCallLocal_run hr hs0 hA hfit hB
  obtain ⟨N, C, hbs, hN, -⟩ := hrun.cost
  refine ⟨N, C, hbs, hN.trans ?_, BigStep.cost_le_fits hbs⟩
  unfold flBound callBound
  have := Nat.mul_le_mul_right (stepBound (stateBound W X m (2 + X * d)) (Program.enc P).size + 1)
    (show n + 2 ≤ 3 * t + 2 by omega)
  omega

/-! ## Placement in a larger register file -/

/-- The interpreter on the registers `ρ 0, …, ρ 15` of a register file `Fin R`
(argument `ρ 0`, result `ρ 1`, scratch `ρ 2 … ρ 15`). -/
def flCall {R : ℕ} (P : Program) (f : ℕ) (ρ : Fin 16 → Fin R) : Stmt (Instr R) :=
  renameS ρ (flCallLocal P f)

/-- **The FL interpreter.** For an injective placement `ρ`, if `P` evaluates `f x = y`
(cost `t`, depth `d`, values `≤ m`; side conditions of `Eval.encodedRun`), then from any
register file `s` with `s (ρ 0) = x.bits` and `s (ρ i) = []` for `i ≥ 2`, `flCall P f ρ` runs
to `update s (ρ 1) y.bits` — every other register, including the argument, is unchanged —
with `N ≤ flBound t SB |Pv| ≤ 700 (t+1)(SB + |Pv| + 1)` primitives and abstract cost
`C ≤ N (2B + 1)`, every visited register file in `Fits B`, for any `B ≥ SB + |Pv| + 2` with
`Fits B s`. Here `SB = stateBound W X m (2 + X·d)` and `Pv = Program.enc P`. -/
theorem flCall_eval {R : ℕ} {ρ : Fin 16 → Fin R} (hρ : Injective ρ) {P : Program}
    {m X W f : ℕ} (hm : 1 ≤ m) (hX3 : 3 ≤ X) (hX : ∀ b ∈ P, b.size ≤ X)
    (hW : ∀ b ∈ P, (Expr.enc b).size ≤ W) (hf : 2 * f + 15 ≤ W)
    {x y : Val} {t d : ℕ} (h : EvalCall P m f x y t d) (hx : x.size ≤ m)
    {s : Regs R} (hA : s (ρ 0) = x.bits) (hs0 : ∀ i : Fin 16, 2 ≤ i.val → s (ρ i) = [])
    (hfit : Fits B s)
    (hB : stateBound W X m (2 + X * d) + (Program.enc P).size + 2 ≤ B) :
    ∃ N C, Stmt.BigStep (basicSem R) (Fits B) (flCall P f ρ) s N C (update s (ρ 1) y.bits) ∧
      N ≤ flBound t (stateBound W X m (2 + X * d)) (Program.enc P).size ∧
      C ≤ N * (2 * B + 1) := by
  have hloc : Fits B (fun i => s (ρ i)) := fun i => hfit (ρ i)
  obtain ⟨N, C, hbs, hN, hC⟩ := flCallLocal_eval (B := B) hm hX3 hX hW hf h hx
    (s := fun i => s (ρ i)) hs0 hA hloc hB
  obtain ⟨t', ht', himg, hout⟩ := bigStep_rename_ext hρ s hfit hbs
  have e : t' = update s (ρ 1) y.bits := by
    funext q
    by_cases hq : ∃ i, ρ i = q
    · obtain ⟨i, rfl⟩ := hq
      rw [himg i]
      by_cases hi : i = 1
      · subst hi; simp
      · rw [update_of_ne hi, update_of_ne (fun e => hi (hρ e))]
    · push_neg at hq
      rw [hout q hq, update_of_ne (fun e => hq 1 e.symm)]
  rw [e] at ht'
  exact ⟨N, C, ht', hN, hC⟩

/-- Polynomial form of `flCall_eval`: abstract cost
`C ≤ 700 (t+1) (SB + |Pv| + 1) (2B + 1)`. -/
theorem flCall_eval_poly {R : ℕ} {ρ : Fin 16 → Fin R} (hρ : Injective ρ) {P : Program}
    {m X W f : ℕ} (hm : 1 ≤ m) (hX3 : 3 ≤ X) (hX : ∀ b ∈ P, b.size ≤ X)
    (hW : ∀ b ∈ P, (Expr.enc b).size ≤ W) (hf : 2 * f + 15 ≤ W)
    {x y : Val} {t d : ℕ} (h : EvalCall P m f x y t d) (hx : x.size ≤ m)
    {s : Regs R} (hA : s (ρ 0) = x.bits) (hs0 : ∀ i : Fin 16, 2 ≤ i.val → s (ρ i) = [])
    (hfit : Fits B s)
    (hB : stateBound W X m (2 + X * d) + (Program.enc P).size + 2 ≤ B) :
    ∃ N C, Stmt.BigStep (basicSem R) (Fits B) (flCall P f ρ) s N C (update s (ρ 1) y.bits) ∧
      N ≤ 700 * (t + 1) * (stateBound W X m (2 + X * d) + (Program.enc P).size + 1) ∧
      C ≤ 700 * (t + 1) * (stateBound W X m (2 + X * d) + (Program.enc P).size + 1) *
        (2 * B + 1) := by
  obtain ⟨N, C, hbs, hN, hC⟩ := flCall_eval hρ hm hX3 hX hW hf h hx hA hs0 hfit hB
  have hN' := hN.trans (flBound_le _ _ _)
  exact ⟨N, C, hbs, hN', hC.trans (Nat.mul_le_mul_right _ hN')⟩

/-- The same run inside oracle programs (`OInstr.basic`): `toOracle (flCall P f ρ)`. -/
theorem flCall_eval_oracle {R : ℕ} (O : OracleSpec) (callOK : Fin R → Prop)
    {ρ : Fin 16 → Fin R} (hρ : Injective ρ) {P : Program}
    {m X W f : ℕ} (hm : 1 ≤ m) (hX3 : 3 ≤ X) (hX : ∀ b ∈ P, b.size ≤ X)
    (hW : ∀ b ∈ P, (Expr.enc b).size ≤ W) (hf : 2 * f + 15 ≤ W)
    {x y : Val} {t d : ℕ} (h : EvalCall P m f x y t d) (hx : x.size ≤ m)
    {s : Regs R} (hA : s (ρ 0) = x.bits) (hs0 : ∀ i : Fin 16, 2 ≤ i.val → s (ρ i) = [])
    (hfit : Fits B s)
    (hB : stateBound W X m (2 + X * d) + (Program.enc P).size + 2 ≤ B) :
    ∃ N C, Stmt.BigStep (oracleSem O R callOK) (Fits B) (toOracle (flCall P f ρ)) s N C
        (update s (ρ 1) y.bits) ∧
      N ≤ flBound t (stateBound W X m (2 + X * d)) (Program.enc P).size ∧
      C ≤ N * (2 * B + 1) := by
  obtain ⟨N, C, hbs, hN, hC⟩ := flCall_eval hρ hm hX3 hX hW hf h hx hA hs0 hfit hB
  exact ⟨N, C, bigStep_toOracle O callOK hbs, hN, hC⟩

end QecReliability.Interp
