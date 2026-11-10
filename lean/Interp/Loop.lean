import Interp.Cases

/-!
# The interpreter loop

`interpLoop = while rH = [] do stepS`. From a CEK run `RunAll P Q st n (ret y [])` whose
states all have encodings of size `≤ SB`, the loop runs from `rS = st.enc.bits` (scratch
registers empty, `rP = Program.enc P`) to `rS = y.bits`, `rH = [true]`, all other registers
unchanged, with at most `(n+1)·(stepBound SB |Pv| + 1) + 1` primitives (`interpLoop_run`).
-/

set_option autoImplicit false

namespace QecReliability.Interp
open QecReliability.RegMachine QecReliability.FL Function

local notation "rS" => (2 : Fin 16)
local notation "rP" => (3 : Fin 16)
local notation "rH" => (4 : Fin 16)

variable {B : ℕ}

/-- `while rH = [] do stepS`. -/
def interpLoop : Stmt (Instr 16) := .loop (.isEmpty rH) true stepS

theorem stepBound_mono {a a' p : ℕ} (h : a ≤ a') : stepBound a p ≤ stepBound a' p := by
  unfold stepBound; omega

theorem interpLoop_run {P : Program} {SB : ℕ} {st : State} {n : ℕ} {y : Val}
    (hr : RunAll P (fun z => z.enc.size ≤ SB) st n (.ret y [])) :
    ∀ s : Regs 16, Clean s → Fits B s → s rS = st.enc.bits → s rP = (Program.enc P).bits →
      SB + (Program.enc P).size + 2 ≤ B →
      Runs B interpLoop s (update (update s rS y.bits) rH [true])
        ((n + 1) * (stepBound SB (Program.enc P).size + 1) + 1) := by
  generalize hfin : State.ret y [] = fin at hr
  induction hr with
  | @refl st hq =>
    intro s hc hfit hS _ hB
    subst hfin
    have hsz : (State.ret y []).enc.size = y.size + 6 := by
      simp [State.enc, tagged, stackEnc, Enc.list, Enc.unary]; omega
    have hy : y.size + 1 ≤ B := by omega
    have hH : s rH = [] := hc rH (by decide)
    have h1 := stepS_halt hfit hS hc hy
    have hf1 := h1.fits_end
    have h2 := Runs.loopF (tp := .isEmpty rH) (pol := true) (c := false) (body := stepS) hf1
      trivial (by simp [Instr.eval]) (by decide)
    have := Runs.loopT (tp := .isEmpty rH) (pol := true) hfit trivial
      (by simp [Instr.eval, hH]) h1 h2
    refine this.mono ?_
    have : 5 * y.size + 25 ≤ stepBound SB (Program.enc P).size := by
      unfold stepBound; omega
    omega
  | @step st st' n' fin' hq hs hrest ih =>
    intro s hc hfit hS hP hB
    have hq' : st'.enc.size ≤ SB := hrest.first
    have h1 := stepS_run hs hc hfit hS hP (by omega) (by omega)
    have hc1 : Clean (update s rS st'.enc.bits) := hc.upd_S _
    have h2 := ih hfin _ hc1 h1.fits_end (by simp) (by rw [update_of_ne (by decide)]; exact hP) hB
    rw [update_idem] at h2
    have := Runs.loopT (tp := .isEmpty rH) (pol := true) hfit trivial
      (by simp [Instr.eval, hc rH (by decide)]) h1 h2
    refine this.mono ?_
    have := stepBound_mono (p := (Program.enc P).size) hq
    have e := Nat.add_mul (n' + 1) 1 (stepBound SB (Program.enc P).size + 1)
    rw [Nat.one_mul] at e
    omega

end QecReliability.Interp
