import Assembly.Run

/-!
# Assembly.Body: one loop iteration, preamble and postamble

All statements are at the level of FL facts (`FL.Computes` with a fixed budget `m, t, d`)
and register files of the form `regsOf`; the registers stay inside `Fits S` as soon as
`S ≥ stBound P I m d + |Pv| + 2` and `S ≥ 2m + 4`.
-/

set_option autoImplicit false

noncomputable section
namespace QecReliability.Assembly
open RegMachine Interp FL Function

/-- Flag register contents. -/
abbrev dnBits (b : Bool) : List Bool := (Enc.bool b).bits

theorem dnBits_length_le (b : Bool) : (dnBits b).length ≤ 3 := by cases b <;> simp [Enc.bool]

/-- Cost of one loop iteration, SAT time excluded. -/
def bodyCost (P : Program) (I : Indices) (S m t d : ℕ) : ℕ :=
  4 * flCost P I S m t d + (S + 2) * (12 * (S + S + 3)) + 10 * (2 * S + 1)

/-- Cost of the preamble. -/
def preCost (P : Program) (I : Indices) (S m t d : ℕ) : ℕ :=
  (S + 2) * (8 * (S + 4)) + 2 * flCost P I S m t d + 3 * (2 * S + 1)

/-- Cost of the postamble. -/
def postCost (P : Program) (I : Indices) (S m t d : ℕ) : ℕ :=
  flCost P I S m t d + (S + 2) * (12 * (S + S + 3))

section
variable {O : OracleSpec} {P : Program} {I : Indices} {S m t d : ℕ}

theorem headIs_eval (r : Fin 20) (s : Regs 20) (b : Bool) (hb : s r = dnBits b) :
    (σO O).eval (.basic (.headIs r true)) s = (s, b) := by
  cases b <;> (simp only [σO, oracleSem, OInstr.eval, Instr.eval, hb]; rfl)

theorem fits_start {vs : Val} {b : Bool} (hm : 2 * m + 4 ≤ S) (hv : vs.size ≤ m) :
    Fits S (regsOf vs.bits [] (dnBits b) [] []) :=
  fits_regsOf _ _ _ _ _ (by simp; omega) (by simp) (by have := dnBits_length_le b; omega)
    (by simp) (by simp)

/-- **Ordinary edge.** -/
theorem body_step_run {vs vs' : Val} {dn' : Bool}
    (hS : stBound P I m d + (Program.enc P).size + 2 ≤ S) (hm : 2 * m + 4 ≤ S)
    (hinv : FL.Computes P I.isInvoke vs (Enc.bool false) m t d)
    (hstep : FL.Computes P I.step vs vs' m t d)
    (hdone : FL.Computes P I.isDone vs' (Enc.bool dn') m t d) :
    ORuns O S (body P I) (regsOf vs.bits [] (dnBits false) [] [])
      (regsOf vs'.bits [] (dnBits dn') [] []) (bodyCost P I S m t d) := by
  have hfit0 := fits_start (b := false) hm hinv.1
  have h1 := flc_regsOf (O := O) I.le_isInvoke hTMP hinv hfit0 hS
  rw [update_regsOf_TMP] at h1
  have h2 := flc_regsOf (O := O) I.le_step hTMP hstep h1.fits_end hS
  rw [update_regsOf_TMP] at h2
  have h3 := moveST_run (O := O) h2.fits_end
  have h4 := flc_regsOf (O := O) I.le_isDone hDN hdone h3.fits_end hS
  rw [update_regsOf_DN] at h4
  have hb : ORuns O S (.ite (.basic (.headIs rTMP true)) (invokeBranch P I) (stepBranch P I))
      (regsOf vs.bits (dnBits false) (dnBits false) [] [])
      (regsOf vs'.bits [] (dnBits false) [] []) (1 + (flCost P I S m t d + 3 * (2 * S + 1))) :=
    ORuns.iteF h1.fits_end trivial (headIs_eval rTMP _ false rfl) (h2.seq h3)
  refine (h1.seq (hb.seq h4)).mono ?_
  unfold bodyCost
  generalize (S + 2) * (12 * (S + S + 3)) = V
  omega

/-- **SAT edge.** The oracle answer `O.oracle qw` is passed to `resume`. -/
theorem body_invoke_run {vs vs' : Val} {dn' : Bool} {qw : List Bool}
    (hS : stBound P I m d + (Program.enc P).size + 2 ≤ S) (hm : 2 * m + 4 ≤ S)
    (hinv : FL.Computes P I.isInvoke vs (Enc.bool true) m t d)
    (hq : FL.Computes P I.query vs (bitsVal qw) m t d) (hok : O.qok qw)
    (hres : FL.Computes P I.resume (Val.cons (Enc.bool (O.oracle qw)) vs) vs' m t d)
    (hdone : FL.Computes P I.isDone vs' (Enc.bool dn') m t d) :
    ORuns O S (body P I) (regsOf vs.bits [] (dnBits false) [] [])
      (regsOf vs'.bits [] (dnBits dn') [] []) (bodyCost P I S m t d + O.ocost qw) := by
  have hvm := hinv.1
  have hfit0 := fits_start (b := false) hm hvm
  have h1 := flc_regsOf (O := O) I.le_isInvoke hTMP hinv hfit0 hS
  rw [update_regsOf_TMP] at h1
  have h2 := flc_regsOf (O := O) I.le_query hTMP hq h1.fits_end hS
  rw [update_regsOf_TMP] at h2
  have h3 := valToRaw_Q_run (O := O) (w := qw) h2.fits_end
  have hqS : qw.length ≤ S := by have := h3.fits_end rQ; simpa using this
  have hvS : vs.bits.length + 4 ≤ S := by simp; omega
  -- the SAT call and the pair
  set ans := O.oracle qw with hans
  have h4 : ORuns O S (.ite (.call rQ) pairT pairF) (regsOf vs.bits [] (dnBits false) qw [])
      (regsOf (Val.cons (Enc.bool ans) vs).bits [] (dnBits false) qw [])
      ((1 + qw.length + O.ocost qw) + 4 * (2 * S + 1)) := by
    have hev : (σO O).eval (.call rQ) (regsOf vs.bits [] (dnBits false) qw []) =
        (regsOf vs.bits [] (dnBits false) qw [], ans) := by
      simp [σO, oracleSem, OInstr.eval, hans]
    have hcost : (σO O).cost (.call rQ) (regsOf vs.bits [] (dnBits false) qw []) =
        1 + qw.length + O.ocost qw := by
      simp [σO, oracleSem, OInstr.cost]
    have hpre : (σO O).pre (.call rQ) (regsOf vs.bits [] (dnBits false) qw []) := by
      simp only [σO, oracleSem, OInstr.pre, regsOf_Q]
      exact ⟨hok, trivial⟩
    rw [← hcost]
    cases hb : ans with
    | true =>
        rw [hb] at hev
        exact ORuns.iteT h3.fits_end hpre hev (pairT_run h3.fits_end hvS)
    | false =>
        rw [hb] at hev
        exact ORuns.iteF h3.fits_end hpre hev (pairF_run h3.fits_end hvS)
  have h5 : ORuns O S (.prim (.basic (.clear rQ)))
      (regsOf (Val.cons (Enc.bool ans) vs).bits [] (dnBits false) qw [])
      (regsOf (Val.cons (Enc.bool ans) vs).bits [] (dnBits false) [] []) (1 * (2 * S + 1)) := by
    have := Runs.clear h4.fits_end rQ
    rw [update_regsOf_Q] at this
    exact ORuns.ofRuns this
  have h6 := flc_regsOf (O := O) I.le_resume hTMP hres h5.fits_end hS
  rw [update_regsOf_TMP] at h6
  have h7 := moveST_run (O := O) h6.fits_end
  have h8 := flc_regsOf (O := O) I.le_isDone hDN hdone h7.fits_end hS
  rw [update_regsOf_DN] at h8
  have hbr : ORuns O S (invokeBranch P I) (regsOf vs.bits (dnBits true) (dnBits false) [] [])
      (regsOf vs'.bits [] (dnBits false) [] [])
      (flCost P I S m t d + ((S + 2) * (12 * (S + S + 3)) + (((1 + qw.length + O.ocost qw) +
        4 * (2 * S + 1)) + (1 * (2 * S + 1) + (flCost P I S m t d + 3 * (2 * S + 1)))))) :=
    h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7))))
  have hb : ORuns O S (.ite (.basic (.headIs rTMP true)) (invokeBranch P I) (stepBranch P I))
      (regsOf vs.bits (dnBits true) (dnBits false) [] [])
      (regsOf vs'.bits [] (dnBits false) [] []) _ :=
    ORuns.iteT h1.fits_end trivial (headIs_eval rTMP _ true rfl) hbr
  refine (h1.seq (hb.seq h8)).mono ?_
  simp only [σO, oracleSem, OInstr.cost, Instr.cost]
  unfold bodyCost
  linarith

/-- **Preamble.** -/
theorem preamble_run {input : List Bool} {v0 : Val} {dn0 : Bool}
    (hS : stBound P I m d + (Program.enc P).size + 2 ≤ S) (hm : 2 * m + 4 ≤ S)
    (hinit : FL.Computes P I.init (bitsVal input) v0 m t d)
    (hdone : FL.Computes P I.isDone v0 (Enc.bool dn0) m t d) :
    ORuns O S (preamble P I) (inputRegs (R := 19) input)
      (regsOf v0.bits [] (dnBits dn0) [] []) (preCost P I S m t d) := by
  have hin : (encBits input).length ≤ m := by
    have := hinit.1
    simpa [encBits] using this
  have h2l := two_mul_length_le_encBits input
  have hfit : Fits S (inputRegs (R := 19) input) := by
    intro r
    by_cases hr : r = 0
    · simp [inputRegs, hr]; omega
    · simp [inputRegs, hr]
  have h1 := rawToVal_run' (O := O) hfit (by omega)
  have h2 := flc_regsOf (O := O) I.le_init hTMP (x := bitsVal input) hinit h1.fits_end hS
  rw [update_regsOf_TMP] at h2
  have h3 := moveST_run (O := O) h2.fits_end
  have h4 := flc_regsOf (O := O) I.le_isDone hDN hdone h3.fits_end hS
  rw [update_regsOf_DN] at h4
  refine (h1.seq (h2.seq (h3.seq h4))).mono ?_
  unfold preCost
  omega

/-- **Postamble.** -/
theorem postamble_run {vs : Val} {w dn : List Bool}
    (hS : stBound P I m d + (Program.enc P).size + 2 ≤ S)
    (hout : FL.Computes P I.output vs (bitsVal w) m t d)
    (hfit : Fits S (regsOf vs.bits [] dn [] [])) :
    ORuns O S (postamble P I) (regsOf vs.bits [] dn [] []) (regsOf vs.bits [] dn [] w)
      (postCost P I S m t d) := by
  have h1 := flc_regsOf (O := O) I.le_output hTMP hout hfit hS
  rw [update_regsOf_TMP] at h1
  have h2 := valToRaw_OUT_run (O := O) (w := w) h1.fits_end
  exact h1.seq h2

end

end QecReliability.Assembly

end
