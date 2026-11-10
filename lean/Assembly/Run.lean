import Assembly.Program

/-!
# Assembly.Run: big-step runs of the pieces of the top-level program

`ORuns O S st s t c`: the oracle program `st` runs from `s` to `t` inside `Fits S` with
abstract cost at most `c`. One lemma per piece: `flc_run` (an FL call through the
interpreter), `moveST_run`, the two loop-body branches (`body_step_run`,
`body_invoke_run`), `preamble_run`, `postamble_run`.

The interpreter's side conditions (`X`, `W`) are computed from the program (`progX`,
`progW`), so they are not part of the contract.
-/

set_option autoImplicit false

noncomputable section
namespace QecReliability.Assembly
open RegMachine Interp FL Function

/-! ## Interpreter side conditions computed from the program -/

theorem le_foldr_max_init {α : Type} (g : α → ℕ) (z : ℕ) :
    ∀ l : List α, z ≤ l.foldr (fun e a => max (g e) a) z
  | [] => le_rfl
  | _ :: l => (le_foldr_max_init g z l).trans (le_max_right _ _)

theorem le_foldr_max {α : Type} (g : α → ℕ) (z : ℕ) :
    ∀ l : List α, ∀ b ∈ l, g b ≤ l.foldr (fun e a => max (g e) a) z
  | [], _, hb => absurd hb (List.not_mem_nil)
  | e :: l, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_max_left _ _
      · exact (le_foldr_max g z l b hb).trans (le_max_right _ _)

/-- Maximal body size (at least `3`). -/
def progX (P : Program) : ℕ := P.foldr (fun e a => max e.size a) 3

/-- Largest function index used at top level. -/
def Indices.maxIdx (I : Indices) : ℕ :=
  max I.init (max I.step (max I.isDone (max I.isInvoke (max I.query (max I.resume I.output)))))

/-- Maximal encoded body size (at least `2 * maxIdx + 15`). -/
def progW (P : Program) (I : Indices) : ℕ :=
  P.foldr (fun e a => max (Expr.enc e).size a) (2 * I.maxIdx + 15)

theorem progX_three (P : Program) : 3 ≤ progX P := le_foldr_max_init _ _ _
theorem size_le_progX (P : Program) : ∀ b ∈ P, b.size ≤ progX P := le_foldr_max _ _ _
theorem enc_le_progW (P : Program) (I : Indices) : ∀ b ∈ P, (Expr.enc b).size ≤ progW P I :=
  le_foldr_max _ _ _

theorem idx_le_progW (P : Program) (I : Indices) {f : ℕ} (hf : f ≤ I.maxIdx) :
    2 * f + 15 ≤ progW P I :=
  le_trans (by omega) (le_foldr_max_init _ _ P)

/-- Every top-level index is `≤ maxIdx`. -/
theorem Indices.le_init (I : Indices) : I.init ≤ I.maxIdx := by unfold Indices.maxIdx; omega
theorem Indices.le_step (I : Indices) : I.step ≤ I.maxIdx := by unfold Indices.maxIdx; omega
theorem Indices.le_isDone (I : Indices) : I.isDone ≤ I.maxIdx := by unfold Indices.maxIdx; omega
theorem Indices.le_isInvoke (I : Indices) : I.isInvoke ≤ I.maxIdx := by
  unfold Indices.maxIdx; omega
theorem Indices.le_query (I : Indices) : I.query ≤ I.maxIdx := by unfold Indices.maxIdx; omega
theorem Indices.le_resume (I : Indices) : I.resume ≤ I.maxIdx := by unfold Indices.maxIdx; omega
theorem Indices.le_output (I : Indices) : I.output ≤ I.maxIdx := by unfold Indices.maxIdx; omega

/-- Interpreter state bound for value budget `m` and depth `d`. -/
def stBound (P : Program) (I : Indices) (m d : ℕ) : ℕ :=
  stateBound (progW P I) (progX P) m (2 + progX P * d)

/-- Abstract cost bound of one FL call (registers `≤ S`, budget `m, t, d`). -/
def flCost (P : Program) (I : Indices) (S m t d : ℕ) : ℕ :=
  700 * (t + 1) * (stBound P I m d + (Program.enc P).size + 1) * (2 * S + 1)

theorem stateBound_mono_H {W X m H H' : ℕ} (h : H ≤ H') :
    stateBound W X m H ≤ stateBound W X m H' := by
  unfold stateBound
  exact Nat.mul_le_mul_right _ (by omega)

theorem stBound_mono_d (P : Program) (I : Indices) (m : ℕ) {d d' : ℕ} (h : d ≤ d') :
    stBound P I m d ≤ stBound P I m d' :=
  stateBound_mono_H (by have := Nat.mul_le_mul_left (progX P) h; omega)

/-! ## Oracle runs with a cost bound -/

/-- The oracle semantics used throughout (every register may be queried). -/
abbrev σO (O : OracleSpec) : PrimSem (OInstr 20) (Regs 20) := oracleSem O 20 (fun _ => True)

/-- `st` runs from `s` to `t` inside `Fits S` with abstract cost at most `c`. -/
def ORuns (O : OracleSpec) (S : ℕ) (st : Stmt (OInstr 20)) (s t : Regs 20) (c : ℕ) : Prop :=
  ∃ N C, Stmt.BigStep (σO O) (Fits S) st s N C t ∧ C ≤ c

namespace ORuns
variable {O : OracleSpec} {S : ℕ} {a b : Stmt (OInstr 20)} {s s1 t : Regs 20} {c c' c1 c2 : ℕ}

theorem mono (h : ORuns O S a s t c) (hc : c ≤ c') : ORuns O S a s t c' := by
  obtain ⟨N, C, h, hC⟩ := h
  exact ⟨N, C, h, hC.trans hc⟩

theorem seq (h1 : ORuns O S a s s1 c1) (h2 : ORuns O S b s1 t c2) :
    ORuns O S (.seq a b) s t (c1 + c2) := by
  obtain ⟨N1, C1, h1, hC1⟩ := h1
  obtain ⟨N2, C2, h2, hC2⟩ := h2
  exact ⟨_, _, .seq h1 h2, by omega⟩

theorem fits_end (h : ORuns O S a s t c) : Fits S t := by
  obtain ⟨N, C, h, -⟩ := h
  exact h.inv_end

/-- A basic run inside `Fits S` with `n` primitives costs at most `n (2S + 1)`. -/
theorem ofRuns {st : Stmt (Instr 20)} {n : ℕ} (h : Runs S st s t n) :
    ORuns O S (toOracle st) s t (n * (2 * S + 1)) := by
  obtain ⟨N, C, h, -, hC⟩ := h.cost
  exact ⟨N, C, bigStep_toOracle O (fun _ => True) h, hC⟩

theorem ofBasic {st : Stmt (Instr 20)} {N C : ℕ}
    (h : Stmt.BigStep (basicSem 20) (Fits S) st s N C t) (hC : C ≤ c) :
    ORuns O S (toOracle st) s t c :=
  ⟨N, C, bigStep_toOracle O (fun _ => True) h, hC⟩

theorem iteT {tp : OInstr 20} {a' : Stmt (OInstr 20)} (hs : Fits S s) (hp : (σO O).pre tp s)
    (he : (σO O).eval tp s = (s, true)) (h : ORuns O S a s t c) :
    ORuns O S (.ite tp a a') s t ((σO O).cost tp s + c) := by
  obtain ⟨N, C, h, hC⟩ := h
  exact ⟨_, _, Stmt.BigStep.iteT hs hp he h, by omega⟩

theorem iteF {tp : OInstr 20} {a' : Stmt (OInstr 20)} (hs : Fits S s) (hp : (σO O).pre tp s)
    (he : (σO O).eval tp s = (s, false)) (h : ORuns O S a' s t c) :
    ORuns O S (.ite tp a a') s t ((σO O).cost tp s + c) := by
  obtain ⟨N, C, h, hC⟩ := h
  exact ⟨_, _, Stmt.BigStep.iteF hs hp he h, by omega⟩

end ORuns

/-- Every primitive of the oracle semantics costs at least `1`, so the number of executed
primitives is at most the abstract cost. -/
theorem OInstr.one_le_cost (O : OracleSpec) (p : OInstr 20) (s : Regs 20) :
    1 ≤ (σO O).cost p s := by
  cases p with
  | basic i => cases i <;> (simp [σO, oracleSem, OInstr.cost, Instr.cost]; try omega)
  | call q => simp [σO, oracleSem, OInstr.cost]; omega

theorem BigStep.steps_le_cost {O : OracleSpec} {Inv : Regs 20 → Prop} {st : Stmt (OInstr 20)}
    {s t : Regs 20} {N C : ℕ} (h : Stmt.BigStep (σO O) Inv st s N C t) : N ≤ C := by
  induction h with
  | @prim p s _ _ _ _ _ _ => exact OInstr.one_le_cost O p s
  | seq _ _ ih1 ih2 => omega
  | @iteT tp _ _ s _ _ _ _ _ _ _ _ ih =>
      have := OInstr.one_le_cost O tp s; omega
  | @iteF tp _ _ s _ _ _ _ _ _ _ _ ih =>
      have := OInstr.one_le_cost O tp s; omega
  | @loopF tp _ _ _ s _ _ _ _ _ _ => exact OInstr.one_le_cost O tp s
  | @loopT tp _ _ s _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
      have := OInstr.one_le_cost O tp s; omega

/-! ## One FL call -/

/-- **An FL call inside the top-level program.** -/
theorem flc_run {O : OracleSpec} {P : Program} {I : Indices} {f : ℕ} (hf : f ≤ I.maxIdx)
    {res : Fin 20} (hres : 2 ≤ res.val ∧ res.val ≤ 5) {m t d S : ℕ} {x y : Val}
    (h : FL.Computes P f x y m t d) {s : Regs 20} (hx : s rST = x.bits)
    (hs0 : ∀ r : Fin 20, 6 ≤ r.val → s r = []) (hfit : Fits S s)
    (hS : stBound P I m d + (Program.enc P).size + 2 ≤ S) :
    ORuns O S (flc P f res) s (update s res y.bits) (flCost P I S m t d) := by
  obtain ⟨hxm, t', d', ht, hd, e⟩ := h
  have hm : 1 ≤ m := lt_of_lt_of_le (Val.size_pos x) hxm
  have hB : stateBound (progW P I) (progX P) m (2 + progX P * d') + (Program.enc P).size + 2
      ≤ S := (Nat.add_le_add_right (Nat.add_le_add_right (stBound_mono_d P I m hd) _) _).trans hS
  have hsc : ∀ i : Fin 16, 2 ≤ i.val → s (place res i) = [] := fun i hi =>
    hs0 _ (by rw [place_scratch res i hi]; omega)
  obtain ⟨N, C, hbs, hN, hC⟩ := flCall_eval_oracle (B := S) O (fun _ => True)
    (place_injective hres) hm (progX_three P) (size_le_progX P) (enc_le_progW P I)
    (idx_le_progW P I hf) e hxm hx hsc hfit hB
  refine ⟨N, C, hbs, hC.trans ?_⟩
  have hN' := hN.trans (flBound_le _ _ _)
  have h1 : 700 * (t' + 1) * (stateBound (progW P I) (progX P) m (2 + progX P * d') +
      (Program.enc P).size + 1) ≤
      700 * (t + 1) * (stBound P I m d + (Program.enc P).size + 1) := by
    apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
    have := stBound_mono_d P I m hd
    unfold stBound at this ⊢
    omega
  unfold flCost
  exact Nat.mul_le_mul_right _ (hN'.trans h1)

/-- `flc_run` on a register file of the form `regsOf`. -/
theorem flc_regsOf {O : OracleSpec} {P : Program} {I : Indices} {f : ℕ} (hf : f ≤ I.maxIdx)
    {res : Fin 20} (hres : 2 ≤ res.val ∧ res.val ≤ 5) {m t d S : ℕ} {x y : Val}
    (h : FL.Computes P f x y m t d) {tmp dn q out : List Bool}
    (hfit : Fits S (regsOf x.bits tmp dn q out))
    (hS : stBound P I m d + (Program.enc P).size + 2 ≤ S) :
    ORuns O S (flc P f res) (regsOf x.bits tmp dn q out)
      (update (regsOf x.bits tmp dn q out) res y.bits) (flCost P I S m t d) :=
  flc_run hf hres h rfl (fun r hr => regsOf_scratch _ _ _ _ _ r hr) hfit hS

theorem hTMP : 2 ≤ rTMP.val ∧ rTMP.val ≤ 5 := by decide
theorem hDN : 2 ≤ rDN.val ∧ rDN.val ≤ 5 := by decide

/-! ## Small pieces -/

theorem moveST_run {O : OracleSpec} {S : ℕ} {st w dn q out : List Bool}
    (hfit : Fits S (regsOf st w dn q out)) :
    ORuns O S moveST (regsOf st w dn q out) (regsOf w [] dn q out) (3 * (2 * S + 1)) := by
  have h1 := Runs.clear hfit rST
  rw [update_regsOf_ST] at h1
  have h2 := Runs.append (d := rST) (r := rTMP) (x := []) (y := w) h1.fits_end (by decide)
    (by simp) (by simp) (by simpa using hfit rTMP)
  rw [update_regsOf_ST] at h2
  have h3 := Runs.clear h2.fits_end rTMP
  rw [update_regsOf_TMP] at h3
  exact ORuns.ofRuns (h1.seq (h2.seq h3))

theorem pf_run {O : OracleSpec} {S : ℕ} (b : Bool) {st tmp dn q out : List Bool}
    (hfit : Fits S (regsOf st tmp dn q out)) (hl : st.length + 1 ≤ S) :
    ORuns O S (pf b) (regsOf st tmp dn q out) (regsOf (b :: st) tmp dn q out) (2 * S + 1) := by
  have ht : Fits S (regsOf (b :: st) tmp dn q out) := by
    rw [← update_regsOf_ST st tmp dn q out (b :: st)]
    exact fits_upd hfit (by simpa using hl)
  refine ⟨1, _, Stmt.BigStep.prim (σ := σO O) (p := .basic (.pushFront rST b)) (b := true) hfit trivial
    (by simp [σO, oracleSem, OInstr.eval, Instr.eval, update_regsOf_ST]) ht, ?_⟩
  have := hfit rST
  simp only [σO, oracleSem, OInstr.cost, Instr.cost, regsOf_ST] at this ⊢
  omega

/-- Bits of the resume argument `(answer, state)`. -/
theorem pair_bits (b : Bool) (v : Val) :
    (Val.cons (Enc.bool b) v).bits =
      (if b then [true, true, false, false] else [true, false]) ++ v.bits := by
  cases b <;> rfl

theorem pairT_run {O : OracleSpec} {S : ℕ} {v : Val} {tmp dn q out : List Bool}
    (hfit : Fits S (regsOf v.bits tmp dn q out)) (hl : v.bits.length + 4 ≤ S) :
    ORuns O S pairT (regsOf v.bits tmp dn q out)
      (regsOf (Val.cons (Enc.bool true) v).bits tmp dn q out) (4 * (2 * S + 1)) := by
  rw [pair_bits]
  have h1 := pf_run (O := O) false hfit (by omega)
  have h2 := pf_run (O := O) false h1.fits_end (by simp only [List.length_cons]; omega)
  have h3 := pf_run (O := O) true h2.fits_end (by simp only [List.length_cons]; omega)
  have h4 := pf_run (O := O) true h3.fits_end (by simp only [List.length_cons]; omega)
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by omega)

theorem pairF_run {O : OracleSpec} {S : ℕ} {v : Val} {tmp dn q out : List Bool}
    (hfit : Fits S (regsOf v.bits tmp dn q out)) (hl : v.bits.length + 4 ≤ S) :
    ORuns O S pairF (regsOf v.bits tmp dn q out)
      (regsOf (Val.cons (Enc.bool false) v).bits tmp dn q out) (4 * (2 * S + 1)) := by
  rw [pair_bits]
  have h1 := pf_run (O := O) false hfit (by omega)
  have h2 := pf_run (O := O) true h1.fits_end (by simp only [List.length_cons]; omega)
  exact (h1.seq h2).mono (by omega)

theorem length_le_encBits (w : List Bool) : w.length ≤ (encBits w).length := by
  rw [encBits_eq]
  induction w with
  | nil => simp
  | cons x w ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      have : 1 ≤ (elemBits x).length := by cases x <;> simp [elemBits]
      omega

theorem two_mul_length_le_encBits (w : List Bool) : 2 * w.length + 1 ≤ (encBits w).length := by
  rw [encBits_eq]
  induction w with
  | nil => simp
  | cons x w ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
      have : 2 ≤ (elemBits x).length := by cases x <;> simp [elemBits]
      omega

/-- `Q := raw (TMP)`, `TMP := []` on a file of the form `regsOf`. -/
theorem valToRaw_Q_run {O : OracleSpec} {S : ℕ} {st dn out w : List Bool}
    (hfit : Fits S (regsOf st (encBits w) dn [] out)) :
    ORuns O S (toOracle (valToRaw rQ rTMP)) (regsOf st (encBits w) dn [] out)
      (regsOf st [] dn w out) ((S + 2) * (12 * (S + S + 3))) := by
  have hw : (encBits w).length ≤ S := by simpa using hfit rTMP
  have hwl := length_le_encBits w
  obtain ⟨N, C, h, hC⟩ := valToRaw_run (S := S) (dst := rQ) (src := rTMP) (by decide) w _
    (by simp) hfit (by simp; omega)
  rw [regsOf_Q, List.nil_append, update_regsOf_Q, update_regsOf_TMP] at h
  refine ORuns.ofBasic h (hC.trans ?_)
  simp only [regsOf_Q, List.length_nil, zero_add]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- `OUT := raw (TMP)`, `TMP := []`. -/
theorem valToRaw_OUT_run {O : OracleSpec} {S : ℕ} {st dn q w : List Bool}
    (hfit : Fits S (regsOf st (encBits w) dn q [])) :
    ORuns O S (toOracle (valToRaw rOUT rTMP)) (regsOf st (encBits w) dn q [])
      (regsOf st [] dn q w) ((S + 2) * (12 * (S + S + 3))) := by
  have hw : (encBits w).length ≤ S := by simpa using hfit rTMP
  have hwl := length_le_encBits w
  obtain ⟨N, C, h, hC⟩ := valToRaw_run (S := S) (dst := rOUT) (src := rTMP) (by decide) w _
    (by simp) hfit (by simp; omega)
  rw [regsOf_OUT, List.nil_append, update_regsOf_OUT, update_regsOf_TMP] at h
  refine ORuns.ofBasic h (hC.trans ?_)
  simp only [regsOf_OUT, List.length_nil, zero_add]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- `ST := encBits IN`, `IN := []`. -/
theorem rawToVal_run' {O : OracleSpec} {S : ℕ} {input : List Bool}
    (hfit : Fits S (inputRegs (R := 19) input)) (hl : 4 * input.length + 1 ≤ S) :
    ORuns O S (toOracle (rawToVal rST rIN)) (inputRegs (R := 19) input)
      (regsOf (encBits input) [] [] [] []) ((S + 2) * (8 * (S + 4))) := by
  have hST : inputRegs (R := 19) input rST = [] := by simp [inputRegs, rST]
  obtain ⟨N, C, h, hC⟩ := rawToVal_run (S := S) (dst := rST) (src := rIN) (by decide) input _
    (by simp [inputRegs, rIN]) hfit (by rw [hST]; simp; omega)
  rw [rawToVal_regs] at h
  refine ORuns.ofBasic h (hC.trans ?_)
  rw [hST]
  simp only [List.length_nil, zero_add]
  exact Nat.mul_le_mul (by omega) (by omega)

end QecReliability.Assembly

end
