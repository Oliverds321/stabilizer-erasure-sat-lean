import Assembly.Instance

/-!
# Assembly.Main: `MainTheorem` from the component bundle

`main_of_components`: for any fixed hash certificate `A`, if for every SAT density the
component bundle `Components hD hd A density` is available, then
`QecReliability.Final.MainTheorem` holds.

The machine is `theMachine E P I`: the compiled top-level register program
(`mainProg P I`, 20 registers on tapes `0 … 19`) with the SAT machine `E` embedded on the
tapes `20 … 20 + kE`; the output tape is register `rOUT`.
-/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

noncomputable section
namespace QecReliability.Assembly
open RegMachine Interp FL Function
open OracleCost OracleCost.MultiTape OracleCost.MultiTape.InjectiveTapeLift
open OracleCost.WholeWrapperCandidate
open SharedCircuit SharedCircuit.LatentEncoding RationalOutput QecPhysical QecPhysical.Stabilizer
open Final SharedCircuit.FixedLocalEmitter.AllLength FiniteLocalSelectorCandidate
open OracleCost.StoredCodeHashConfidence

/-! ## The machine -/

section Machine
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]

/-- The top-level machine: compiled register program with the SAT machine embedded. -/
abbrev theMachine (E : Machine kE ΓE ΛE) (P : Program) (I : Indices) :=
  oracleMachine E (stdEngEmb 19 kE) (((mainProg P I).toProg).map (stdRegEmb 19 kE))

/-- The output tape (register `rOUT`). -/
abbrev outTape (kE : ℕ) : Fin (19 + kE + 1 + 1) := stdRegEmb 19 kE rOUT

/-- From an abstract run of the main program body to a completed machine run. -/
theorem complete_of_oruns {E : Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope}
    {T : ℕ → ℕ} (spec : EncodedSAT E density PtE PsE T) {P : Program} {I : Indices}
    {Lq S Cst : ℕ} {bits : List Bool} {u : Regs 20} {r : ℕ} {v : RationalOutput.Vector r}
    (h : ORuns (satOracle E density Lq) S (mainProg P I).body (inputRegs (R := 19) bits) u Cst)
    (hout : u rOUT = outputWord v) :
    ∃ run : Completed (theMachine E P I) bits,
      Outputs (theMachine E P I) run (outTape kE) v ∧
      run.time ≤ (3 * kE + 6) * (Cst + 1) ∧
      run.cells ≤ (19 + kE + 1 + 1) * (2 * max S (PsE.eval Lq) + 3) := by
  obtain ⟨N, C, hbs, hC⟩ := h
  have hN := BigStep.steps_le_cost hbs
  obtain ⟨run, -, htime, hcells, htapes⟩ := oracle_sprog_completed E (stdRegEmb 19 kE)
    (stdEngEmb 19 kE) (stdRegEmb_zero 19 kE) (std_disjoint 19 kE) (satOracle E density Lq)
    (satOracle_spec spec Lq).2 (mainProg P I) hbs trivial rfl hbs.inv_end
  refine ⟨run, ?_, ?_, hcells⟩
  · have hin : (theMachine E P I).inputSymbol = RegSyms.sym :=
      oGadget_input E (stdEngEmb 19 kE) _
    unfold Outputs
    rw [htapes rOUT, hout, hin]
  · have h1 : (oracleSem (satOracle E density Lq) (19 + 1) fun _ => True).cost
        (mainProg P I).final u = 1 := rfl
    rw [h1] at htime
    have h2 : (3 * kE + 5) * (C + 1) ≤ (3 * kE + 5) * (Cst + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : (3 * kE + 6) * (Cst + 1) = (3 * kE + 5) * (Cst + 1) + (Cst + 1) := by ring
    omega

end Machine

/-! ## Arithmetic -/

theorem one_le_mul_of {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x * y := by
  have := Nat.mul_le_mul hx hy
  rwa [Nat.one_mul] at this

theorem time_arith {pre post K disp oT Y Bp Q Tx : ℕ}
    (hdisp : disp ≤ 4096 * Y * Bp) (hoT : oT ≤ 384 * Y * Bp * Q * Tx) (hY : 1 ≤ Y)
    (hBp : 1 ≤ Bp) :
    pre + (disp + 1) * (K + 1) + oT + post ≤
      (4097 * Y * (pre + post + (K + 1)) + 384 * Y * Q) * Bp * (Tx + 1) := by
  have hZ : 1 ≤ Y * Bp * (Tx + 1) := one_le_mul_of (one_le_mul_of hY hBp) (Nat.succ_pos _)
  have h1 : pre + post ≤ (pre + post) * (Y * Bp * (Tx + 1)) := Nat.le_mul_of_pos_right _ hZ
  have h2 : (disp + 1) * (K + 1) ≤ 4097 * (Y * Bp) * (K + 1) := by
    apply Nat.mul_le_mul_right
    have : 1 ≤ Y * Bp := one_le_mul_of hY hBp
    have e : 4096 * Y * Bp = 4096 * (Y * Bp) := by ring
    omega
  have h3 : 4097 * (Y * Bp) * (K + 1) ≤ 4097 * (Y * Bp) * (K + 1) * (Tx + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h4 : 384 * Y * Bp * Q * Tx ≤ 384 * Y * Bp * Q * (Tx + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e : (4097 * Y * (pre + post + (K + 1)) + 384 * Y * Q) * Bp * (Tx + 1) =
      4097 * ((pre + post) * (Y * Bp * (Tx + 1))) + 4097 * (Y * Bp) * (K + 1) * (Tx + 1) +
        384 * Y * Bp * Q * (Tx + 1) := by ring
  rw [e]
  generalize (pre + post) * (Y * Bp * (Tx + 1)) = X1 at h1 ⊢
  generalize 4097 * (Y * Bp) * (K + 1) * (Tx + 1) = X2 at h3 ⊢
  generalize 4097 * (Y * Bp) * (K + 1) = X3 at h2 h3
  generalize 384 * Y * Bp * Q * (Tx + 1) = X4 at h4 ⊢
  generalize 384 * Y * Bp * Q * Tx = X5 at hoT h4
  generalize (disp + 1) * (K + 1) = X6 at h2 ⊢
  omega

theorem coins_arith (L s : ℕ) : (6 * L + 5) * (s * (2 * L)) ≤ 12 * s * (L + 1) ^ 2 := by
  have h1 : 6 * L + 5 ≤ 6 * (L + 1) := by omega
  have h2 : s * (2 * L) ≤ s * (2 * (L + 1)) := Nat.mul_le_mul_left _ (by omega)
  calc (6 * L + 5) * (s * (2 * L)) ≤ (6 * (L + 1)) * (s * (2 * (L + 1))) := Nat.mul_le_mul h1 h2
    _ = 12 * s * (L + 1) ^ 2 := by ring

/-! ## One instance on the machine -/

section Instance
variable {D t : ℕ} {hD : D = 16^384} {hd : D = 256*t}
    {A : FiniteLocalSelectorCandidate.CertifiedParity (512*t) (64*t) t}
variable {density : ℕ} (Cm : Components hD hd A density)
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}

/-- Time polynomial (before the `B` and `T` factors). -/
def timeCore (P : Program) (I : Indices) (Bd : Budget) (G density : ℕ)
    (PtE PsE : PolynomialEnvelope) (L : ℕ) : ℕ :=
  4097 * (L + 1) ^ 4 * (preBound P I Bd L + postBound P I Bd L +
      (iterBound P I Bd L + PsE.eval (qcap G density L) + 1)) +
    384 * (L + 1) ^ 4 * PtE.eval (qcap G density L)

/-- Space polynomial. -/
def spaceCore (P : Program) (I : Indices) (Bd : Budget) (G density kE : ℕ)
    (PsE : PolynomialEnvelope) (L : ℕ) : ℕ :=
  (19 + kE + 1 + 1) * (2 * max (regBound P I Bd L) (PsE.eval (qcap G density L)) + 3)

theorem timeCore_poly (P : Program) (I : Indices) (Bd : Budget) (G density kE : ℕ)
    (PtE PsE : PolynomialEnvelope) :
    PolyBounded (fun L => (3 * kE + 6) * (timeCore P I Bd G density PtE PsE L + 1)) := by
  have h1 := preBound_poly P I Bd
  have h2 := postBound_poly P I Bd
  have h3 := iterBound_poly P I Bd
  have h4 := qcap_poly G density
  unfold timeCore
  poly_bounded

theorem spaceCore_poly (P : Program) (I : Indices) (Bd : Budget) (G density kE : ℕ)
    (PsE : PolynomialEnvelope) : PolyBounded (spaceCore P I Bd G density kE PsE) := by
  have h1 := regBound_poly P I Bd
  have h4 := qcap_poly G density
  unfold spaceCore
  poly_bounded

/-- **Every instance, on the machine.** -/
theorem machine_instance (spec : EncodedSAT E density PtE PsE T) (hT : Monotone T)
    (n : ℕ) (rows : List (List (PauliCoord n))) {a b c d : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd' : 0 < d)
    (coins : Fin (coinBits hD hd A c d n) → Bool) (bits : List Bool)
    (hbits : bits = machineInput rows a b c d (List.ofFn coins)) :
    ∃ run : Completed (theMachine E Cm.P Cm.idx) bits,
      Outputs (theMachine E Cm.P Cm.idx) run (outTape kE)
        (macroRun hD hd A spec a b c d n rows (coinWord hD hd A c d n coins)) ∧
      run.time ≤ (3 * kE + 6) * (timeCore Cm.P Cm.idx Cm.budget (gateConstant hD hd A) density
          PtE PsE (paperL rows a b c d) + 1) * (rationalCellBudget a b + 1) *
        (T (variableConstant (gateConstant hD hd A) density * (n + rowIncidences rows + 1)) + 1) ∧
      run.cells ≤ spaceCore Cm.P Cm.idx Cm.budget (gateConstant hD hd A) density kE PsE
        (paperL rows a b c d) := by
  subst hbits
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have MM := macro_main hD hd A spec hT a b c d ha hb hc hd' hab
  set L := paperL rows a b c d with hL
  set G := gateConstant hD hd A with hG
  have hY : 1 ≤ (L + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hscale : ∀ Cst : ℕ, Cst ≤ timeCore Cm.P Cm.idx Cm.budget G density PtE PsE L *
        (rationalCellBudget a b + 1) *
        (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1) →
      (3 * kE + 6) * (Cst + 1) ≤ (3 * kE + 6) * (timeCore Cm.P Cm.idx Cm.budget G density
          PtE PsE L + 1) * (rationalCellBudget a b + 1) *
        (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1) := by
    intro Cst hCst
    have e : (3 * kE + 6) * (timeCore Cm.P Cm.idx Cm.budget G density PtE PsE L + 1) *
        (rationalCellBudget a b + 1) *
        (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1) =
        (3 * kE + 6) * (timeCore Cm.P Cm.idx Cm.budget G density PtE PsE L *
          (rationalCellBudget a b + 1) *
          (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1) +
          (rationalCellBudget a b + 1) *
          (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1)) := by ring
    rw [e]
    apply Nat.mul_le_mul_left
    have : 1 ≤ (rationalCellBudget a b + 1) *
        (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1) :=
      one_le_mul_of (Nat.succ_pos _) (Nat.succ_pos _)
    omega
  cases n with
  | zero =>
      obtain ⟨u, hu, hout⟩ := zero_instance Cm (oracleAt E density G L) rows ha hab hc hd'
      have hcoins : List.ofFn coins = [] := by
        have : coinBits hD hd A c d 0 = 0 := rfl
        exact List.eq_nil_of_length_eq_zero (by simp [this])
      rw [hcoins]
      have hv : macroRun hD hd A spec a b c d 0 rows (coinWord hD hd A c d 0 coins) =
          ZeroLengthDispatch.zeroVector := (MM.zero rows _).1
      rw [hv]
      obtain ⟨run, hO, htime, hcells⟩ := complete_of_oruns spec hu hout
      refine ⟨run, hO, htime.trans (hscale _ ?_), hcells⟩
      have h1 : preBound Cm.P Cm.idx Cm.budget L + 1 + postBound Cm.P Cm.idx Cm.budget L ≤
          timeCore Cm.P Cm.idx Cm.budget G density PtE PsE L := by
        unfold timeCore
        have : preBound Cm.P Cm.idx Cm.budget L + postBound Cm.P Cm.idx Cm.budget L +
            (iterBound Cm.P Cm.idx Cm.budget L + PsE.eval (qcap G density L) + 1) ≤
            4097 * (L + 1) ^ 4 * (preBound Cm.P Cm.idx Cm.budget L +
              postBound Cm.P Cm.idx Cm.budget L +
              (iterBound Cm.P Cm.idx Cm.budget L + PsE.eval (qcap G density L) + 1)) :=
          Nat.le_mul_of_pos_left _ (by positivity)
        omega
      have h2 : 1 ≤ (rationalCellBudget a b + 1) *
          (T (variableConstant G density * (0 + rowIncidences rows + 1)) + 1) :=
        one_le_mul_of (Nat.succ_pos _) (Nat.succ_pos _)
      calc _ ≤ timeCore Cm.P Cm.idx Cm.budget G density PtE PsE L := h1
        _ ≤ timeCore Cm.P Cm.idx Cm.budget G density PtE PsE L *
            ((rationalCellBudget a b + 1) *
              (T (variableConstant G density * (0 + rowIncidences rows + 1)) + 1)) :=
          Nat.le_mul_of_pos_right _ h2
        _ = _ := by ring
  | succ k =>
      obtain ⟨final, totals, u, PR, hu, hout⟩ := positive_instance Cm spec hT rows coins ha hab hc hd'
      have hout' : u rOUT = outputWord (macroRun hD hd A spec a b c d (k+1) rows
          (coinWord hD hd A c d (k+1) coins)) := by
        rw [hout, PR.output]
        rfl
      obtain ⟨run, hO, htime, hcells⟩ := complete_of_oruns spec hu hout'
      refine ⟨run, hO, htime.trans (hscale _ ?_), hcells⟩
      have hdisp : totals.dispatches ≤ 4096 * (L + 1) ^ 4 * (rationalCellBudget a b + 1) :=
        PR.dispatches_poly.trans (dispatchPoly_le _ _)
      have hoT : totals.oracleTime ≤ 384 * (L + 1) ^ 4 * (rationalCellBudget a b + 1) *
          PtE.eval (qcap G density L) *
          T (variableConstant G density * ((k + 1) + rowIncidences rows + 1)) := by
        refine PR.oracleTime_poly.trans ?_
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_right
        exact callPoly_le _ _
      have := time_arith (pre := preBound Cm.P Cm.idx Cm.budget L)
        (post := postBound Cm.P Cm.idx Cm.budget L)
        (K := iterBound Cm.P Cm.idx Cm.budget L + PsE.eval (qcap G density L)) hdisp hoT hY
        (by omega)
      refine this.trans (le_of_eq ?_)
      unfold timeCore
      ring

end Instance

/-! ## The main theorem from the bundle -/

/-- **`MainTheorem` from the component bundle.** For any fixed hash certificate `A`, the
bundle for every SAT density gives the machine-level main theorem. -/
theorem main_of_components {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512*t) (64*t) t)
    (hC : ∀ density : ℕ, Components hD hd A density) : MainTheorem := by
  intro kE ΓE ΛE _ _ _ E density PtE PsE T spec hT
  let Cm := hC density
  set G := gateConstant hD hd A with hG
  obtain ⟨ct, et, hct⟩ := timeCore_poly Cm.P Cm.idx Cm.budget G density kE PtE PsE
  obtain ⟨cs, es, hcs⟩ := spaceCore_poly Cm.P Cm.idx Cm.budget G density kE PsE
  refine ⟨19 + kE + 1, Cell ΓE, _, inferInstance, inferInstance, inferInstance,
    theMachine E Cm.P Cm.idx, outTape kE, fun n _ _ _ c d => coinBits hD hd A c d n,
    ⟨145 * ct, et + 2⟩, ⟨cs, es⟩, ⟨12 * seedConstant hD hd A, 2⟩, variableConstant G density, ?_⟩
  intro n rows a b c d ha hab hc hd'
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have MM := macro_main hD hd A spec hT a b c d ha hb hc hd' hab
  refine ⟨?_, ?_, ?_⟩
  · -- coins
    refine (MM.randomBits_le n rows).trans ?_
    exact coins_arith _ _
  · -- every coin string: a run with the output, time, space and shape
    intro coins hlen
    have hlen' : coins.length = coinBits hD hd A c d n := hlen
    let f : Fin (coinBits hD hd A c d n) → Bool := fun i => coins[i.val]'(by omega)
    have hofn : List.ofFn f = coins :=
      List.ext_getElem (by simp [hlen']) (fun i _ _ => by simp [f])
    obtain ⟨run, hO, htime, hcells⟩ := machine_instance Cm spec hT n rows ha hab hc hd' f
      (machineInput rows a b c d coins) (by rw [hofn])
    refine ⟨run, _, hO, ?_, (hcells.trans (hcs _)), MM.shape n rows _⟩
    -- time
    have hB : rationalCellBudget a b + 1 ≤ 145 * (b / a + 1) ^ 2 := by
      have := MM.cellBudget_le
      have : 1 ≤ (b / a + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
      omega
    refine htime.trans ?_
    have h1 := hct (paperL rows a b c d)
    simp only at h1
    calc (3 * kE + 6) * (timeCore Cm.P Cm.idx Cm.budget G density PtE PsE
            (paperL rows a b c d) + 1) * (rationalCellBudget a b + 1) *
          (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1)
        ≤ ct * (paperL rows a b c d + 1) ^ et * (145 * (b / a + 1) ^ 2) *
          (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1) := by
          gcongr
      _ = 145 * (ct * (paperL rows a b c d + 1) ^ et * (b / a + 1) ^ 2) *
          (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1) := by ring
      _ ≤ 145 * (ct * (paperL rows a b c d + b / a + 1) ^ (et + 2)) *
          (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 145 (env_two_var ct et _ _))
      _ = PolynomialEnvelope.eval ⟨145 * ct, et + 2⟩ (paperL rows a b c d + b / a) *
          (T (variableConstant G density * (n + rowIncidences rows + 1)) + 1) := by
          unfold PolynomialEnvelope.eval
          ring
  · -- optimality and confidence
    intro lift
    refine ⟨MM.optimality n rows lift, (MM.confidence_coins n rows lift).trans ?_⟩
    exact_mod_cast Finset.card_le_card (fun w hw => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      intro run v hv
      obtain ⟨run₀, hO₀, -, -⟩ := machine_instance Cm spec hT n rows ha hab hc hd' w
        (machineInput rows a b c d (List.ofFn w)) rfl
      have hfin := (Completed.unique run run₀).1
      have hv₀ : Outputs (theMachine E Cm.P Cm.idx) run₀ (outTape kE) v := by
        unfold Outputs at hv ⊢
        rw [← hfin]
        exact hv
      rw [Outputs.unique hv₀ hO₀]
      exact hw)

/-- The same with the bundle given as a `Prop` (`Nonempty`). -/
theorem main_of_nonempty_components {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512*t) (64*t) t)
    (hC : ∀ density : ℕ, Nonempty (Components hD hd A density)) : MainTheorem :=
  main_of_components hD hd A (fun density => Classical.choice (hC density))

/-- Closed form: one certificate together with its bundles suffices. -/
theorem main_of_some_components
    (h : ∃ (t : ℕ) (hd : (16:ℕ)^384 = 256*t)
      (A : FiniteLocalSelectorCandidate.CertifiedParity (512*t) (64*t) t),
      ∀ density : ℕ, Nonempty (Components rfl hd A density)) : MainTheorem := by
  obtain ⟨t, hd, A, hC⟩ := h
  exact main_of_nonempty_components rfl hd A hC

end QecReliability.Assembly

end
