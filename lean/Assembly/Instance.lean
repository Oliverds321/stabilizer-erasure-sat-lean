import Assembly.Loop
import Assembly.Poly

/-!
# Assembly.Instance: the register-level run of one instance

From the component bundle and the macro theorem (`macro_main`):

* `positive_instance` (`n = k+1`): the main program body runs from the input register file
  to a file whose output register holds `ratioWord final.output`, where `final` is the
  terminal state of the `PositiveRun`, inside `Fits (regBound L)` and with cost
  `≤ pre + (dispatches + 1)·(iterBound L + PsE(qcap L) + 1) + oracleTime + post`;
* `zero_instance` (`n = 0`): the same with no loop iteration.

All register bounds and per-iteration costs depend on `L = paperL` only.
-/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

noncomputable section
namespace QecReliability.Assembly
open RegMachine Interp FL Function
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate
open SharedCircuit SharedCircuit.LatentEncoding RationalOutput QecPhysical QecPhysical.Stabilizer
open Final SharedCircuit.FixedLocalEmitter.AllLength FiniteLocalSelectorCandidate

/-! ## Bounds as functions of `L` -/

section Bounds
variable (P : Program) (I : Indices) (Bd : Budget)

/-- Register-length bound at input length `L`. -/
def regBound (L : ℕ) : ℕ :=
  stBound P I (Bd.value.eval L) (Bd.depth.eval L) + (Program.enc P).size + 2 * Bd.value.eval L + 6

/-- Cost of one loop iteration without the SAT call's own time and cells. -/
def iterBound (L : ℕ) : ℕ :=
  bodyCost P I (regBound P I Bd L) (Bd.value.eval L) (Bd.cost.eval L) (Bd.depth.eval L)

def preBound (L : ℕ) : ℕ :=
  preCost P I (regBound P I Bd L) (Bd.value.eval L) (Bd.cost.eval L) (Bd.depth.eval L)

def postBound (L : ℕ) : ℕ :=
  postCost P I (regBound P I Bd L) (Bd.value.eval L) (Bd.cost.eval L) (Bd.depth.eval L)

theorem regBound_hS (L : ℕ) :
    stBound P I (Bd.value.eval L) (Bd.depth.eval L) + (Program.enc P).size + 2 ≤
      regBound P I Bd L := by
  unfold regBound; omega

theorem regBound_hm (L : ℕ) : 2 * Bd.value.eval L + 4 ≤ regBound P I Bd L := by
  unfold regBound; omega

theorem regBound_poly : PolyBounded (regBound P I Bd) := by
  unfold regBound stBound stateBound frameBound
  poly_bounded

theorem flCost_poly : PolyBounded (fun L => flCost P I (regBound P I Bd L) (Bd.value.eval L)
    (Bd.cost.eval L) (Bd.depth.eval L)) := by
  have h := regBound_poly P I Bd
  unfold flCost stBound stateBound frameBound
  poly_bounded

theorem iterBound_poly : PolyBounded (iterBound P I Bd) := by
  have h := regBound_poly P I Bd
  have hf := flCost_poly P I Bd
  unfold iterBound bodyCost
  poly_bounded

theorem preBound_poly : PolyBounded (preBound P I Bd) := by
  have h := regBound_poly P I Bd
  have hf := flCost_poly P I Bd
  unfold preBound preCost
  poly_bounded

theorem postBound_poly : PolyBounded (postBound P I Bd) := by
  have h := regBound_poly P I Bd
  have hf := flCost_poly P I Bd
  unfold postBound postCost
  poly_bounded

end Bounds

/-- Query-length cap at input length `L` (`queryPolynomial` of the macro layer). -/
abbrev qcap (G density L : ℕ) : ℕ := InputEncoding.queryPolynomial G density L

theorem qcap_poly (G density : ℕ) : PolyBounded (qcap G density) := by
  unfold qcap InputEncoding.queryPolynomial
  poly_bounded

theorem canonical_of_padded {density : ℕ} {bits : List Bool} (h : IsPaddedQuery density bits) :
    CanonicalDensityInput density bits := by
  obtain ⟨req, rfl⟩ := h
  exact ⟨padRequest density req, padRequest_density density req, rfl⟩

/-! ## Instances -/

section Instances
variable {D t : ℕ} {hD : D = 16^384} {hd : D = 256*t}
    {A : FiniteLocalSelectorCandidate.CertifiedParity (512*t) (64*t) t}
variable {density : ℕ} (Cm : Components hD hd A density)
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}

/-- The SAT oracle used at input length `L`. -/
abbrev oracleAt (E : Machine kE ΓE ΛE) (density G L : ℕ) : OracleSpec :=
  satOracle E density (qcap G density L)

/-- **Positive instances.** -/
theorem positive_instance (spec : EncodedSAT E density PtE PsE T) (hT : Monotone T)
    {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd' : 0 < d) :
    ∃ (final : Config) (totals : Totals) (u : Regs 20),
      PositiveRun hD hd A spec a b c d k rows (coinWord hD hd A c d (k+1) coins) final totals ∧
      ORuns (oracleAt E density (gateConstant hD hd A) (paperL rows a b c d))
        (regBound Cm.P Cm.idx Cm.budget (paperL rows a b c d)) (mainProg Cm.P Cm.idx).body
        (inputRegs (R := 19) (machineInput rows a b c d (List.ofFn coins))) u
        (preBound Cm.P Cm.idx Cm.budget (paperL rows a b c d) +
          (totals.dispatches + 1) * (iterBound Cm.P Cm.idx Cm.budget (paperL rows a b c d) +
            PsE.eval (qcap (gateConstant hD hd A) density (paperL rows a b c d)) + 1) +
          totals.oracleTime + postBound Cm.P Cm.idx Cm.budget (paperL rows a b c d)) ∧
      u rOUT = ratioWord final.output := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨final, totals, PR⟩ := (macro_main hD hd A spec hT a b c d ha hb hc hd' hab).positive
    k rows (coinWord hD hd A c d (k+1) coins)
  obtain ⟨enc, F⟩ := Cm.positive E PtE PsE T spec hT a b c d k rows coins ha hab hc hd'
  have hS := regBound_hS Cm.P Cm.idx Cm.budget (paperL rows a b c d)
  have hm := regBound_hm Cm.P Cm.idx Cm.budget (paperL rows a b c d)
  -- preamble
  have hpre := preamble_run (O := oracleAt E density (gateConstant hD hd A) (paperL rows a b c d))
    hS hm F.init (F.isDone _ reachable_initial)
  -- loop body for every reachable state
  have hbody : ∀ s e, InstReachable hD hd A spec a b c d k rows coins s →
      instStep hD hd A spec a b c d k rows coins s = some e →
      ORuns (oracleAt E density (gateConstant hD hd A) (paperL rows a b c d))
        (regBound Cm.P Cm.idx Cm.budget (paperL rows a b c d)) (body Cm.P Cm.idx)
        (headRegs (enc s) false) (headRegs (enc e.next) (decide (e.next.pc = .done)))
        ((iterBound Cm.P Cm.idx Cm.budget (paperL rows a b c d) +
          PsE.eval (qcap (gateConstant hD hd A) density (paperL rows a b c d))) + e.oracleTime) := by
    intro s e hs he
    have hne := pc_ne_done_of_step he
    have hdone' := F.isDone e.next (reachable_next hs he)
    by_cases hpc : s.pc = .invoke
    · have hinv := F.isInvoke s hs hne
      rw [show decide (s.pc = .invoke) = true by simp [hpc]] at hinv
      have hq := F.query s hs hpc
      obtain ⟨hpad, run, hcells, hval, htime, -⟩ := PR.invoke s hs hpc
      have hok : (oracleAt E density (gateConstant hD hd A) (paperL rows a b c d)).qok s.query :=
        ⟨canonical_of_padded hpad, PR.query s hs⟩
      obtain ⟨ho, hcost⟩ := satOracle_run E density
        (qcap (gateConstant hD hd A) density (paperL rows a b c d)) run
      have hval' : ((instExt hD hd A spec c d k rows coins).sat s.query).value =
          (oracleAt E density (gateConstant hD hd A) (paperL rows a b c d)).oracle s.query :=
        hval.trans ho.symm
      have hres := F.resume s e hs hpc he
      rw [hval'] at hres
      refine (body_invoke_run hS hm hinv hq hok hres hdone').mono ?_
      have ht : e.oracleTime = run.time := (invoke_edge_time hpc he).trans htime
      have hcells' : run.cells ≤ PsE.eval (qcap (gateConstant hD hd A) density
        (paperL rows a b c d)) := hcells
      rw [hcost, ht]
      unfold iterBound
      omega
    · have hinv := F.isInvoke s hs hne
      rw [show decide (s.pc = .invoke) = false by simp [hpc]] at hinv
      refine (body_step_run hS hm hinv (F.step s e hs hpc he) hdone').mono ?_
      unfold iterBound
      omega
  -- the loop along the macro trace
  obtain ⟨events, htr⟩ := PR.trace
  have hloop := loop_trace (P := Cm.P) (I := Cm.idx) enc
    (InstReachable hD hd A spec a b c d k rows coins)
    (fun s e hs he => reachable_next hs he)
    (fun s hs => fits_start hm (F.isDone s hs).1) hbody htr reachable_initial PR.done
  -- postamble
  have hpost := postamble_run (O := oracleAt E density (gateConstant hD hd A) (paperL rows a b c d))
    hS (F.output final ⟨_, _, htr⟩ PR.done) hloop.fits_end
  refine ⟨final, totals, _, PR, (hpre.seq (hloop.seq hpost)).mono
    (by unfold preBound postBound; omega), rfl⟩

/-- **The zero-length instance.** -/
theorem zero_instance (O : OracleSpec) {a b c d : ℕ} (rows : List (List (PauliCoord 0)))
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd' : 0 < d) :
    ∃ u : Regs 20,
      ORuns O (regBound Cm.P Cm.idx Cm.budget (paperL rows a b c d)) (mainProg Cm.P Cm.idx).body
        (inputRegs (R := 19) (machineInput rows a b c d [])) u
        (preBound Cm.P Cm.idx Cm.budget (paperL rows a b c d) + 1 +
          postBound Cm.P Cm.idx Cm.budget (paperL rows a b c d)) ∧
      u rOUT = outputWord ZeroLengthDispatch.zeroVector := by
  obtain ⟨v, hinit, hdone, hout⟩ := Cm.zero rows a b c d ha hab hc hd'
  have hS := regBound_hS Cm.P Cm.idx Cm.budget (paperL rows a b c d)
  have hm := regBound_hm Cm.P Cm.idx Cm.budget (paperL rows a b c d)
  have hpre := preamble_run (O := O) hS hm hinit hdone
  have hf := hpre.fits_end
  have hloop : ORuns O (regBound Cm.P Cm.idx Cm.budget (paperL rows a b c d)) (mainLoop Cm.P Cm.idx)
      (headRegs v true) (headRegs v true) 1 := by
    refine ⟨1, _, Stmt.BigStep.loopF (σ := σO O) hf trivial
      (headIs_eval rDN _ true (by simp)) (by decide) hf, ?_⟩
    simp [σO, oracleSem, OInstr.cost, Instr.cost]
  have hpost := postamble_run (O := O) hS hout hloop.fits_end
  exact ⟨_, (hpre.seq (hloop.seq hpost)).mono (by unfold preBound postBound; omega), rfl⟩

end Instances

end QecReliability.Assembly

end
