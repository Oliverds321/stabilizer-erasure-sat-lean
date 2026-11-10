import IidErasureTheorem
import ProductCode

/-! The uncorrectable-erasure probability `U(p)` from the fixed SAT machine, by reduction.

The `m`-fold direct sum of the input code (`ProductCode.rowsPower m rows`, on `n*m` qubits) is run
through the multiclass machine theorem `isotropic_tensor_machine_guarantee_strong` with ONE
latent class of `n` iid bits and the duplication circuit `dupProgram n m`, which sends latent bit
`i` to qubit `i` of every block. The latent fidelity of that instance is
`F_m(p) = Σ_E P_p(E) 2^{-m d_E}` (`fidelity_dup`), so `Û(p) = 1 - (output curve)(p)` is a
relative estimate of `I_m(p) = 1 - F_m(p)`, and `(1 - 2^{-m}) U ≤ I_m ≤ U`
(`ProductCode.uncorrectableProb_sandwich`) transfers it to `U(p)`. No new machine is built. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.UncorrectableMachine
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape RationalOutput Final QecPhysical QecPhysical.Stabilizer
open ExternalSATBridge TensorBernstein TensorLatent
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open QecReliability.LatentMachine.Runtime.FixedQuantum
open QecReliability.TensorMachine.Runtime.FixedQuantum
open QecReliability.IidErasure QecReliability.ProductCode
open QecPhysical.Stabilizer.Uncorrectable

/-- The duplication circuit: latent bit `i` erases qubit `i` of every block. No gates. -/
def dupProgram (n m : ℕ) : SharedCircuit.Program [n].sum (n * m) :=
  SharedCircuit.Program.pure (fun k => ((idx n m).symm k).1)

theorem dupProgram_map (n m : ℕ) (b : Causes n) :
    TensorEncoding.circuitMap (dupProgram n m) (b, PUnit.unit) = rep m b := by
  unfold TensorEncoding.circuitMap
  rw [flattenCauses_single]
  ext k
  simp [LatentEncoding.circuitMap, dupProgram, SharedCircuit.Program.pure_eval, Binary.causeBits]

theorem dupProgram_monotone (n m : ℕ) :
    Monotone (TensorEncoding.circuitMap (dupProgram n m)) := by
  intro x y hxy
  rcases x with ⟨bx, ux⟩
  rcases y with ⟨b_y, uy⟩
  cases ux
  cases uy
  rw [dupProgram_map, dupProgram_map]
  exact rep_mono hxy.1

theorem coefficients_dup {n m : ℕ} (S : Submodule Bit (Pauli (n * m))) (j : Fin (n + 1)) :
    multivariateCoefficients S (TensorEncoding.circuitMap (dupProgram n m)) (j, PUnit.unit) =
      layerAverage (id : Causes n → Finset (Fin n)) (fun E => erasureScore S (rep m E)) j := by
  show layerAverage (id : Causes n → Causes n)
    (fun b => erasureScore S (TensorEncoding.circuitMap (dupProgram n m) (b, PUnit.unit))) j = _
  simp only [dupProgram_map]

/-- **(2) at the channel level.** For every lift of the `m`-fold code, the optimal fidelity of the
latent channel (one iid class of `n` bits, duplication circuit) is `F_m(p)`. -/
theorem fidelity_dup {n m : ℕ} {rows : List (List (PauliCoord n))}
    (lift : Lift (rowSpace (rowsPower m rows))) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.multivariateLatentErasure (TensorEncoding.circuitMap (dupProgram n m))
          (p, PUnit.unit) ⟨hp, trivial⟩)).map =
      powerFidelity m (rowSpace rows) p := by
  rw [(lift.multivariateLatentErasure_optimum (TensorEncoding.circuitMap (dupProgram n m))
      (p, PUnit.unit) ⟨hp, trivial⟩).1]
  show bernsteinCurve n (fun j => multivariateCoefficients (rowSpace (rowsPower m rows))
    (TensorEncoding.circuitMap (dupProgram n m)) (j, PUnit.unit)) p = _
  simp only [coefficients_dup]
  rw [← latentCurve_eq_bernstein, powerFidelity_eq_sum_rep, ← rowSpace_rowsPower]
  rfl

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => explicitCertificate

/-- **Uncorrectable-erasure probability from the fixed machine.** The same fixed machine `M` of
`isotropic_tensor_machine_guarantee_strong` reads the rows of the `m`-fold code
`rowsPower m rows` (on `n*m` qubits), the duplication circuit `dupProgram n m`, `ε' = a/b` and
`δ = c/d`. On every coin string it halts within the stated time and space with an output vector
`v`; `Û(p) = 1 - Σ_j f̂_j C(n,j) p^j (1-p)^(n-j)` is nondecreasing and in `[0,1]` on `[0,1]`, and
its Bernstein coefficients `1 - f̂_j` vanish exactly where the layer fractions of `U` vanish. With
probability at least `1 - c/d`, for all `p ∈ [0,1]` simultaneously,
`(1-ε')(1-2^{-m}) U(p) ≤ Û(p) ≤ (1+ε') U(p)`, and if moreover `2^{-m} ≤ ε'` then
`|Û(p) - U(p)| ≤ 2ε' U(p)`. Here `U = uncorrectableProb (rowSpace rows)`. -/
theorem uncorrectable_machine_guarantee :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n : ℕ}
    (rows : List (List (PauliCoord n))) (m a b c d : ℕ), 1 ≤ m → 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let R := rowsPower m rows
    let C := dupProgram n m
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace R) (rowsPower_isotropic hS)
    let U := uncorrectableProb (rowSpace rows)
    let L := Boundary.resourceSize R C a b c d
    let B := rationalCellBudget a b
    let r := rationalRepetitionBudget (2*slots [n]) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT (n*m) [n])
      (Factory.width HD HS CERT (n*m) [n]) r
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    let Uhat := fun (v : Vector (slots [n]-1)) (p : ℝ) => 1 - bernsteinCurve n (coefficients v) p
    -- (i) the target of the instance is the latent fidelity `F_m` of the `m`-fold code
    (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      entanglementFidelity (lift.erasureFlagDecoder.comp
          (lift.multivariateLatentErasure (TensorEncoding.circuitMap C)
            (p, PUnit.unit) ⟨hp, trivial⟩)).map = powerFidelity m (rowSpace rows) p) ∧
    -- (ii) every coin string
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input [n] R C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed*
            (Boundary.satStructuralSize R C+1))+1) ∧
        run.cells ≤ Pspace.eval L ∧
        MonotoneOn (Uhat v) (Set.Icc 0 1) ∧
        (∀ p ∈ Set.Icc (0:ℝ) 1, 0 ≤ Uhat v p ∧ Uhat v p ≤ 1) ∧
        (∀ j, 1 - coefficients v j = 0 ↔ layerFraction (rowSpace rows) j = 0)) ∧
    -- (iii) one coin event: the two-sided bound for every `p ∈ [0,1]` simultaneously
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input [n] R C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)), Outputs M run outputTape v →
          ∀ p ∈ Set.Icc (0:ℝ) 1,
            ((1 - (a:ℝ)/b) * (1 - ((2:ℝ)^m)⁻¹) * U p ≤ Uhat v p ∧
              Uhat v p ≤ (1 + (a:ℝ)/b) * U p) ∧
            (((2:ℝ)^m)⁻¹ ≤ (a:ℝ)/b → |Uhat v p - U p| ≤ 2 * ((a:ℝ)/b) * U p)) := by
  obtain ⟨engine,rateConstant,Ptime,Pspace,hrate,hclosed⟩ :=
    isotropic_tensor_machine_guarantee_strong
  refine ⟨engine,rateConstant,Ptime,Pspace,hrate,?_⟩
  intro n rows m a b c d hm ha hab hc hd hS
  have hS' := rowsPower_isotropic (m := m) hS
  obtain ⟨_,hruns,hprob⟩ := hclosed (n:=n*m) (ds:=[n]) (rowsPower m rows) (dupProgram n m)
    a b c d ha hab hc hd hS' (dupProgram_monotone n m)
  have hε0 : (0:ℝ) ≤ (a:ℝ)/b := by positivity
  have hε1 : (a:ℝ)/b ≤ 1 := by
    have hb : (0:ℝ) < b := by exact_mod_cast (lt_of_lt_of_le ha hab)
    rw [div_le_one hb]
    exact_mod_cast hab
  refine ⟨?_,?_,?_⟩
  · intro p hp
    exact fidelity_dup _ p hp
  · intro coins
    obtain ⟨run,v,hout,htime,hspace,_,hanti,hrange,_,hone⟩ := hruns coins
    have hanti' : Antitone (coefficients v) := by
      intro i j hij
      have h := hanti (show ((i, PUnit.unit) : Grid [n]) ≤ (j, PUnit.unit) from ⟨hij, le_rfl⟩)
      rw [vectorTable_single, vectorTable_single] at h
      exact h
    have hrange' : ∀ j, 0 ≤ coefficients v j ∧ coefficients v j ≤ 1 := by
      intro j
      have h := hrange (j, PUnit.unit)
      rw [vectorTable_single] at h
      exact h
    refine ⟨run,v,hout,htime,hspace,?_,?_,?_⟩
    · intro p hp q hq hpq
      have h := bernsteinCurve_antitone _ hanti' hp hq hpq
      simp only
      linarith
    · intro p hp
      have h := bernsteinCurve_range hp.1 hp.2 hrange'
      constructor <;> linarith [h.1, h.2]
    · intro j
      have h := hone (j, PUnit.unit)
      rw [vectorTable_single, coefficients_dup, rowSpace_rowsPower] at h
      rw [sub_eq_zero, eq_comm, h]
      exact layerAverage_rep_eq_one_iff (rowSpace rows) hm j
  · apply hprob.trans
    apply FiniteProbability.prob_mono
    intro coins hgood run v hv p hp
    have h := hgood run v hv (p, PUnit.unit) ⟨hp, trivial⟩
    rw [vectorCurve_single, fidelity_dup _ p hp] at h
    have hu : |(1 - bernsteinCurve n (coefficients v) p) - powerInfidelity m (rowSpace rows) p| ≤
        (a:ℝ)/b * powerInfidelity m (rowSpace rows) p := by
      rw [powerInfidelity_eq]
      have h2 := h.2
      rw [show (1 - bernsteinCurve n (coefficients v) p) - (1 - powerFidelity m (rowSpace rows) p)
          = -(bernsteinCurve n (coefficients v) p - powerFidelity m (rowSpace rows) p) by ring,
        abs_neg]
      exact h2
    refine ⟨uncorrectable_of_relative (rowSpace rows) m hp.1 hp.2 hε0 hε1 hu, fun hm2 => ?_⟩
    have h3 := uncorrectable_relative_of_half (rowSpace rows) m (ε := 2 * ((a:ℝ)/b))
      hp.1 hp.2 (by positivity) (by linarith) (by linarith)
      (by rw [show 2 * ((a:ℝ)/b) / 2 = (a:ℝ)/b by ring]; exact hu)
    exact h3

end QecReliability.UncorrectableMachine

#print axioms QecReliability.UncorrectableMachine.dupProgram_monotone
#print axioms QecReliability.UncorrectableMachine.fidelity_dup
#print axioms QecReliability.UncorrectableMachine.uncorrectable_machine_guarantee
