import TensorFixedQuantumStrong
import PhysicalBridge.ZeroLengthDispatchCandidate
import PhysicalBridge.PhysicalBernstein

/-! Independent flagged erasure of every qubit with one probability `p`, stated
without tensor vocabulary. This is the single-class (`ds = [n]`, identity latent
circuit) specialization of `isotropic_tensor_machine_guarantee_strong`. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.IidErasure
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape RationalOutput Final QecPhysical QecPhysical.Stabilizer
open ExternalSATBridge TensorBernstein TensorLatent
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open QecReliability.LatentMachine.Runtime.FixedQuantum
open QecReliability.TensorMachine.Runtime.FixedQuantum

/-- The identity latent circuit: latent cause `i` erases qubit `i`. -/
def iidProgram (n : ℕ) : SharedCircuit.Program [n].sum n := ZeroLengthDispatch.iidProgram n

theorem flattenCauses_single (n : ℕ) (b : Causes n) :
    flattenCauses [n] (b, PUnit.unit) = b := by
  ext i
  simp [flattenCauses, causesBits, Binary.causeBits, Binary.appendBits, Fin.append_right_nil]
  exact decide_eq_true_iff

theorem iidProgram_map (n : ℕ) (b : Causes n) :
    TensorEncoding.circuitMap (iidProgram n) (b, PUnit.unit) = b := by
  unfold TensorEncoding.circuitMap iidProgram
  rw [flattenCauses_single]
  exact congrFun (ZeroLengthDispatch.iidProgram_map n) b

theorem iidProgram_monotone (n : ℕ) : Monotone (TensorEncoding.circuitMap (iidProgram n)) := by
  intro x y hxy
  rcases x with ⟨bx, ux⟩
  rcases y with ⟨b_y, uy⟩
  cases ux
  cases uy
  rw [iidProgram_map, iidProgram_map]
  exact hxy.1

/-- Output slot of coefficient `j`: the `j`-th entry of the flat output vector. -/
def slot (n : ℕ) (j : Fin (n+1)) : Fin (slots [n] - 1 + 1) :=
  ⟨j.val, by have := j.isLt; simp only [slots, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]; omega⟩

theorem flatMap_singleton_map {α β : Type} (f : α → β) (l : List α) :
    l.flatMap (fun i => [f i]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem enum_single (n : ℕ) :
    RationalTensorRepair.enum [n] = (List.finRange (n+1)).map (fun i => (i, PUnit.unit)) := by
  simp only [RationalTensorRepair.enum, List.map_cons, List.map_nil]
  exact flatMap_singleton_map _ _

theorem index_single (n : ℕ) (k : Fin (slots [n] - 1 + 1)) :
    (Boundary.index [n] k).1.val = k.val := by
  simp [Boundary.index, ordinalIndex, enum_single]

/-- The flat output order is the coefficient order. -/
theorem position_single (n : ℕ) (j : Fin (n+1)) : position [n] (j, PUnit.unit) = slot n j := by
  apply Fin.ext
  have h := position_index [n] (j, PUnit.unit)
  have h1 := congrArg (fun x : Grid [n] => (x.1 : Fin (n+1)).val) h
  simp only at h1
  rw [index_single] at h1
  exact h1

/-- The coefficient `f̂ j` written by the machine: entry `j` of the output vector. -/
def coefficients {n : ℕ} (v : RationalOutput.Vector (slots [n] - 1)) : Fin (n+1) → ℝ :=
  fun j => (v.get (slot n j)).value

theorem vectorTable_single {n : ℕ} (v : RationalOutput.Vector (slots [n] - 1)) (j : Fin (n+1)) :
    vectorTable [n] v (j, PUnit.unit) = coefficients v j := by
  simp only [vectorTable, coefficients, position_single]

theorem vectorCurve_single {n : ℕ} (v : RationalOutput.Vector (slots [n] - 1)) (p : ℝ) :
    vectorCurve [n] v (p, PUnit.unit) = bernsteinCurve n (coefficients v) p := by
  show bernsteinCurve n (fun j => vectorTable [n] v (j, PUnit.unit)) p = _
  simp only [vectorTable_single]

theorem coefficients_single {n : ℕ} (S : Submodule Bit (Pauli n)) (j : Fin (n+1)) :
    multivariateCoefficients S (TensorEncoding.circuitMap (iidProgram n)) (j, PUnit.unit) =
      layerAverage (id : Causes n → Finset (Fin n)) (erasureScore S) j := by
  show layerAverage (id : Causes n → Causes n)
    (fun b => erasureScore S (TensorEncoding.circuitMap (iidProgram n) (b, PUnit.unit))) j = _
  simp only [iidProgram_map]

/-- The single-class tensor channel at `(p, ())` has the iid erasure fidelity. -/
theorem fidelity_single {n : ℕ} {S : Submodule Bit (Pauli n)} (lift : Lift S) (p : ℝ)
    (hp : p ∈ Set.Icc (0:ℝ) 1) :
    entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.multivariateLatentErasure (TensorEncoding.circuitMap (iidProgram n))
          (p, PUnit.unit) ⟨hp, trivial⟩)).map =
      entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map := by
  rw [(lift.multivariateLatentErasure_optimum (TensorEncoding.circuitMap (iidProgram n))
      (p, PUnit.unit) ⟨hp, trivial⟩).1,
    (lift.iidLatentErasure_optimum id p hp.1 hp.2).1]
  show bernsteinCurve n (fun j => multivariateCoefficients S
    (TensorEncoding.circuitMap (iidProgram n)) (j, PUnit.unit)) p = _
  simp only [coefficients_single]

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => explicitCertificate

/-- **Theorem 1 + Corollary 3 (iid flagged erasure).** One fixed machine `M`
(chosen, with its SAT engine and polynomial envelopes, before any input) reads the
check rows of an isotropic `n`-qubit stabilizer code, `ε = a/b ∈ (0,1]`,
`δ = c/d`, and `N` coin bits. Every qubit is erased independently with probability
`p` and the erased set is flagged; `F p` is the entanglement fidelity of the fixed
flag decoder, which is optimal over all recoveries and equals the Bernstein curve
of the layer-averaged erasure scores `f`. On every coin string `M` halts within the
stated time and space with an output vector whose entries `f̂ j = coefficients v j`
are antitone, lie in `[0,1]`, satisfy `f̂ 0 = 1` and `f̂ n = F 1 = 4^{-(n-k)}`, and
equal one exactly where `f` does. With probability at least `1 - c/d` over the
coins, `R p = ∑ j f̂ j C(n,j) p^j (1-p)^(n-j)` satisfies both relative tails
`RelPair ε (F p) (R p)` simultaneously for every `p ∈ [0,1]`. -/
theorem iid_erasure_machine_guarantee :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n : ℕ}
    (rows : List (List (PauliCoord n))) (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let C := iidProgram n
    -- physical target: each qubit erased independently with probability `p`, flagged
    let F := fun (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) =>
      entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map
    -- true Bernstein coefficients: erasure scores averaged over each Hamming layer
    let f := layerAverage (id : Causes n → Finset (Fin n)) (erasureScore (rowSpace rows))
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots [n]) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n [n])
      (Factory.width HD HS CERT n [n]) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    -- (i) `F` is optimal over all recoveries and is the Bernstein curve of `f`
    (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      F p hp = bernsteinCurve n f p ∧
      ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
        entanglementFidelity (Q.comp
          (lift.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map ≤ F p hp) ∧
    -- (ii) every coin string
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input [n] rows C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed*
            (Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L ∧
        Antitone (coefficients v) ∧
        (∀ j, 0 ≤ coefficients v j ∧ coefficients v j ≤ 1) ∧
        coefficients v 0 = 1 ∧
        coefficients v (Fin.last n) = F 1 ⟨zero_le_one, le_rfl⟩ ∧
        coefficients v (Fin.last n) = erasureScore (rowSpace rows) Finset.univ ∧
        coefficients v (Fin.last n) = ((4:ℝ) ^ (n - Module.finrank Bit (rowSpace rows)))⁻¹ ∧
        (∀ j, coefficients v j = 1 ↔ f j = 1)) ∧
    -- (iii) one coin event: both relative tails for every `p ∈ [0,1]` simultaneously
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input [n] rows C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)), Outputs M run outputTape v →
          ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
            RelPair ((a:ℝ)/b) (F p hp) (bernsteinCurve n (coefficients v) p)) := by
  obtain ⟨engine,rateConstant,Ptime,Pspace,hrate,hclosed⟩ :=
    isotropic_tensor_machine_guarantee_strong
  refine ⟨engine,rateConstant,Ptime,Pspace,hrate,?_⟩
  intro n rows a b c d ha hab hc hd hS
  obtain ⟨_,hruns,hprob⟩ := hclosed (n:=n) (ds:=[n]) rows (iidProgram n) a b c d ha hab hc hd hS
    (iidProgram_monotone n)
  have hopt := fun p (hp : p ∈ Set.Icc (0:ℝ) 1) =>
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).iidLatentErasure_optimum
      (id : Causes n → Finset (Fin n)) p hp.1 hp.2
  have hend := (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).iidLatentErasure_endpoints
    (id : Causes n → Finset (Fin n))
  refine ⟨?_,?_,?_⟩
  · intro p hp
    exact ⟨(hopt p hp).1, fun Q => ((hopt p hp).2 Q).trans (hopt p hp).1.symm.le⟩
  · intro coins
    obtain ⟨run,v,hout,htime,hspace,_,hanti,hrange,hcorner,hone⟩ := hruns coins
    have hlast : coefficients v (Fin.last n) = erasureScore (rowSpace rows) Finset.univ := by
      have h := (hcorner (true, PUnit.unit)).2
      change vectorTable [n] v (Fin.last n, PUnit.unit) =
        erasureScore (rowSpace rows)
          (TensorEncoding.circuitMap (iidProgram n) (Finset.univ, PUnit.unit)) at h
      rw [vectorTable_single, iidProgram_map] at h
      exact h
    refine ⟨run,v,hout,htime,hspace,?_,?_,?_,?_,hlast,?_,?_⟩
    · intro i j hij
      have h := hanti (show ((i, PUnit.unit) : Grid [n]) ≤ (j, PUnit.unit) from ⟨hij, le_rfl⟩)
      rw [vectorTable_single, vectorTable_single] at h
      exact h
    · intro j
      have h := hrange (j, PUnit.unit)
      rw [vectorTable_single] at h
      exact h
    · have h := (hcorner (false, PUnit.unit)).2
      change vectorTable [n] v (⟨0, Nat.zero_lt_succ n⟩, PUnit.unit) =
        erasureScore (rowSpace rows)
          (TensorEncoding.circuitMap (iidProgram n) (∅, PUnit.unit)) at h
      rw [vectorTable_single, iidProgram_map] at h
      have e : (0 : Fin (n+1)) = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext (by simp)
      rw [e, h]
      exact score_empty _
    · rw [hlast]
      exact hend.2.symm
    · rw [hlast]
      exact score_full (rowSpace rows) hS
    · intro j
      have h := hone (j, PUnit.unit)
      rw [vectorTable_single, coefficients_single] at h
      exact h
  · apply hprob.trans
    apply FiniteProbability.prob_mono
    intro coins hgood run v hv p hp
    have h := hgood run v hv (p, PUnit.unit) ⟨hp, trivial⟩
    rw [vectorCurve_single, fidelity_single _ p hp] at h
    exact h

end QecReliability.IidErasure
