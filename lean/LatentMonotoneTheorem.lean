import IidErasureTheorem

/-! One-class latent theorem for an arbitrary MONOTONE latent circuit
`C : {0,1}^r → {0,1}^n`, stated without tensor vocabulary: the single-class
(`ds = [r]`) specialization of `isotropic_tensor_machine_guarantee_strong`, for any
monotone `C : SharedCircuit.Program [r].sum n` (the identity circuit of
`IidErasureTheorem` is one instance). Also: for monotone `C` the coefficients equal
to one (zero infidelity) form a prefix `j < d_C`, for the truth and for the output. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.LatentMonotone
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape RationalOutput Final QecPhysical QecPhysical.Stabilizer
open ExternalSATBridge TensorBernstein TensorLatent
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open QecReliability.LatentMachine.Runtime.FixedQuantum
open QecReliability.TensorMachine.Runtime.FixedQuantum
open QecReliability.IidErasure (coefficients vectorTable_single vectorCurve_single)

/-- The erasure pattern of a latent bit vector under a one-class circuit. -/
def latentMap {r n : ℕ} (C : SharedCircuit.Program [r].sum n) (b : Causes r) : Finset (Fin n) :=
  TensorEncoding.circuitMap C (b, PUnit.unit)

theorem tensor_monotone {r n : ℕ} (C : SharedCircuit.Program [r].sum n)
    (hC : Monotone (latentMap C)) : Monotone (TensorEncoding.circuitMap C) := by
  intro x y hxy
  rcases x with ⟨bx, ux⟩
  rcases y with ⟨b_y, uy⟩
  cases ux
  cases uy
  exact hC hxy.1

theorem coefficients_eq {r n : ℕ} (S : Submodule Bit (Pauli n))
    (C : SharedCircuit.Program [r].sum n) (j : Fin (r+1)) :
    multivariateCoefficients S (TensorEncoding.circuitMap C) (j, PUnit.unit) =
      layerAverage (latentMap C) (erasureScore S) j := rfl

/-- The single-class tensor channel at `(p, ())` is the latent iid channel through `C`. -/
theorem fidelity_eq {r n : ℕ} {S : Submodule Bit (Pauli n)} (lift : Lift S)
    (C : SharedCircuit.Program [r].sum n) (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.multivariateLatentErasure (TensorEncoding.circuitMap C)
          (p, PUnit.unit) ⟨hp, trivial⟩)).map =
      entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.iidLatentErasure (latentMap C) p hp.1 hp.2)).map := by
  rw [(lift.multivariateLatentErasure_optimum (TensorEncoding.circuitMap C)
      (p, PUnit.unit) ⟨hp, trivial⟩).1,
    (lift.iidLatentErasure_optimum (latentMap C) p hp.1 hp.2).1]
  rfl

/-- For an antitone sequence bounded by one, the indices where it equals one form a
prefix `{j | j < d}` with `d ≤ r+1`. -/
theorem eq_one_prefix {r : ℕ} (f : Fin (r+1) → ℝ) (hf : Antitone f) (h1 : ∀ j, f j ≤ 1) :
    ∃ dC : ℕ, dC ≤ r+1 ∧ ∀ j : Fin (r+1), f j = 1 ↔ j.val < dC := by
  classical
  let s := Finset.univ.filter (fun j : Fin (r+1) => f j = 1)
  by_cases hs : s.Nonempty
  · refine ⟨(s.max' hs).val + 1, by have := (s.max' hs).isLt; omega, fun j => ?_⟩
    constructor
    · intro hj
      have : j ≤ s.max' hs := s.le_max' j (by simp [s, hj])
      have : j.val ≤ (s.max' hs).val := this
      omega
    · intro hj
      have hle : j ≤ s.max' hs := by
        show j.val ≤ (s.max' hs).val
        omega
      have hm : f (s.max' hs) = 1 := by
        have := s.max'_mem hs
        simpa [s] using this
      exact le_antisymm (h1 j) (hm ▸ hf hle)
  · refine ⟨0, Nat.zero_le _, fun j => ?_⟩
    simp only [Nat.not_lt_zero, iff_false]
    intro hj
    exact hs ⟨j, by simp [s, hj]⟩

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => explicitCertificate

/-- **Latent theorem, monotone circuits.** One fixed machine `M` (chosen with its
SAT engine and polynomial envelopes before any input) reads the check rows of an
isotropic stabilizer code, a monotone one-class latent circuit `C` on `r` latent
bits, `ε = a/b ∈ (0,1]`, `δ = c/d` and `N` coin bits. `F p` is the entanglement
fidelity of the fixed flag decoder for the channel that draws `r` latent bits iid
Bernoulli(`p`) and erases (flagged) the set `C(b)`; it is optimal over all
recoveries and equals the Bernstein curve of `f j` (scores averaged over the
`j`-th Hamming layer of latent vectors). The coefficients equal to one form a
prefix `j < d_C`. On every coin string `M` halts within the stated time and space
with an `(r+1)`-vector `f̂ = coefficients v` that is antitone, in `[0,1]`, has exact
endpoints `f̂ 0 = f 0 = F 0` and `f̂ r = f r = F 1`, and has `f̂ j = 1 ↔ f j = 1`
(hence also `f̂ j = 1 ↔ j < d_C`). With probability at least `1-c/d` the curve
`Σ_j f̂ j C(r,j) p^j (1-p)^(r-j)` is `ε`-accurate in both tails for every `p`. -/
theorem latent_monotone_machine_guarantee :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program [r].sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    Monotone (latentMap C) →
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    -- physical target: latent bits iid Bernoulli(p), erased set `C(b)`, flagged
    let F := fun (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) =>
      entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.iidLatentErasure (latentMap C) p hp.1 hp.2)).map
    -- true Bernstein coefficients: erasure scores averaged over each latent Hamming layer
    let f := layerAverage (latentMap C) (erasureScore (rowSpace rows))
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots [r]) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n [r])
      (Factory.width HD HS CERT n [r]) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    -- (i) `F` is optimal over all recoveries and is the Bernstein curve of `f`
    (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      F p hp = bernsteinCurve r f p ∧
      ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
        entanglementFidelity (Q.comp
          (lift.iidLatentErasure (latentMap C) p hp.1 hp.2)).map ≤ F p hp) ∧
    -- (ii) the true coefficients are antitone, and those equal to one form a prefix
    Antitone f ∧
    (∃ dC : ℕ, dC ≤ r+1 ∧ ∀ j : Fin (r+1), f j = 1 ↔ j.val < dC) ∧
    -- (iii) every coin string
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input [r] rows C a b c d (List.ofFn coins)))
        (v : Vector (slots [r]-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed*
            (Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L ∧
        Antitone (coefficients v) ∧
        (∀ j, 0 ≤ coefficients v j ∧ coefficients v j ≤ 1) ∧
        coefficients v 0 = f 0 ∧
        coefficients v 0 = erasureScore (rowSpace rows) (latentMap C ∅) ∧
        coefficients v 0 = F 0 ⟨le_rfl, zero_le_one⟩ ∧
        coefficients v (Fin.last r) = f (Fin.last r) ∧
        coefficients v (Fin.last r) = erasureScore (rowSpace rows) (latentMap C Finset.univ) ∧
        coefficients v (Fin.last r) = F 1 ⟨zero_le_one, le_rfl⟩ ∧
        (∀ j, coefficients v j = 1 ↔ f j = 1)) ∧
    -- (iv) one coin event: both relative tails for every `p ∈ [0,1]` simultaneously
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input [r] rows C a b c d (List.ofFn coins)))
        (v : Vector (slots [r]-1)), Outputs M run outputTape v →
          ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
            RelPair ((a:ℝ)/b) (F p hp) (bernsteinCurve r (coefficients v) p)) := by
  obtain ⟨engine,rateConstant,Ptime,Pspace,hrate,hclosed⟩ :=
    isotropic_tensor_machine_guarantee_strong
  refine ⟨engine,rateConstant,Ptime,Pspace,hrate,?_⟩
  intro n r rows C a b c d ha hab hc hd hS hC
  have hCt := tensor_monotone C hC
  obtain ⟨_,hruns,hprob⟩ := hclosed (n:=n) (ds:=[r]) rows C a b c d ha hab hc hd hS hCt
  have hopt := fun p (hp : p ∈ Set.Icc (0:ℝ) 1) =>
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).iidLatentErasure_optimum
      (latentMap C) p hp.1 hp.2
  have hend := (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).iidLatentErasure_endpoints
    (latentMap C)
  have hanti_f : Antitone (layerAverage (latentMap C) (erasureScore (rowSpace rows))) := by
    intro i j hij
    have h := (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS).multivariateCoefficients_antitone
      (TensorEncoding.circuitMap C) hCt
      (show ((i, PUnit.unit) : Grid [r]) ≤ (j, PUnit.unit) from ⟨hij, le_rfl⟩)
    rw [coefficients_eq, coefficients_eq] at h
    exact h
  have hle_f : ∀ j, layerAverage (latentMap C) (erasureScore (rowSpace rows)) j ≤ 1 := by
    intro j
    rw [← coefficients_eq]
    exact (multivariateCoefficients_range _ _ _).2
  refine ⟨?_,hanti_f,eq_one_prefix _ hanti_f hle_f,?_,?_⟩
  · intro p hp
    exact ⟨(hopt p hp).1, fun Q => ((hopt p hp).2 Q).trans (hopt p hp).1.symm.le⟩
  · intro coins
    obtain ⟨run,v,hout,htime,hspace,_,hanti,hrange,hcorner,hone⟩ := hruns coins
    have hlast := hcorner (true, PUnit.unit)
    change vectorTable [r] v (Fin.last r, PUnit.unit) =
        multivariateCoefficients (rowSpace rows) (TensorEncoding.circuitMap C)
          (Fin.last r, PUnit.unit) ∧
      vectorTable [r] v (Fin.last r, PUnit.unit) =
        erasureScore (rowSpace rows)
          (TensorEncoding.circuitMap C (Finset.univ, PUnit.unit)) at hlast
    rw [vectorTable_single, coefficients_eq] at hlast
    have hfirst := hcorner (false, PUnit.unit)
    change vectorTable [r] v (⟨0, Nat.zero_lt_succ r⟩, PUnit.unit) =
        multivariateCoefficients (rowSpace rows) (TensorEncoding.circuitMap C)
          (⟨0, Nat.zero_lt_succ r⟩, PUnit.unit) ∧
      vectorTable [r] v (⟨0, Nat.zero_lt_succ r⟩, PUnit.unit) =
        erasureScore (rowSpace rows)
          (TensorEncoding.circuitMap C (∅, PUnit.unit)) at hfirst
    rw [vectorTable_single, coefficients_eq] at hfirst
    have e : (0 : Fin (r+1)) = ⟨0, Nat.zero_lt_succ r⟩ := Fin.ext (by simp)
    refine ⟨run,v,hout,htime,hspace,?_,?_,?_,?_,?_,hlast.1,hlast.2,?_,?_⟩
    · intro i j hij
      have h := hanti (show ((i, PUnit.unit) : Grid [r]) ≤ (j, PUnit.unit) from ⟨hij, le_rfl⟩)
      rw [vectorTable_single, vectorTable_single] at h
      exact h
    · intro j
      have h := hrange (j, PUnit.unit)
      rw [vectorTable_single] at h
      exact h
    · rw [e]; exact hfirst.1
    · rw [e]; exact hfirst.2
    · rw [e, hfirst.2]
      exact hend.1.symm
    · rw [hlast.2]
      exact hend.2.symm
    · intro j
      have h := hone (j, PUnit.unit)
      rw [vectorTable_single, coefficients_eq] at h
      exact h
  · apply hprob.trans
    apply FiniteProbability.prob_mono
    intro coins hgood run v hv p hp
    have h := hgood run v hv (p, PUnit.unit) ⟨hp, trivial⟩
    rw [vectorCurve_single, fidelity_eq _ C p hp] at h
    exact h

/-- The output's unit coefficients form the same prefix `j < d_C` as the truth's
(a consequence of `f̂ j = 1 ↔ f j = 1` and `eq_one_prefix`; stated for any table
with that identification property). -/
theorem output_prefix {r : ℕ} (f g : Fin (r+1) → ℝ) (hf : Antitone f) (h1 : ∀ j, f j ≤ 1)
    (hg : ∀ j, g j = 1 ↔ f j = 1) :
    ∃ dC : ℕ, dC ≤ r+1 ∧ ∀ j : Fin (r+1), (f j = 1 ↔ j.val < dC) ∧ (g j = 1 ↔ j.val < dC) := by
  obtain ⟨dC, hd, h⟩ := eq_one_prefix f hf h1
  exact ⟨dC, hd, fun j => ⟨h j, (hg j).trans (h j)⟩⟩

end QecReliability.LatentMonotone

#print axioms QecReliability.LatentMonotone.latent_monotone_machine_guarantee
#print axioms QecReliability.LatentMonotone.output_prefix
