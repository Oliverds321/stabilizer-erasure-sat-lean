# Formal statements (Lean 4.34.1)

Verbatim copies of the Lean declarations cited in the manuscript, with file paths (relative to `lean/`) and line ranges, grouped by the part of the paper they belong to. The numbers are: a graph of 6,157 modules, 34 final modules whose 2,386 declarations are audited, and 147 theorems cited in the manuscript audited by name. Both audits (`tools/audit/`) report no axiom other than `propext`, `Classical.choice` and `Quot.sound`.

# 1. The main theorem and the SAT engine

## Theorem 1 and Corollary 3 as one declaration: `QecReliability.IidErasure.iid_erasure_machine_guarantee`

(`IidErasureTheorem.lean`, lines 115-176)

```lean
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
            RelPair ((a:ℝ)/b) (F p hp) (bernsteinCurve n (coefficients v) p))
```

Supporting definitions in the same file: `iidProgram`, `slot`, `coefficients` (entry `j` of the output vector), `position_single` (flat output order is coefficient order), `fidelity_single` (one-class tensor channel = iid channel).

## Proposition 2 (resources) as conjuncts of the machine theorems

(`ResourceAccounting.lean`, lines 467-543)

```lean
theorem iid_erasure_machine_guarantee_resources :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace Pover PtE PsE : PolynomialEnvelope),
    0<rateConstant ∧
    ∃ spec : ResourceEncodedSAT (PrimitiveTransport.machine (PrimitiveLink.queryMachine engine))
      1 PtE PsE (RateMajorant.runtimeEnvelope rateConstant) requestExtent,
    ∀ {n : ℕ}
    (rows : List (List (PauliCoord n))) (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let C := iidProgram n
    let F := fun (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) =>
      entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map
    let f := layerAverage (id : Causes n → Finset (Fin n)) (erasureScore (rowSpace rows))
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots [n]) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n [n])
      (Factory.width HD HS CERT n [n]) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    let q := keySize n [n].sum
    let r := slots [n]-1
    let κ := Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed
    let S := Boundary.satStructuralSize rows C
    let rate := RateMajorant.runtimeEnvelope rateConstant (κ*(S+1))
    let charge := PtE.eval (Boundary.extentPolynomial 1 (data HD HS CERT).Cfixed L)*rate
    -- (i) `F` is optimal over all recoveries and is the Bernstein curve of `f`
    (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      F p hp = bernsteinCurve n f p ∧
      ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
        entanglementFidelity (Q.comp
          (lift.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map ≤ F p hp) ∧
    -- (ii) every coin string
    (∀ coins : Fin N → Bool,
      let ext := TensorMachine.Runtime.external HD HS CERT 1 spec (n:=n) (ds:=[n]) rows C m coins
      ∃ (run : Completed M (input [n] rows C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)) (totals : Totals),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(rate+1) ∧
        run.cells ≤ Pspace.eval L ∧
        Antitone (coefficients v) ∧
        (∀ j, 0 ≤ coefficients v j ∧ coefficients v j ≤ 1) ∧
        coefficients v 0 = 1 ∧
        coefficients v (Fin.last n) = F 1 ⟨zero_le_one, le_rfl⟩ ∧
        coefficients v (Fin.last n) = erasureScore (rowSpace rows) Finset.univ ∧
        coefficients v (Fin.last n) = ((4:ℝ) ^ (n - Module.finrank Bit (rowSpace rows)))⁻¹ ∧
        (∀ j, coefficients v j = 1 ↔ f j = 1) ∧
        -- (R1) bit length of every output coefficient `f̂ j`
        (∀ j : Fin (n+1), (v.get (slot n j)).num ≤ (v.get (slot n j)).den ∧
          (v.get (slot n j)).den ≤ 2*QecReliability.trialValueBound (3*n) B ∧
          (v.get (slot n j)).num.size ≤ 3*n+(4*B+1).size+1 ∧
          (v.get (slot n j)).den.size ≤ 3*n+(4*B+1).size+1) ∧
        -- (R2) SAT calls of the source-level schedule, and their accounting in the run
        totals.calls = CountingTrace.sideCalls q r B m ext true (List.finRange (r+1))+
          CountingTrace.sideCalls q r B m ext false (List.finRange (r+1)) ∧
        totals.calls ≤ 2*(n+1)*(2*m+1)*trialCallCap (3*n) B ∧
        totals.calls ≤ 512*(L+1)^4*(B+1) ∧
        totals.oracleTime = CountingTrace.sideTime q r B m ext true (List.finRange (r+1))+
          CountingTrace.sideTime q r B m ext false (List.finRange (r+1)) ∧
        totals.oracleTime ≤ totals.calls*charge ∧
        run.time ≤ Pover.eval L*(totals.dispatches+1)+
          (3*(PrimitiveLink.queryMachine engine).tapeCount+6)*totals.oracleTime ∧
        totals.dispatches ≤ 8*totals.calls+2*(n+1)*coefficientLocalBound (3*n) m+2*(n+1)+3 ∧
        -- (R3) size of every SAT query in the schedule's index range
        (∀ key, ValidKey q r m key → ∃ req : SATRequest,
          (ext.compileQuery key).bits = QueryCodec.encode req ∧
          req.varCount ≤ κ*(S+1) ∧ req.formula.length ≤ κ*(S+1) ∧
          (ext.sat (ext.compileQuery key).bits).time ≤ charge)) ∧
    -- (iii) one coin event: both relative tails for every `p ∈ [0,1]` simultaneously
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input [n] rows C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)), Outputs M run outputTape v →
          ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
            RelPair ((a:ℝ)/b) (F p hp) (bernsteinCurve n (coefficients v) p))
```

`isotropic_tensor_machine_guarantee_resources` (same file) is the multiclass statement with the same three resource conjuncts; `bound_size`, `outputVector_entry_bounds` and `resource_completion` are its ingredients.

## Machine guarantee for an arbitrary SAT engine

Namespace `QecReliability.TensorMachine.Runtime`. The section variables fix an arbitrary machine `E` with `spec : ResourceEncodedSAT E density Pt Ps T requestExtent` and `hT : Monotone T`, and a hash certificate `A`; `lift` is the physical lift of the row space.

(`TensorMachineGuarantee.lean`, lines 74-95)

```lean
theorem tensor_machine_guarantee : ∃ Ptime Pspace : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ (lift : Lift (rowSpace rows)), Monotone (TensorEncoding.circuitMap C) →
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let N := CodeHash.repeatBits (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m
    (∀ coins : Fin N → Bool,
      ∃ run : Completed MACHINE (input ds rows C a b c d (List.ofFn coins)),
        Outputs MACHINE run (outTape kE)
          (PhysicalAlgorithm.outputVector hD hd A (n:=n) (ds:=ds) rows C spec.service.solver B m coins) ∧
        run.time ≤ Ptime.eval L*(B+1)*(T (Boundary.variableCoefficient density
          (data hD hd A).Cfixed*(Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L) ∧
    (∀ (coins : Fin N → Bool) (run : Completed MACHINE (input ds rows C a b c d (List.ofFn coins)))
      (v : Vector (slots ds-1)), Outputs MACHINE run (outTape kE) v →
        lift.TensorPhysicalStructure (TensorEncoding.circuitMap C) (vectorCurve ds v)) ∧
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed MACHINE (input ds rows C a b c d (List.ofFn coins)))
        (v : Vector (slots ds-1)), Outputs MACHINE run (outTape kE) v →
          lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b) (vectorCurve ds v))
```

## SAT contract: `ResourceEncodedSAT` and `requestExtent` (`ResourceEncodedSAT.lean`, lines 1-23)

```lean
import OracleCost.EncodedSAT

/-! An additional resource-parametric SAT contract. The existing `EncodedSAT`
contract is unchanged. Resource measures and envelopes are proof specifications,
not runtime advice or extra machine inputs. -/
namespace QecReliability.OracleCost
open PrefixCNF MultiTape

/-- Binary payload plus explicitly charged ambient dimension. -/
def requestExtent (request : SATRequest) : ℕ :=
  request.varCount + (QueryCodec.encode request).length

variable {k : ℕ} {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Fintype Λ]

structure ResourceEncodedSAT (M : Machine k Γ Λ) (D : ℕ)
    (Ptime Pspace : PolynomialEnvelope) (T : ℕ → ℕ)
    (resource : SATRequest → ℕ) : Prop where
  positive_density_parameter : 0 < D
  complete : ∀ request : SATRequest, D * request.formula.length ≤ request.varCount →
    ∃ run : Completed M (QueryCodec.encode request),
      (run.output = true ↔ ∃ a, eval request.formula a = true) ∧
      run.time ≤ Ptime.eval (resource request) * T request.varCount ∧
      run.cells ≤ Pspace.eval (resource request)
```

## Concrete engine: `ConcreteSolver.exists_resource_machine` (`ExternalSATConcreteSolver.lean`, lines 93-105)

```lean

/-- The density parameter is fixed at one. The stronger preceding result
handles every typed width-three request, including requests outside that
density restriction. -/
theorem exists_resource_machine :
    ∃ (engine : PrimitiveMachine) (Ptime Pspace : PolynomialEnvelope) (A : ℝ),
      0 < A ∧
      ResourceEncodedSAT (PrimitiveTransport.machine (PrimitiveLink.queryMachine engine))
        1 Ptime Pspace (RateMajorant.runtimeEnvelope A) requestExtent ∧
      Monotone (RateMajorant.runtimeEnvelope A) := by
  obtain ⟨engine, Ptime, Pspace, A, hA, hrun⟩ := exists_bounded_machine
  refine ⟨engine, Ptime, Pspace, A, hA, ?_, RateMajorant.runtimeEnvelope_monotone A⟩
  exact ⟨by decide, fun q _hdensity => hrun q⟩
```

## External engine theorem (openai/math at commit `4eaee875`, `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean`, line 149 ff.)

```lean
theorem sat_polynomial_space (k : ℕ) (hk : 3 ≤ k) :
    ∃ (labels : ℕ) (program : BitProgram.Program 80 1220 labels)
      (C A S : ℝ) (d e : ℕ),
      program.outputStack = 1216 ∧
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
        ∃ (answer : Bool) (time : ℕ)
          (final : LocatedCfg (GuardedCompiler.primitive program)),
          Computation.Trace (locatedStep (GuardedCompiler.primitive program)) time
            (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F)) final ∧
          final.config.tapes (256 : Fin 1220) =
            Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
          final.config.tapes (1216 : Fin 1220) = Turing.Tape.mk₁ [some answer] ∧
          final.config.state = Sum.inl answer ∧
          answer = decide (0 < SAT.count F) ∧
          (answer = true ↔ SAT.Satisfiable F) ∧
          (time : ℝ) ≤ OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength F) n ∧
          ∀ (prefixSteps : ℕ)
            (intermediate : LocatedCfg (GuardedCompiler.primitive program)), prefixSteps ≤ time →
            Computation.Trace (locatedStep (GuardedCompiler.primitive program)) prefixSteps
              (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F))
              intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e
```

`runtimeScale` (`.../SqrtLog/StatementScale.lean`, line 24):

```lean
def runtimeScale (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
    Real.sqrt (Real.log ((n : ℝ) + 16))
```

# 2. Correlated erasures: latent circuits and probability classes

## Single-parameter closure: `isotropic_polynomial_endpoint_machine_guarantee` (`FixedQuantumClosure.lean`, lines 76-121)

```lean

/-- For isotropic stabilizer rows, the physical lift is constructed from the
row space. The engine and polynomial envelopes are fixed before all inputs. -/
theorem isotropic_polynomial_endpoint_machine_guarantee :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Pspace Ptime : PolynomialEnvelope),
    0 < rateConstant ∧ ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    let N := CodeHash.repeatBits
      (Factory.length fixedDegree_eq fixedDegree_scale fixedCertificate n r)
      (Factory.width fixedDegree_eq fixedDegree_scale fixedCertificate n r) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E
      (program fixedDegree_eq fixedDegree_scale fixedCertificate 1) assemblyIndices
    let timeBound := Ptime.eval L*(b/a+1)^2*
      (RateMajorant.runtimeEnvelope rateConstant
        (InputEncoding.queryVariableCoeff
          (gateConstant fixedDegree_eq fixedDegree_scale fixedCertificate) 1*
          (satExtent rows C+1))+1)
    PhysicalTargetOptimality rows C lift ∧
    (∀ w : Fin N → Bool,
      ∃ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
        Final.Outputs M run (Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount) v ∧
        run.time ≤ timeBound ∧ run.cells ≤ Pspace.eval L ∧
        EndpointStructure (rowSpace rows) (circuitMap C) v.curve ∧
        ∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
          TailExact (entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map) (v.curve p)) ∧
    (1-(c:ℝ)/d)*(2:ℝ)^N ≤
      ((Finset.univ.filter (fun w : Fin N → Bool =>
        ∀ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
          Final.Outputs M run (Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount) v →
          lift.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b) v.curve)).card : ℝ) := by
  obtain ⟨engine, rateConstant, Pspace, Ptime, hrate, hclosed⟩ :=
    fixed_polynomial_endpoint_machine_guarantee
  refine ⟨engine, rateConstant, Pspace, Ptime, hrate, ?_⟩
  intro n r rows C a b c d ha hab hc hd hS
  exact hclosed rows C a b c d ha hab hc hd
    (QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS)

end QecReliability.LatentMachine.Runtime.FixedQuantum
```

## Latent theorem: one-class monotone corollary, and the general-circuit form with resources

(`LatentMonotoneTheorem.lean`, lines 99-154)

```lean
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
            RelPair ((a:ℝ)/b) (F p hp) (bernsteinCurve r (coefficients v) p))
```

(`LatentResourceAccounting.lean`, lines 273-358)

```lean
theorem isotropic_latent_machine_guarantee_resources :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Pspace Ptime Pover PtE PsE : PolynomialEnvelope),
    0 < rateConstant ∧
    ∃ spec : ResourceEncodedSAT (PrimitiveTransport.machine (PrimitiveLink.queryMachine engine))
      1 PtE PsE (RateMajorant.runtimeEnvelope rateConstant) requestExtent,
    ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let f := layerAverage (circuitMap C) (score (rowSpace rows))
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let B := rationalCellBudget a b
    let L := InputEncoding.paperLength rows C a b c d
    let N := CodeHash.repeatBits
      (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) assemblyIndices
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    let q := keySize n r
    let G := gateConstant HD HS CERT
    let κ := InputEncoding.queryVariableCoeff G 1
    let S := satExtent rows C
    let rate := RateMajorant.runtimeEnvelope rateConstant (κ*(S+1))
    let timeBound := Ptime.eval L*(b/a+1)^2*(rate+1)
    let charge := PtE.eval (InputEncoding.queryExtentPolynomial G 1 L)*rate
    PhysicalTargetOptimality rows C lift ∧
    -- the target is the Bernstein curve of the true coefficient vector `f`
    (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      entanglementFidelity (lift.erasureFlagDecoder.comp
        (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map = bernsteinCurve r f p) ∧
    (∀ j, 0 < f j ∧ f j ≤ 1) ∧
    -- explicit budgets: B = O(ε⁻²), 2m+1 = O(log(2(r+1)/δ))
    B ≤ 144*(ceilDiv b a)^2 ∧
    2*m+1 ≤ 2*((2*(r+1)-1).size+(ceilDiv d c-1).size)+1 ∧
    (∀ w : Fin N → Bool,
      let seeds := decodeCoins (Factory.length HD HS CERT n r) (Factory.width HD HS CERT n r) m w
      let Hh := actualCodeHash (Factory.system HD HS CERT n r)
      let Kc := Factory.circuits HD HS CERT n r
      let cache := SharedCircuit.ConcreteQuantum.prepare rows C Hh Kc spec.service.solver B m seeds
      let ext := resourceExternal HD HS CERT 1 spec rows C m w
      ∃ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
        Final.Outputs M run outputTape v ∧
        run.time ≤ timeBound ∧ run.cells ≤ Pspace.eval L ∧
        EndpointStructure (rowSpace rows) (circuitMap C) v.curve ∧
        (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
          TailExact (entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.iidLatentErasure (circuitMap C) p hp.1 hp.2)).map) (v.curve p)) ∧
        -- (a) coefficient level: `f̂_j = (v.get j).value`
        v = endpointVector rows C cache ∧
        v.curve = bernsteinCurve r (fun j => (v.get j).value) ∧
        (∀ j, 0 < (v.get j).value ∧ (v.get j).value ≤ 1) ∧
        (v.get 0).value = f 0 ∧
        (v.get 0).value = score (rowSpace rows) (circuitMap C ∅) ∧
        (v.get (Fin.last r)).value = f (Fin.last r) ∧
        (v.get (Fin.last r)).value = score (rowSpace rows) (circuitMap C Finset.univ) ∧
        (∀ j, (v.get j).value = 1 ↔ f j = 1) ∧
        -- (R1) bit length of every output coefficient
        (∀ j, (v.get j).num ≤ (v.get j).den ∧
          (v.get j).den ≤ 2*QecReliability.trialValueBound q B ∧
          (v.get j).num.size ≤ q+(4*B+1).size+1 ∧
          (v.get j).den.size ≤ q+(4*B+1).size+1) ∧
        -- (R2) SAT calls of the cache, and their accounting in the run
        cache.calls ≤ 2*(r+1)*(2*m+1)*trialCallBound q B ∧
        (0 < r → ∃ totals final events,
          OracleCost.WholeWrapperCandidate.Trace q r B m false ext
            (OracleCost.WholeWrapperCandidate.initial q r m) totals events final ∧
          totals.calls = cache.calls ∧
          totals.calls ≤ totalCallCap q r B m ∧
          totals.oracleTime =
            (QuantumService.prepareMeasured rows C Hh Kc spec.service B m seeds).oracleTime ∧
          totals.oracleTime ≤ 2*(r+1)*(2*m+1)*trialCallBound q B*charge ∧
          totals.dispatches ≤ macroDispatchBound q r B m ∧
          run.time ≤ Pover.eval L*(macroDispatchBound q r B m+1)+
            (3*(PrimitiveLink.queryMachine engine).tapeCount+6)*totals.oracleTime) ∧
        -- (R3) size of every SAT query in the schedule's index range
        (0 < r → ∀ key, ValidKey q r m key → ∃ req : SATRequest,
          (ext.compileQuery key).bits = QueryCodec.encode req ∧
          req.varCount ≤ κ*(S+1) ∧ req.formula.length ≤ κ*(S+1) ∧
          (ext.sat (ext.compileQuery key).bits).time ≤ charge)) ∧
    (1-(c:ℝ)/d)*(2:ℝ)^N ≤
      ((Finset.univ.filter (fun w : Fin N → Bool =>
        ∀ (run : Completed M (input rows C a b c d (List.ofFn w))) (v : Vector r),
          Final.Outputs M run outputTape v →
          lift.PhysicalAccuracy (circuitMap C) ((a:ℝ)/b) v.curve)).card : ℝ)
```

## Multiclass closure: `isotropic_tensor_machine_guarantee` (`TensorFixedQuantumClosure.lean`, lines 23-54)

```lean
/-- The engine, fixed reliability program and resource envelopes precede all
runtime inputs. The hypotheses concern the input code, observation map and
requested accuracy/confidence; none assumes a SAT solver or compiler bound. -/
theorem isotropic_tensor_machine_guarantee :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    Monotone (TensorEncoding.circuitMap C) →
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n ds) (Factory.width HD HS CERT n ds) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input ds rows C a b c d (List.ofFn coins))) (v : Vector (slots ds-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed*
            (Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L ∧
        lift.TensorPhysicalStructure (TensorEncoding.circuitMap C) (vectorCurve ds v)) ∧
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input ds rows C a b c d (List.ofFn coins)))
        (v : Vector (slots ds-1)), Outputs M run outputTape v →
          lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b) (vectorCurve ds v)) := by
  obtain ⟨engine,PtE,PsE,rateConstant,hrate,spec,hT⟩ := ConcreteSolver.exists_resource_machine
```

## Strengthened multiclass theorem: `...TensorMachine.Runtime.FixedQuantum.isotropic_tensor_machine_guarantee_strong`

(`TensorFixedQuantumStrong.lean`, lines 264-323)

```lean
/-- The explicit packed-semantic certificate, without `Classical.choice`. -/
@[irreducible] noncomputable def explicitCertificate :
    CertifiedParity (512 * fixedScale) (64 * fixedScale) fixedScale :=
  PackedSemanticBridgeCandidate.localCertified fixedScale fixedScale_pos

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => explicitCertificate

theorem isotropic_tensor_machine_guarantee_strong :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    Monotone (TensorEncoding.circuitMap C) →
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let f := multivariateCoefficients (rowSpace rows) (TensorEncoding.circuitMap C)
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n ds) (Factory.width HD HS CERT n ds) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    -- (a) the target is the Bernstein curve of `f`, and it is optimal over all recoveries
    (∀ p (hp : cube ds p),
      entanglementFidelity (lift.erasureFlagDecoder.comp
          (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map =
        curve ds f p ∧
      ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
        entanglementFidelity (Q.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map ≤
          entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map) ∧
    -- (b,c) every coin string: completed run, output, resources, curve and table structure
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input ds rows C a b c d (List.ofFn coins))) (v : Vector (slots ds-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed*
            (Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L ∧
        lift.TensorPhysicalStructure (TensorEncoding.circuitMap C) (vectorCurve ds v) ∧
        -- the output table is antitone in the componentwise order
        Antitone (vectorTable ds v) ∧
        -- every output coefficient lies in the unit interval
        (∀ j, 0 ≤ vectorTable ds v j ∧ vectorTable ds v j ≤ 1) ∧
        -- every corner coefficient is the exact physical score
        (∀ b : Corner ds, vectorTable ds v (cornerIndex ds b) = f (cornerIndex ds b) ∧
          vectorTable ds v (cornerIndex ds b) =
            erasureScore (rowSpace rows) (TensorEncoding.circuitMap C (cornerCauses ds b))) ∧
        -- zero-infidelity coefficients are identified exactly
        (∀ j, vectorTable ds v j = 1 ↔ f j = 1)) ∧
    -- (c) one coin event gives two-tail accuracy on the whole parameter cube
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input ds rows C a b c d (List.ofFn coins)))
        (v : Vector (slots ds-1)), Outputs M run outputTape v →
          lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b) (vectorCurve ds v))
```

## Multiclass theorem for general circuits (no monotonicity hypothesis)

(`TensorGeneralCircuit.lean`, lines 29-78)

```lean
theorem isotropic_tensor_machine_guarantee_general :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace rows) hS
    let f := multivariateCoefficients (rowSpace rows) (TensorEncoding.circuitMap C)
    let L := Boundary.resourceSize rows C a b c d
    let B := rationalCellBudget a b
    let m := rationalRepetitionBudget (2*slots ds) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT n ds) (Factory.width HD HS CERT n ds) m
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (QecReliability.TensorMachineG.Runtime.program HD HS CERT 1)
      (QecReliability.TensorMachineG.Runtime.indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    -- (a) the target is the Bernstein curve of `f`, and it is optimal over all recoveries
    (∀ p (hp : cube ds p),
      entanglementFidelity (lift.erasureFlagDecoder.comp
          (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map =
        curve ds f p ∧
      ∀ Q : Channel (ErasureFlagOutput n) lift.LogicalIndex,
        entanglementFidelity (Q.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map ≤
          entanglementFidelity (lift.erasureFlagDecoder.comp
            (lift.multivariateLatentErasure (TensorEncoding.circuitMap C) p hp)).map) ∧
    -- (b) every coin string: completed run, output, resources, table and curve structure
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input ds rows C a b c d (List.ofFn coins))) (v : Vector (slots ds-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed*
            (Boundary.satStructuralSize rows C+1))+1) ∧
        run.cells ≤ Pspace.eval L ∧
        -- every output coefficient lies in the unit interval
        (∀ j, 0 ≤ vectorTable ds v j ∧ vectorTable ds v j ≤ 1) ∧
        -- every corner coefficient is the exact physical score
        (∀ b : Corner ds, vectorTable ds v (cornerIndex ds b) = f (cornerIndex ds b) ∧
          vectorTable ds v (cornerIndex ds b) =
            erasureScore (rowSpace rows) (TensorEncoding.circuitMap C (cornerCauses ds b))) ∧
        -- zero-infidelity coefficients are identified exactly
        (∀ j, vectorTable ds v j = 1 ↔ f j = 1) ∧
        -- the output curve lies in [0,1] on the cube and is exact at every corner
        TensorGeneral.GeneralStructure rows (TensorEncoding.circuitMap C) lift (vectorCurve ds v)) ∧
    -- (c) one coin event gives two-tail accuracy on the whole parameter cube
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input ds rows C a b c d (List.ofFn coins)))
        (v : Vector (slots ds-1)), Outputs M run outputTape v →
          lift.TensorPhysicalAccuracy (TensorEncoding.circuitMap C) ((a:ℝ)/b) (vectorCurve ds v))
```

# 3. Hardness

## Distance determination (Proposition 12)

(`DistanceDetermination.lean`, lines 113-117)

```lean
theorem zero_prefix_iff (b c : Fin (n + 1) → ℝ) (hb : ∀ j, 0 ≤ b j) {ε : ℝ} (hε : ε < 1)
    (h : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve n c p - bernsteinCurve n b p| ≤ ε * bernsteinCurve n b p)
    (j : Fin (n + 1)) :
    (∀ i ≤ j, c i = 0) ↔ (∀ i ≤ j, b i = 0)
```

(`DistanceDetermination.lean`, lines 226-234)

```lean
theorem Lift.distance_determination {n : ℕ} {S : Submodule Bit (Pauli n)} (L : Lift S)
    (c : Fin (n + 1) → ℝ) {ε : ℝ} (hε : ε < 1)
    (h : ∀ p (hp : p ∈ Set.Icc (0 : ℝ) 1),
      |bernsteinCurve n c p - (1 - entanglementFidelity (L.erasureFlagDecoder.comp
          (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map)| ≤
        ε * (1 - entanglementFidelity (L.erasureFlagDecoder.comp
          (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp.1 hp.2)).map))
    (j : Fin (n + 1)) :
    (∀ i ≤ j, c i = 0) ↔ (∀ E : Finset (Fin n), E.card ≤ j.val → erasureScore S E = 1)
```

## Reduction from CNF satisfiability to the distance of a code with one logical qubit

All in namespace `QecReliability.SatReduction`. `Instance` packages the number of qubits, the check rows and the threshold; `reduce` is a function on `Std.Sat.CNF Nat`.

(`SatToDistance.lean`, lines 786-787)

```lean
def reduce (φ : Std.Sat.CNF Nat) : Instance :=
  ⟨(formulaOf φ).nq, (formulaOf φ).rows, (formulaOf φ).thr⟩
```

(`SatToDistance.lean`, lines 789-790)

```lean
theorem reduce_isotropic (φ : Std.Sat.CNF Nat) :
    rowSpace (reduce φ).rows ≤ normalizer (symplectic (reduce φ).n) (rowSpace (reduce φ).rows)
```

(`SatToDistance.lean`, lines 794-796)

```lean
theorem reduce_correct (φ : Std.Sat.CNF Nat) :
    (∃ a, φ.Sat a) ↔ ∃ E : Finset (Fin (reduce φ).n), E.card ≤ (reduce φ).thr ∧
      0 < ambiguity (symplectic (reduce φ).n) (rowSpace (reduce φ).rows) (supported E)
```

(`SatToDistance.lean`, lines 801-802)

```lean
theorem reduce_isDistance_le_iff (φ : Std.Sat.CNF Nat) {d : ℕ}
    (hd : IsDistance (rowSpace (reduce φ).rows) d) : d ≤ (reduce φ).thr ↔ ∃ a, φ.Sat a
```

(`SatToDistance.lean`, lines 806-807)

```lean
theorem reduce_isDistance_eq (φ : Std.Sat.CNF Nat) {d : ℕ}
    (hd : IsDistance (rowSpace (reduce φ).rows) d) (hsat : ∃ a, φ.Sat a) : d = (reduce φ).thr
```

(`SatToDistance.lean`, lines 811-812)

```lean
theorem reduce_exists_isDistance (φ : Std.Sat.CNF Nat) :
    ∃ d, IsDistance (rowSpace (reduce φ).rows) d
```

(`SatToDistance.lean`, lines 959-962)

```lean
theorem reduce_size (φ : Std.Sat.CNF Nat) :
    (reduce φ).n ≤ 3 * (varBound φ.clauses.toList + litCount φ.clauses.toList + 4) ^ 2 ∧
      rowIncidences (reduce φ).rows ≤
        12 * (varBound φ.clauses.toList + litCount φ.clauses.toList + 4) ^ 3
```

(`SatLogicalQubit.lean`, lines 291-292)

```lean
theorem reduce_finrank (φ : Std.Sat.CNF Nat) :
    Module.finrank Bit (rowSpace (reduce φ).rows) + 1 = (reduce φ).n
```

(`SatLogicalQubit.lean`, lines 296-297)

```lean
theorem reduce_logical_qubits (φ : Std.Sat.CNF Nat) :
    (reduce φ).n - Module.finrank Bit (rowSpace (reduce φ).rows) = 1
```

Composition with the extraction of the distance from an output of the algorithm, from one value of the infidelity, and from one value of the uncorrectable-erasure probability:

(`SatHardness.lean`, lines 33-44)

```lean
theorem sat_iff_table (φ : Std.Sat.CNF Nat) (c : ℚ) (hc : 1 < c) {ε : ℝ} (hε : ε < 1)
    (A : List (List (PauliCoord ((reduce φ).n + padM c (reduce φ).rows))) →
      Fin ((reduce φ).n + padM c (reduce φ).rows + 1) → ℚ)
    (hA : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve ((reduce φ).n + padM c (reduce φ).rows)
          (fun j => (A (sparsePad c (reduce φ).rows) j : ℝ)) p -
          infidelity (rowSpace (sparsePad c (reduce φ).rows)) p| ≤
        ε * infidelity (rowSpace (sparsePad c (reduce φ).rows)) p) :
    (rowIncidences (sparsePad c (reduce φ).rows) : ℚ) ≤
        c * (((reduce φ).n + padM c (reduce φ).rows : ℕ) : ℚ) ∧
      (distanceOfTable (A (sparsePad c (reduce φ).rows)) ≤ (reduce φ).thr ↔ ∃ a, φ.Sat a) ∧
      ((∃ a, φ.Sat a) → distanceOfTable (A (sparsePad c (reduce φ).rows)) = (reduce φ).thr)
```

(`SatHardness.lean`, lines 52-64)

```lean
theorem sat_iff_point (φ : Std.Sat.CNF Nat) (c : ℚ) (hc : 1 < c) (h : ℕ)
    (A : List (List (PauliCoord ((reduce φ).n + padM c (reduce φ).rows))) → ℚ)
    (hA : infidelity (rowSpace (sparsePad c (reduce φ).rows))
          (pointAt ((reduce φ).n + padM c (reduce φ).rows) h) / ((2 : ℚ) ^ h : ℚ)
          ≤ A (sparsePad c (reduce φ).rows) ∧
        (A (sparsePad c (reduce φ).rows) : ℝ) ≤ ((2 : ℚ) ^ h : ℚ) *
          infidelity (rowSpace (sparsePad c (reduce φ).rows))
            (pointAt ((reduce φ).n + padM c (reduce φ).rows) h)) :
    (rowIncidences (sparsePad c (reduce φ).rows) : ℚ) ≤
        c * (((reduce φ).n + padM c (reduce φ).rows : ℕ) : ℚ) ∧
      (distanceOfPoint ((reduce φ).n + padM c (reduce φ).rows)
          (pointAt ((reduce φ).n + padM c (reduce φ).rows) h) (2 ^ h)
          (A (sparsePad c (reduce φ).rows)) ≤ (reduce φ).thr ↔ ∃ a, φ.Sat a)
```

(`SatHardness.lean`, lines 73-85)

```lean
theorem sat_iff_pointU (φ : Std.Sat.CNF Nat) (c : ℚ) (hc : 1 < c) (h : ℕ)
    (A : List (List (PauliCoord ((reduce φ).n + padM c (reduce φ).rows))) → ℚ)
    (hA : uncorrectableProb (rowSpace (sparsePad c (reduce φ).rows))
          (pointAt ((reduce φ).n + padM c (reduce φ).rows) h) / ((2 : ℚ) ^ h : ℚ)
          ≤ A (sparsePad c (reduce φ).rows) ∧
        (A (sparsePad c (reduce φ).rows) : ℝ) ≤ ((2 : ℚ) ^ h : ℚ) *
          uncorrectableProb (rowSpace (sparsePad c (reduce φ).rows))
            (pointAt ((reduce φ).n + padM c (reduce φ).rows) h)) :
    (rowIncidences (sparsePad c (reduce φ).rows) : ℚ) ≤
        c * (((reduce φ).n + padM c (reduce φ).rows : ℕ) : ℚ) ∧
      (distanceOfPointU ((reduce φ).n + padM c (reduce φ).rows)
          (pointAt ((reduce φ).n + padM c (reduce φ).rows) h) (2 ^ h)
          (A (sparsePad c (reduce φ).rows)) ≤ (reduce φ).thr ↔ ∃ a, φ.Sat a)
```

Not formalized: the Cook-Levin theorem and the polynomial running time of `reduce` (its output size is bounded by `reduce_size`).

## Padding step of the sparse-hardness corollary

(`PaddingInvariance.lean`, lines 64-65)

```lean
def pad (m : ℕ) (S : Submodule Bit (Pauli n)) : Submodule Bit (Pauli (n + m)) where
  carrier := {v | oldPart m v ∈ S ∧ ∀ j : Fin m, v.1 (Fin.natAdd n j) = 0}
```

(`PaddingInvariance.lean`, lines 234-235)

```lean
theorem erasureScore_pad (S : Submodule Bit (Pauli n)) (E' : Finset (Fin (n + m))) :
    erasureScore (pad m S) E' = erasureScore S (oldSet m E')
```

(`PaddingInvariance.lean`, lines 314-320)

```lean
theorem isotropicLift_fidelity_pad {S : Submodule Bit (Pauli n)}
    (hS : S ≤ normalizer (symplectic n) S) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementFidelity ((isotropicLift (pad m S) (pad_isotropic hS)).erasureFlagDecoder.comp
        ((isotropicLift (pad m S) (pad_isotropic hS)).iidLatentErasure
          (id : Causes (n + m) → Finset (Fin (n + m))) p hp0 hp1)).map =
      entanglementFidelity ((isotropicLift S hS).erasureFlagDecoder.comp
        ((isotropicLift S hS).iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0 hp1)).map :=
```

(`PaddingInvariance.lean`, lines 338-339)

```lean
theorem rowIncidences_padRows (rows : List (List (PauliCoord n))) :
    rowIncidences (padRows m rows) = rowIncidences rows + m
```

(`PaddingInvariance.lean`, lines 367-368)

```lean
theorem rowSpace_padRows (rows : List (List (PauliCoord n))) :
    rowSpace (padRows m rows) = pad m (rowSpace rows)
```

## Single-value hardness (tail sandwich, point estimates determine the distance)

(`PointHardness.lean`, lines 26-28)

```lean
def IsDistance (S : Submodule Bit (Pauli n)) (d : ℕ) : Prop :=
  (∀ E : Finset (Fin n), E.card < d → ¬ (0 < ambiguity (symplectic n) S (supported E))) ∧
    ∃ E : Finset (Fin n), E.card = d ∧ 0 < ambiguity (symplectic n) S (supported E)
```

(`PointHardness.lean`, lines 144-148)

```lean
theorem tail_sandwich (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ d / 2 ≤ infidelity S p ∧ infidelity S p ≤ (n.choose d : ℝ) * p ^ d ∧
      p ^ d ≤ uncorrectableProb S p ∧ uncorrectableProb S p ≤ (n.choose d : ℝ) * p ^ d
```

(`PointHardness.lean`, lines 203-208)

```lean
theorem infidelity_point_determines_distance (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p R est : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hR : 1 ≤ R)
    (hsmall : (2:ℝ) ^ (n + 1) * R ^ 2 * p < 1)
    (hest : infidelity S p / R ≤ est ∧ est ≤ R * infidelity S p) (d' : ℕ) :
    (p ^ d' / (2 * R) ≤ est ∧ est ≤ (2:ℝ) ^ n * R * p ^ d') ↔ d' = d
```

(`PointHardness.lean`, lines 220-228)

```lean
theorem channel_point_determines_distance {S : Submodule Bit (Pauli n)} (L : Lift S)
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p R est : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hR : 1 ≤ R)
    (hsmall : (2:ℝ) ^ (n + 1) * R ^ 2 * p < 1)
    (hest : (1 - entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0.le hp1)).map) / R ≤ est ∧
      est ≤ R * (1 - entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0.le hp1)).map)) (d' : ℕ) :
    (p ^ d' / (2 * R) ≤ est ∧ est ≤ (2:ℝ) ^ n * R * p ^ d') ↔ d' = d
```

(`PointHardness.lean`, lines 233-238)

```lean
theorem uncorrectableProb_point_determines_distance (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p R est : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hR : 1 ≤ R)
    (hsmall : (2:ℝ) ^ n * R ^ 2 * p < 1)
    (hest : uncorrectableProb S p / R ≤ est ∧ est ≤ R * uncorrectableProb S p) (d' : ℕ) :
    (p ^ d' / R ≤ est ∧ est ≤ (2:ℝ) ^ n * R * p ^ d') ↔ d' = d
```

(`PointHardness.lean`, lines 299-303)

```lean
theorem distance_le_iff_certificate (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d) (w : ℕ) :
    d ≤ w ↔ ∃ E : Finset (Fin n), E.card ≤ w ∧
        ∃ x ∈ localized (symplectic n) S (supported E),
          ∃ z ∈ normalizer (symplectic n) S, symplectic n x z = 1
```

## The sparse and single-value corollaries as explicit extraction procedures

(`DistanceExtraction.lean`, lines 380-390)

```lean
theorem cor_sparsehard_extraction (rows : List (List (PauliCoord n))) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) (c : ℚ) (hc : 1 < c) {ε : ℝ} (hε : ε < 1)
    (A : List (List (PauliCoord (n + padM c rows))) → Fin (n + padM c rows + 1) → ℚ)
    (hA : ∀ p ∈ Set.Ioc (0 : ℝ) 1,
      |bernsteinCurve (n + padM c rows) (fun j => (A (sparsePad c rows) j : ℝ)) p -
          infidelity (rowSpace (sparsePad c rows)) p| ≤
        ε * infidelity (rowSpace (sparsePad c rows)) p) :
    (rowIncidences (sparsePad c rows) : ℚ) ≤ c * ((n + padM c rows : ℕ) : ℚ) ∧
      IsDistance (rowSpace (sparsePad c rows)) d ∧
      (∀ p : ℝ, infidelity (rowSpace (sparsePad c rows)) p = infidelity (rowSpace rows) p) ∧
      distanceOfTable (A (sparsePad c rows)) = d
```

(`DistanceExtraction.lean`, lines 418-428)

```lean
theorem cor_pointhard_extraction (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) (c : ℚ) (hc : 1 < c) (h : ℕ)
    (A : List (List (PauliCoord (n + padM c rows))) → ℚ)
    (hA : infidelity (rowSpace (sparsePad c rows)) (pointAt (n + padM c rows) h) / ((2 : ℚ) ^ h : ℚ)
          ≤ A (sparsePad c rows) ∧
        (A (sparsePad c rows) : ℝ) ≤
          ((2 : ℚ) ^ h : ℚ) * infidelity (rowSpace (sparsePad c rows)) (pointAt (n + padM c rows) h)) :
    (rowIncidences (sparsePad c rows) : ℚ) ≤ c * ((n + padM c rows : ℕ) : ℚ) ∧
      distanceOfPoint (n + padM c rows) (pointAt (n + padM c rows) h) (2 ^ h)
        (A (sparsePad c rows)) = d
```

(`DistanceExtraction.lean`, lines 438-448)

```lean
theorem cor_pointhard_extractionU (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) (c : ℚ) (hc : 1 < c) (h : ℕ)
    (A : List (List (PauliCoord (n + padM c rows))) → ℚ)
    (hA : uncorrectableProb (rowSpace (sparsePad c rows)) (pointAt (n + padM c rows) h) /
          ((2 : ℚ) ^ h : ℚ) ≤ A (sparsePad c rows) ∧
        (A (sparsePad c rows) : ℝ) ≤ ((2 : ℚ) ^ h : ℚ) *
          uncorrectableProb (rowSpace (sparsePad c rows)) (pointAt (n + padM c rows) h)) :
    (rowIncidences (sparsePad c rows) : ℚ) ≤ c * ((n + padM c rows : ℕ) : ℚ) ∧
      distanceOfPointU (n + padM c rows) (pointAt (n + padM c rows) h) (2 ^ h)
        (A (sparsePad c rows)) = d
```

## The completeness formula: converse, and the exact distance from satisfiability

(`CompletenessConverse.lean`, lines 226-232)

```lean
theorem certFormula_sat_iff {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L : ℕ)
    (mins : List (List (Fin n))) (units : List (Fin n × Bool)) :
    (∃ a, (certFormula rows L mins units).Sat a) ↔
      ∃ E : Finset (Fin n), E.card ≤ L ∧ (∀ u ∈ units, (u.1 ∈ E ↔ u.2 = true)) ∧
        (∀ M ∈ mins, ¬ M.toFinset ⊆ E) ∧
        0 < ambiguity (symplectic n) (rowSpace rows) (supported E)
```

(`CompletenessConverse.lean`, lines 243-247)

```lean
theorem sat_iff_exists_uncorrectable {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L : ℕ) :
    (∃ a, (certFormula rows L [] []).Sat a) ↔
      ∃ E : Finset (Fin n), E.card ≤ L ∧
        0 < ambiguity (symplectic n) (rowSpace rows) (supported E)
```

(`CompletenessConverse.lean`, lines 261-264)

```lean
theorem distance_le_iff_sat {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) (L : ℕ) :
    d ≤ L ↔ ∃ a, (certFormula rows L [] []).Sat a
```

(`CompletenessConverse.lean`, lines 269-272)

```lean
theorem distance_isLeast {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) {d : ℕ}
    (hd : IsDistance (rowSpace rows) d) :
    IsLeast {L : ℕ | ∃ a, (certFormula rows L [] []).Sat a} d
```

## Weight enumerators as model counts of 3-CNF formulas

(`EnumeratorFormula.lean`, lines 575-579)

```lean
theorem normWeightFormula_count :
    (Finset.univ.filter (fun a : Fin (normWeightVars rows t) → Bool =>
      (normWeightFormula rows t).eval
        (fun v => if h : v < normWeightVars rows t then a ⟨v, h⟩ else false) = true)).card =
      weightCount (normalizer (symplectic n) (rowSpace rows)) t
```

(`EnumeratorFormula.lean`, lines 597-598)

```lean
theorem normWeightFormula_width :
    ∀ c ∈ (normWeightFormula rows t).clauses, c.length ≤ 3
```

(`EnumeratorFormula.lean`, lines 1085-1086)

```lean
theorem normWeightVars_eq :
    normWeightVars rows t = (2 * t + 5) * n + rowIncidences rows + 2
```

(`EnumeratorFormula.lean`, lines 930-934)

```lean
theorem stabWeightFormula_count :
    (Finset.univ.filter (fun a : Fin (stabWeightVars rows t) → Bool =>
      (stabWeightFormula rows t).eval
        (fun v => if h : v < stabWeightVars rows t then a ⟨v, h⟩ else false) = true)).card =
      2 ^ (rows.length - Module.finrank Bit (rowSpace rows)) * weightCount (rowSpace rows) t
```

(`EnumeratorFormula.lean`, lines 957-958)

```lean
theorem stabWeightFormula_width :
    ∀ c ∈ (stabWeightFormula rows t).clauses, c.length ≤ 3
```

(`EnumeratorFormula.lean`, lines 1091-1092)

```lean
theorem stabWeightVars_eq :
    stabWeightVars rows t = (2 * t + 3) * n + rowIncidences rows + rows.length + 2
```

The statements are inside sections with variables `{n : ℕ} (rows : List (List (PauliCoord n))) (t : ℕ)`; `weightCount T w` is the number of elements of `T` of Pauli weight `w` (`EnumeratorExample.lean`). These are statements about the formulas; a machine that calls a counting engine on them is not formalized.

# 4. Uncorrectable-erasure probability

## General anchored repair (Lemma 11) and the uncorrectable-erasure probability (the uncorrectable-probability corollary, mathematical core)

(`UncorrectableProbability.lean`, lines 76-84)

```lean
theorem repair_interval (anchors : Finset ι) (anchorValues estimates f : ι → ℝ)
    (lo hi : ℝ → ℝ)
    (hlo : MonotoneOn lo (Set.Icc 0 1)) (_hhi : MonotoneOn hi (Set.Icc 0 1))
    (hlo_le : ∀ t ∈ Set.Icc (0:ℝ) 1, lo t ≤ t) (hle_hi : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≤ hi t)
    (hanti : Antitone f) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hanchor : ∀ a ∈ anchors, anchorValues a = f a)
    (hest : ∀ i, lo (f i) ≤ estimates i ∧ estimates i ≤ hi (f i)) :
    ∀ j, lo (f j) ≤ repair anchors anchorValues estimates j ∧
         repair anchors anchorValues estimates j ≤ hi (f j) :=
```

(`UncorrectableProbability.lean`, lines 149-153)

```lean
theorem uncorrectable_iff_certificate (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (E : Finset (Fin n)) :
    0 < ambiguity (symplectic n) S (supported E) ↔
      ∃ x ∈ localized (symplectic n) S (supported E),
        ∃ z ∈ normalizer (symplectic n) S, symplectic n x z = 1
```

(`UncorrectableProbability.lean`, lines 245-251)

```lean
theorem channel_infidelity_le_uncorrectableProb {S : Submodule Bit (Pauli n)} (L : Lift S)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0 hp1)).map ≤
        uncorrectableProb S p ∧
      uncorrectableProb S p ≤ 2 * (1 - entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0 hp1)).map)
```

(`UncorrectableProbability.lean`, lines 422-426)

```lean
theorem repairedCurve_rel {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ j, (1 - ε) * layerFraction S j ≤ c j ∧ c j ≤ (1 + ε) * layerFraction S j)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |bernsteinCurve n (repairedFraction S c) p - uncorrectableProb S p| ≤
      ε * uncorrectableProb S p
```

Other statements in that module (`uncorrectable_mono`, `uncorrectableProb_eq_bernstein`, `layerFraction_monotone`, `repairedFraction_monotone`, `repairedFraction_zero`, `repairedFraction_last`, `repairedFraction_rel`, `repairedFraction_eq_zero_iff`, `repairedCurve_monotoneOn`, `repairedCurve_range`) are listed in the by-name audit.

## Uncorrectable-erasure probability at machine level (repeated code)

(`ProductCode.lean`, lines 197-199)

```lean
theorem ambiguity_rep (S : Submodule Bit (Pauli n)) (E : Finset (Fin n)) :
    ambiguity (symplectic (n * m)) (power m S) (supported (rep m E)) =
      m * ambiguity (symplectic n) S (supported E)
```

(`ProductCode.lean`, lines 256-259)

```lean
theorem uncorrectableProb_sandwich (S : Submodule Bit (Pauli n)) (m : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - ((2 : ℝ) ^ m)⁻¹) * uncorrectableProb S p ≤ powerInfidelity m S p ∧
      powerInfidelity m S p ≤ uncorrectableProb S p
```

(`ProductCode.lean`, lines 294-298)

```lean
theorem uncorrectable_relative_of_half (S : Submodule Bit (Pauli n)) (m : ℕ) {p ε u : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 2)
    (hm : ((2 : ℝ) ^ m)⁻¹ ≤ ε / 2)
    (hu : |u - powerInfidelity m S p| ≤ ε / 2 * powerInfidelity m S p) :
    |u - uncorrectableProb S p| ≤ ε * uncorrectableProb S p
```

(`UncorrectableMachine.lean`, lines 87-130)

```lean
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
            (((2:ℝ)^m)⁻¹ ≤ (a:ℝ)/b → |Uhat v p - U p| ≤ 2 * ((a:ℝ)/b) * U p))
```

(`UncorrectableMachineSized.lean`, lines 123-125)

```lean
theorem satStructuralSize_dup (n m : ℕ) (rows : List (List (PauliCoord n))) :
    Boundary.satStructuralSize (rowsPower m rows) (dupProgram n m) =
      n*m+n+m*rowIncidences rows+1
```

(`UncorrectableMachineSized.lean`, lines 142-145)

```lean
theorem resourceSize_dup_le (n m : ℕ) (rows : List (List (PauliCoord n))) (a b c d : ℕ)
    (hm : 1 ≤ m) :
    Boundary.resourceSize (rowsPower m rows) (dupProgram n m) a b c d ≤
      sizedLength n m rows a b c d
```

`uncorrectable_machine_guarantee_sized` (same file) restates the theorem with the time bound `Ptime.eval L' * (B+1) * (runtimeEnvelope rateConstant (K' * m * (n + rowIncidences rows + 1)) + 1)` and the space bound `Pspace.eval L'`, `L' = sizedLength n m rows a b c d`.

## Uncorrectable sets of a given size as the projected models of one 3-CNF

(`UncorrectableFormula.lean`, lines 38-41)

```lean
noncomputable def uncCount {n : ℕ} (S : Submodule Bit (Pauli n)) (j : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun E : Finset (Fin n) =>
    E.card = j ∧ 0 < ambiguity (symplectic n) S (supported E)).card
```

(`UncorrectableFormula.lean`, lines 44-46)

```lean
theorem uncorrectableProb_eq_counts {n : ℕ} (S : Submodule Bit (Pauli n)) (p : ℝ) :
    uncorrectableProb S p =
      ∑ j ∈ Finset.range (n + 1), (uncCount S j : ℝ) * (p ^ j * (1 - p) ^ (n - j))
```

(`UncorrectableFormula.lean`, lines 71-74)

```lean
def uncFormula : Formula (n + hiddenVars rows j) :=
  rename (Fin.cast (Nat.add_assoc n (n + n)
    (BadEncoding.witnessSize n + (BadEncoding.layerBlock rows j).aux)))
    (BadEncoding.layerFormula rows j)
```

(`UncorrectableFormula.lean`, lines 112-116)

```lean
theorem uncFormula_projected
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (hj : j ≤ n)
    (E : Finset (Fin n)) :
    Projected (uncFormula rows j) (causeBits n E) ↔
      E.card = j ∧ 0 < ambiguity (symplectic n) (rowSpace rows) (supported E)
```

(`UncorrectableFormula.lean`, lines 129-132)

```lean
theorem uncFormula_count
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (hj : j ≤ n) :
    PrefixEnumeration.modelCount (Projected (uncFormula rows j)) =
      uncCount (rowSpace rows) j
```

(`UncorrectableFormula.lean`, lines 151-161)

```lean
theorem uncFormula_contract
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (hj : j ≤ n) :
    Width 3 (uncFormula rows j) ∧
    (uncFormula rows j).length ≤ 18 * rowIncidences rows + 99 * n + 52 ∧
    n + hiddenVars rows j ≤ 29 * n + 4 * rowIncidences rows + 12 ∧
    (∀ E : Finset (Fin n), Projected (uncFormula rows j) (causeBits n E) ↔
      E.card = j ∧ 0 < ambiguity (symplectic n) (rowSpace rows) (supported E)) ∧
    PrefixEnumeration.modelCount (Projected (uncFormula rows j)) =
      uncCount (rowSpace rows) j ∧
    ∀ p : ℝ, uncorrectableProb (rowSpace rows) p =
      ∑ i ∈ Finset.range (n + 1), (uncCount (rowSpace rows) i : ℝ) * (p ^ i * (1 - p) ^ (n - i))
```

Inside a section with variables `{n : ℕ} (rows : List (List (PauliCoord n))) (j : ℕ)`. `Projected F e` means that the assignment `e` of the first `n` variables extends to a model of `F`; `causeBits n E` is the indicator assignment of `E`; `0 < ambiguity ...` is the predicate behind `uncorrectable`. This is the formula-level step of the direct algorithm for the uncorrectable-erasure probability; a machine that runs it is not formalized (the machine-level theorem is `uncorrectable_machine_guarantee`, through the repeated code).

# 5. Comparisons and worked examples

## Worked examples: equal weight enumerators, different erasure curves

(`EnumeratorExample.lean`, lines 39-39)

```lean
def rowsR : List (List (PauliCoord 3)) := [[.inr 0, .inr 1], [.inr 1, .inr 2]]
```

(`EnumeratorExample.lean`, lines 42-42)

```lean
def rowsB : List (List (PauliCoord 3)) := [[.inl 0, .inl 1], [.inr 0, .inr 1]]
```

(`EnumeratorExample.lean`, lines 144-148)

```lean
theorem layerSum_R :
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 0), erasureScore (rowSpace rowsR) E = 1 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 1), erasureScore (rowSpace rowsR) E = 3/2 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 2), erasureScore (rowSpace rowsR) E = 3/2 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 3), erasureScore (rowSpace rowsR) E = 1/4
```

(`EnumeratorExample.lean`, lines 154-158)

```lean
theorem layerSum_B :
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 0), erasureScore (rowSpace rowsB) E = 1 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 1), erasureScore (rowSpace rowsB) E = 9/4 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 2), erasureScore (rowSpace rowsB) E = 3/2 ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin 3) => E.card = 3), erasureScore (rowSpace rowsB) E = 1/4
```

(`EnumeratorExample.lean`, lines 249-254)

```lean
theorem physical_difference (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementFidelity (liftB.erasureFlagDecoder.comp
        (liftB.iidLatentErasure (id : Causes 3 → Finset (Fin 3)) p hp hp1)).map -
      entanglementFidelity (liftR.erasureFlagDecoder.comp
        (liftR.iidLatentErasure (id : Causes 3 → Finset (Fin 3)) p hp hp1)).map =
      (3/4) * p * (1 - p) ^ 2
```

(`EnumeratorExample.lean`, lines 348-349)

```lean
theorem stabilizer_enumerators_eq (w : ℕ) :
    weightCount (rowSpace rowsR) w = weightCount (rowSpace rowsB) w
```

(`EnumeratorExample.lean`, lines 356-358)

```lean
theorem normalizer_enumerators_eq (w : ℕ) :
    weightCount (normalizer (symplectic 3) (rowSpace rowsR)) w =
      weightCount (normalizer (symplectic 3) (rowSpace rowsB)) w
```

(`EnumeratorExample.lean`, lines 386-386)

```lean
theorem bare_infidelity (p : ℝ) : infidelity (rowSpace rowsBare) p = (3/4) * p
```

(`EnumeratorExample.lean`, lines 397-397)

```lean
theorem bare_uncorrectableProb (p : ℝ) : uncorrectableProb (rowSpace rowsBare) p = p
```

(`EnumeratorExample.lean`, lines 414-416)

```lean
theorem four_correctable (E : Finset (Fin 4)) :
    erasureScore (rowSpace rows4) E = 1 ↔
      E ∈ ({∅, {0}, {1}, {3}, {1, 3}} : Finset (Finset (Fin 4)))
```

## Worked examples of the text

(`PaperExamples.lean`, lines 115-117)

```lean
theorem repetition_single_average_fidelity (i : Fin 3) :
    ((2:ℝ) ^ (3 - Module.finrank Bit (rowSpace rowsR)) * erasureScore (rowSpace rowsR) {i} + 1) /
      ((2:ℝ) ^ (3 - Module.finrank Bit (rowSpace rowsR)) + 1) = 2 / 3
```

(`PaperExamples.lean`, lines 161-171)

```lean
theorem bell_good_counts :
    (univ.filter (fun z : Pauli 2 => z ∈ normalizer (symplectic 2) (rowSpace rowsBell) ∧
        Good (symplectic 2) (rowSpace rowsBell) (supported univ) z)).card =
      (univ.filter (fun z : Pauli 2 => z ∈ normalizer (symplectic 2) (rowSpace rowsBell))).card ∧
    (univ.filter (fun z : Pauli 2 => z ∈ normalizer (symplectic 2) (rowSpace rowsBell))).card = 4 ∧
    (univ.filter (fun z : Pauli 2 =>
        Good (symplectic 2) (rowSpace rowsBell) (supported univ) z)).card = 4 ∧
    Fintype.card (Pauli 2) = 16 ∧
    ((univ.filter (fun z : Pauli 2 =>
        Good (symplectic 2) (rowSpace rowsBell) (supported univ) z)).card : ℚ) /
      Fintype.card (Pauli 2) = 1 / 4
```

(`PaperExamples.lean`, lines 295-299)

```lean
theorem bell4_witnesses_E13 (z : Pauli 4)
    (hz : Bad (symplectic 4) (rowSpace rowsBell4) (supported E13) z) :
    (univ.filter (fun x : Pauli 4 =>
      x ∈ localized (symplectic 4) (rowSpace rowsBell4) (supported E13) ∧
        symplectic 4 x z = 1)).card = 2
```

(`PaperExamples.lean`, lines 307-311)

```lean
theorem bell4_witnesses_E34 (z : Pauli 4)
    (hz : Bad (symplectic 4) (rowSpace rowsBell4) (supported E34) z) :
    (univ.filter (fun x : Pauli 4 =>
      x ∈ localized (symplectic 4) (rowSpace rowsBell4) (supported E34) ∧
        symplectic 4 x z = 1)).card = 8
```

(`PaperExamples.lean`, lines 407-413)

```lean
theorem xor_physical (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    1 - entanglementFidelity (liftBare.erasureFlagDecoder.comp
        (liftBare.iidLatentErasure (LatentEncoding.circuitMap xorProgram) p hp hp1)).map =
      (3 / 2) * p * (1 - p) ∧
    ∀ Q : Channel (ErasureFlagOutput 1) liftBare.LogicalIndex,
      1 - (3 / 2) * p * (1 - p) ≥ entanglementFidelity
        (Q.comp (liftBare.iidLatentErasure (LatentEncoding.circuitMap xorProgram) p hp hp1)).map
```

(`PaperExamples.lean`, lines 503-504)

```lean
theorem pad_hess_posDef (s t : ℝ) (h : s ≠ 0 ∨ t ≠ 0) :
    0 < hessForm (blockVec s t) (blockVec s t)
```

(`PaperExamples.lean`, lines 524-525)

```lean
theorem pad_not_logConcave :
    ¬ ConcaveOn ℝ {y : Fin 8 → ℝ | ∀ i, 0 < y i} (fun y => Real.log (pairPoly y))
```

## Distance, tail bounds and the sampling section

(`DistanceWeight.lean`, lines 87-91)

```lean
theorem isDistance_iff_minWeight (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (d : ℕ) :
    IsDistance S d ↔
      (∃ x ∈ normalizer (symplectic n) S, x ∉ S ∧ pauliWeight x = d) ∧
        ∀ x ∈ normalizer (symplectic n) S, x ∉ S → d ≤ pauliWeight x
```

(`PaperExamples.lean`, lines 83-91)

```lean
theorem tail_bound {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ d / 2 ≤ infidelity S p ∧
    infidelity S p ≤ uncorrectableProb S p ∧
    uncorrectableProb S p ≤
      ∑ E ∈ univ.filter (fun E : Finset (Fin n) => d ≤ E.card), causeMass p E ∧
    ∑ E ∈ univ.filter (fun E : Finset (Fin n) => d ≤ E.card), causeMass p E =
      ∑ j ∈ Finset.Ico d (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)
```

(`SamplingBounds.lean`, lines 73-76)

```lean
theorem binomial_tail_chernoff (n d : ℕ) {p α : ℝ} (hp : 0 < p) (hpα : p < α) (hα1 : α ≤ 1)
    (hd : α * n ≤ d) :
    ∑ j ∈ Ico d (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) ≤
      exp (-(n * kl α p))
```

(`SamplingBounds.lean`, lines 154-157)

```lean
theorem infidelity_exponential {n : ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ QecReliability.normalizer (symplectic n) S) {d : ℕ} (hd : IsDistance S d)
    {p α : ℝ} (hp : 0 < p) (hpα : p < α) (hα1 : α ≤ 1) (hαd : α * n ≤ d) :
    p ^ n / 2 ≤ infidelity S p ∧ infidelity S p ≤ exp (-(n * kl α p))
```

(`SamplingBounds.lean`, lines 240-242)

```lean
theorem sample_size {θ δ : ℝ} {M : ℕ} (hθ0 : 0 < θ) (hθ : θ ≤ 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (h : (1 - θ) ^ M ≤ δ) :
    log (1/δ) / (-log (1 - θ)) ≤ M ∧ log (1/δ) / (2 * θ) ≤ log (1/δ) / (-log (1 - θ))
```

## Sampling section, last remark: averaging the exact rank values

(`RankSampling.lean`, lines 31-32)

```lean
def patternWeight (p : ℝ) {M : ℕ} (x : Fin M → Finset (Fin n)) : ℝ :=
  ∏ i, causeMass p (x i)
```

(`RankSampling.lean`, lines 46-47)

```lean
def rankMean (S : Submodule Bit (Pauli n)) {M : ℕ} (x : Fin M → Finset (Fin n)) : ℝ :=
  (∑ i, infidelityScore S (x i)) / M
```

(`RankSampling.lean`, lines 75-78)

```lean
theorem allCorrectable_prob (S : Submodule Bit (Pauli n)) (p : ℝ) (M : ℕ) :
    ∑ x : Fin M → Finset (Fin n),
        patternWeight p x * (if ∀ i, uncorrectable S (x i) = 0 then 1 else 0) =
      (1 - uncorrectableProb S p) ^ M
```

(`RankSampling.lean`, lines 104-108)

```lean
theorem failure_prob_ge (S : Submodule Bit (Pauli n)) {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hθ : 0 < infidelity S p) (hε : ε < 1) (M : ℕ) :
    (1 - uncorrectableProb S p) ^ M ≤ ∑ x : Fin M → Finset (Fin n),
      patternWeight p x *
        (if ε * infidelity S p < |rankMean S x - infidelity S p| then 1 else 0)
```

(`RankSampling.lean`, lines 127-134)

```lean
theorem rank_sample_size (S : Submodule Bit (Pauli n)) {p ε δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hθ : 0 < infidelity S p) (hq : uncorrectableProb S p ≤ 1/2) (hε : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (M : ℕ)
    (hfail : ∑ x : Fin M → Finset (Fin n),
      patternWeight p x *
        (if ε * infidelity S p < |rankMean S x - infidelity S p| then 1 else 0) ≤ δ) :
    log (1/δ) / (2 * uncorrectableProb S p) ≤ M ∧
      log (1/δ) / (4 * infidelity S p) ≤ log (1/δ) / (2 * uncorrectableProb S p)
```

# 6. Computed section

## Identities behind the hybrid estimator of the computed section

(`HybridEstimator.lean`, lines 60-63)

```lean
theorem ambiguity_add_ambiguity_compl (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (E : Finset (Fin n)) :
    ambiguity (symplectic n) S (supported E) + ambiguity (symplectic n) S (supported Eᶜ) =
      2 * (n - finrank Bit S)
```

(`HybridEstimator.lean`, lines 126-132)

```lean
theorem layerAverage_erasureScore_dual (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (j : Fin (n + 1)) :
    layerAverage (id : Causes n → Finset (Fin n)) (erasureScore S) j =
      ((4:ℝ) ^ (n - finrank Bit S))⁻¹ *
        layerAverage (id : Causes n → Finset (Fin n))
          (fun E => (2:ℝ) ^ ambiguity (symplectic n) S (supported E))
          ⟨n - j.val, by omega⟩
```

(`HybridEstimator.lean`, lines 141-143)

```lean
def IsMinimalUncorrectable (S : Submodule Bit (Pauli n)) (M : Finset (Fin n)) : Prop :=
  0 < ambiguity (symplectic n) S (supported M) ∧
    ∀ M' ⊂ M, ¬ 0 < ambiguity (symplectic n) S (supported M')
```

(`HybridEstimator.lean`, lines 146-148)

```lean
theorem exists_minimalUncorrectable_subset (S : Submodule Bit (Pauli n))
    (E : Finset (Fin n)) (hE : 0 < ambiguity (symplectic n) S (supported E)) :
    ∃ M ⊆ E, IsMinimalUncorrectable S M
```

(`HybridEstimator.lean`, lines 162-167)

```lean
theorem uncorrectable_iff_exists_mins (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    (E : Finset (Fin n)) (hE : E.card ≤ w) :
    0 < ambiguity (symplectic n) S (supported E) ↔ ∃ M ∈ mins, M ⊆ E
```

(`HybridEstimator.lean`, lines 178-182)

```lean
theorem sum_union_eq_karpLuby {α : Type*} [DecidableEq α] (terms layer : Finset (Finset α))
    (g : Finset α → ℝ) :
    ∑ E ∈ layer.filter (fun E => ∃ M ∈ terms, M ⊆ E), g E =
      ∑ M ∈ terms, ∑ E ∈ layer.filter (fun E => M ⊆ E),
        g E / ((terms.filter (fun M' => M' ⊆ E)).card : ℝ)
```

(`HybridEstimator.lean`, lines 243-251)

```lean
theorem layer_sum_infidelityScore_eq_karpLuby (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {j : ℕ} (hj : j ≤ w) :
    ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = j), infidelityScore S E =
      ∑ M ∈ mins, ∑ E ∈ (Finset.univ.filter (fun E : Finset (Fin n) => E.card = j)).filter
          (fun E => M ⊆ E),
        infidelityScore S E / ((mins.filter (fun M' => M' ⊆ E)).card : ℝ)
```

(`HybridEstimator.lean`, lines 254-262)

```lean
theorem layer_sum_uncorrectable_eq_karpLuby (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {j : ℕ} (hj : j ≤ w) :
    ∑ E ∈ Finset.univ.filter (fun E : Finset (Fin n) => E.card = j), uncorrectable S E =
      ∑ M ∈ mins, ∑ E ∈ (Finset.univ.filter (fun E : Finset (Fin n) => E.card = j)).filter
          (fun E => M ⊆ E),
        uncorrectable S E / ((mins.filter (fun M' => M' ⊆ E)).card : ℝ)
```

(`HybridEstimator.lean`, lines 268-270)

```lean
theorem bernsteinCurve_rel_of_coeff {b c : Fin (n + 1) → ℝ} {ε : ℝ}
    (hc : ∀ j, |c j - b j| ≤ ε * b j) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |bernsteinCurve n c p - bernsteinCurve n b p| ≤ ε * bernsteinCurve n b p
```

### Symmetry reduction of the minimal-set search, and the split estimator

(`HybridSymmetry.lean`, lines 35-41)

```lean
def permute (σ : Equiv.Perm (Fin n)) : Pauli n ≃ₗ[Bit] Pauli n where
  toFun x := (fun i => x.1 (σ.symm i), fun i => x.2 (σ.symm i))
  invFun x := (fun i => x.1 (σ i), fun i => x.2 (σ i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Prod.ext (funext fun i => by simp) (funext fun i => by simp)
  right_inv x := Prod.ext (funext fun i => by simp) (funext fun i => by simp)
```

(`HybridSymmetry.lean`, lines 56-57)

```lean
def permuteSub (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n)) : Submodule Bit (Pauli n) :=
  S.map (permute σ : Pauli n →ₗ[Bit] Pauli n)
```

(`HybridSymmetry.lean`, lines 127-130)

```lean
theorem ambiguity_map_of_preserved (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n))
    (hσ : permuteSub σ S = S) (E : Finset (Fin n)) :
    ambiguity (symplectic n) S (supported (E.map σ.toEmbedding)) =
      ambiguity (symplectic n) S (supported E)
```

(`HybridSymmetry.lean`, lines 151-153)

```lean
theorem isMinimalUncorrectable_map (σ : Equiv.Perm (Fin n)) (S : Submodule Bit (Pauli n))
    (hσ : permuteSub σ S = S) {M : Finset (Fin n)} (hM : IsMinimalUncorrectable S M) :
    IsMinimalUncorrectable S (M.map σ.toEmbedding)
```

(`HybridSymmetry.lean`, lines 175-180)

```lean
theorem minimal_eq_image_through_representative (S : Submodule Bit (Pauli n))
    (G : Subgroup (Equiv.Perm (Fin n))) (hG : ∀ σ ∈ G, permuteSub σ S = S)
    (reps : Finset (Fin n)) (hreps : ∀ i : Fin n, ∃ σ ∈ G, σ i ∈ reps)
    {M : Finset (Fin n)} (hM : IsMinimalUncorrectable S M) :
    ∃ σ ∈ G, ∃ M' : Finset (Fin n), IsMinimalUncorrectable S M' ∧ M'.card = M.card ∧
      (∃ q ∈ reps, q ∈ M') ∧ M'.map σ.toEmbedding = M
```

(`HybridSymmetry.lean`, lines 201-206)

```lean
theorem sum_eq_karpLuby_add_remainder {α : Type*} [DecidableEq α]
    (terms layer : Finset (Finset α)) (g : Finset α → ℝ) :
    ∑ E ∈ layer, g E =
      (∑ M ∈ terms, ∑ E ∈ layer.filter (fun E => M ⊆ E),
        g E / ((terms.filter (fun M' => M' ⊆ E)).card : ℝ)) +
      ∑ E ∈ layer.filter (fun E => ¬ ∃ M ∈ terms, M ⊆ E), g E
```

(`HybridSymmetry.lean`, lines 211-215)

```lean
theorem remainder_minimal_card (S : Submodule Bit (Pauli n)) (w : ℕ)
    (mins : Finset (Finset (Fin n)))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {E : Finset (Fin n)} (hE : ¬ ∃ M ∈ mins, M ⊆ E)
    {M : Finset (Fin n)} (hM : IsMinimalUncorrectable S M) (hME : M ⊆ E) : w < M.card
```

(`HybridSymmetry.lean`, lines 221-225)

```lean
theorem remainder_correctable (S : Submodule Bit (Pauli n)) (w : ℕ)
    (mins : Finset (Finset (Fin n)))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {E : Finset (Fin n)} (hE : ¬ ∃ M ∈ mins, M ⊆ E) (hcard : E.card ≤ w) :
    ambiguity (symplectic n) S (supported E) = 0
```

These are identities about exact quantities. The sampling errors of the estimators and the answers of the SAT solver are not formalized.

## The completeness formula of the computed section

(`CompletenessFormula.lean`, lines 751-757)

```lean
theorem certFormula_unsat {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L : ℕ)
    (mins : List (List (Fin n))) (units : List (Fin n × Bool))
    (h : (certFormula rows L mins units).Unsat) :
    ∀ E : Finset (Fin n), E.card ≤ L → (∀ u ∈ units, (u.1 ∈ E ↔ u.2 = true)) →
      0 < ambiguity (symplectic n) (rowSpace rows) (supported E) →
        ∃ M ∈ mins, M.toFinset ⊆ E
```

(`CompletenessFormula.lean`, lines 768-775)

```lean
theorem certFormula_checked {n : ℕ} (rows : List (List (PauliCoord n)))
    (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L : ℕ)
    (mins : List (List (Fin n))) (units : List (Fin n × Bool))
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (h : Std.Tactic.BVDecide.LRAT.check proof (certFormula rows L mins units) = true) :
    ∀ E : Finset (Fin n), E.card ≤ L → (∀ u ∈ units, (u.1 ∈ E ↔ u.2 = true)) →
      0 < ambiguity (symplectic n) (rowSpace rows) (supported E) →
        ∃ M ∈ mins, M.toFinset ⊆ E
```

`tools/lrat/CertifyList.lean` builds `certFormula` from an instance file, writes its DIMACS form, and checks an LRAT refutation against the formula it built with `Std.Tactic.BVDecide.LRAT.check`; `experiments/erasure/certify.py --lean` drives it.

## Verified combiner for the certificates of the computed section

(`ListCertificate.lean`, lines 1005-1011)

```lean
theorem symmetric_certificate {n : ℕ} (rows : List (List (PauliCoord n))) (L d : ℕ)
    (mins : Array (List (Fin n))) (xs : Array (List (PauliCoord n))) (zi : Array ℕ)
    (logs : Array (List (PauliCoord n))) (gens : Array (Fin n → Fin n)) (imgs : Array (Array ℕ))
    (words : Array (List ℕ)) (leaves : List (Fin n × List (List (Fin n × Bool))))
    (h : symCheckB rows L d mins xs zi logs gens imgs words leaves = true)
    (hunsat : ∀ p ∈ leaves, ∀ u ∈ p.2, (certFormula rows L mins.toList ((p.1, true) :: u)).Unsat) :
    Certified rows L d mins.toList
```

(`ListCertificate.lean`, lines 1020-1025)

```lean
theorem plain_certificate {n : ℕ} (rows : List (List (PauliCoord n))) (L d : ℕ)
    (mins : Array (List (Fin n))) (xs : Array (List (PauliCoord n))) (zi : Array ℕ)
    (logs : Array (List (PauliCoord n))) (leaves : List (List (Fin n × Bool)))
    (h : plainCheckB rows L d mins xs zi logs leaves = true)
    (hunsat : ∀ u ∈ leaves, (certFormula rows L mins.toList u).Unsat) :
    Certified rows L d mins.toList
```

`tools/lrat/CertifyCode.lean` evaluates the Boolean checks in the hypotheses of these two theorems on a certificate bundle (code, list, symmetry generators, case split, one checked LRAT refutation per case); `experiments/erasure/certify_code.py` drives it and writes `results/certificate_CODE.json`.

## Union (Karp-Luby-Madras) estimator: mean and second moment

(`UnionEstimator.lean`, lines 123-126)

```lean
theorem mean_sample (terms layer : Finset (Finset α)) (g : Finset α → ℝ)
    (hP : (pairs terms layer).Nonempty) :
    (∑ x ∈ pairs terms layer, sample terms layer g x) / ((pairs terms layer).card : ℝ) =
      unionSum terms layer g
```

(`UnionEstimator.lean`, lines 152-158)

```lean
theorem second_moment_le (terms layer : Finset (Finset α)) (g : Finset α → ℝ)
    {gmin gmax νmax : ℝ} (hgmin : 0 < gmin)
    (hg : ∀ E ∈ unionLayer terms layer, gmin ≤ g E ∧ g E ≤ gmax)
    (hν : ∀ E ∈ unionLayer terms layer, (nu terms E : ℝ) ≤ νmax)
    (hP : (pairs terms layer).Nonempty) :
    (∑ x ∈ pairs terms layer, sample terms layer g x ^ 2) / ((pairs terms layer).card : ℝ) ≤
      νmax * (gmax / gmin) * unionSum terms layer g ^ 2
```

(`UnionEstimator.lean`, lines 210-217)

```lean
theorem variance_le (terms layer : Finset (Finset α)) (g : Finset α → ℝ)
    {gmin gmax νmax : ℝ} (hgmin : 0 < gmin)
    (hg : ∀ E ∈ unionLayer terms layer, gmin ≤ g E ∧ g E ≤ gmax)
    (hν : ∀ E ∈ unionLayer terms layer, (nu terms E : ℝ) ≤ νmax)
    (hP : (pairs terms layer).Nonempty) :
    (∑ x ∈ pairs terms layer, (sample terms layer g x - unionSum terms layer g) ^ 2) /
        ((pairs terms layer).card : ℝ) ≤
      (νmax * (gmax / gmin) - 1) * unionSum terms layer g ^ 2
```

(`UnionEstimator.lean`, lines 263-279)

```lean
theorem stabilizer_union_estimator (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (symplectic n) S) (w : ℕ) (mins : Finset (Finset (Fin n)))
    (hunc : ∀ M ∈ mins, 0 < ambiguity (symplectic n) S (supported M))
    (hcover : ∀ M, IsMinimalUncorrectable S M → M.card ≤ w → M ∈ mins)
    {j : ℕ} (hj : j ≤ w) {νmax : ℝ}
    (hν : ∀ E ∈ unionLayer mins (univ.filter (fun E : Finset (Fin n) => E.card = j)),
      (nu mins E : ℝ) ≤ νmax)
    (hP : (pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j))).Nonempty) :
    (∑ x ∈ pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j)),
        sample mins (univ.filter (fun E : Finset (Fin n) => E.card = j)) (infidelityScore S) x) /
        ((pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j))).card : ℝ) =
      ∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j), infidelityScore S E ∧
    (∑ x ∈ pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j)),
        sample mins (univ.filter (fun E : Finset (Fin n) => E.card = j)) (infidelityScore S) x ^ 2) /
        ((pairs mins (univ.filter (fun E : Finset (Fin n) => E.card = j))).card : ℝ) ≤
      2 * νmax * (∑ E ∈ univ.filter (fun E : Finset (Fin n) => E.card = j),
        infidelityScore S E) ^ 2
```

## Verified exhaustive table

(`ExactTable.lean`, lines 440-441)

```lean
def fRat (rows : List (List (PauliCoord n))) (j : ℕ) : ℚ :=
  (scoreNat rows j : ℚ) / (2 ^ (2 * n) * (n.choose j : ℚ))
```

(`ExactTable.lean`, lines 448-450)

```lean
theorem fRat_spec (rows : List (List (PauliCoord n))) (j : Fin (n + 1)) :
    (fRat rows j.val : ℝ) =
      layerAverage (id : Causes n → Finset (Fin n)) (erasureScore (rowSpace rows)) j
```

(`ExactTable.lean`, lines 457-458)

```lean
theorem uRat_spec (rows : List (List (PauliCoord n))) (j : Fin (n + 1)) :
    (uRat rows j.val : ℝ) = Uncorrectable.layerFraction (rowSpace rows) j
```

`tools/exact/ExactTable.lean` evaluates `fRat` and `uRat` and prints the table; `experiments/erasure/exact_lean.py` compares it with the Python enumeration.
