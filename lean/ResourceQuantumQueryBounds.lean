import OracleCost.QuantumQueryBound
import ResourceSATOracle
import Final.ConcreteExternal
import WholeWrapperInputBounds

/-! Typed dimension-aware caps for the exact generated latent queries. Independent
n and r, arbitrary supplied hash family, original concreteQuery and density padding.
No SAT algorithm, total runtime, or controller reachability hypothesis is used. -/
set_option autoImplicit false
namespace QecReliability.OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open QuantumService

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))

/-- One common cap for padded ambient dimension plus the actual encoded payload. -/
def queryExtentCap (D g : ℕ) : ℕ :=
  engineVariables rows C D g + engineInputBound rows C D g

/-- Both request constructors retain explicit dimensions before serialization. -/
theorem resolveRequest_dimensions (m : ℕ) (ω : Fin (2*m+1) → Ω) (g : ℕ)
    (hg : ∀ scale seed, (K.program scale seed).gates ≤ g)
    (key : RequestKey) (valid : ValidKey (keySize n r) r m key) :
    (resolveRequest rows C H K m ω key valid).varCount ≤ variableBound rows C g ∧
    (resolveRequest rows C H K m ω key valid).formula.length ≤ clauseBound rows C g := by
  cases key with
  | base side j rep =>
      exact base_dimensions rows C g (side, ⟨j, valid.1⟩) []
  | cell side j rep scale pre =>
      exact cell_dimensions rows C H K g (side, ⟨j, valid.1⟩)
        ⟨scale, valid.2.2.1⟩ (ω ⟨rep, valid.2.1⟩) pre (hg _ _)

theorem resolveRequest_padded_extent (m : ℕ) (ω : Fin (2*m+1) → Ω) (D g : ℕ)
    (hg : ∀ scale seed, (K.program scale seed).gates ≤ g)
    (key : RequestKey) (valid : ValidKey (keySize n r) r m key) :
    requestExtent (padRequest D (resolveRequest rows C H K m ω key valid)) ≤
      queryExtentCap rows C D g := by
  have hdim := resolveRequest_dimensions rows C H K m ω g hg key valid
  exact padRequest_extent_le _ _ _ hdim.1 hdim.2

namespace InputEncoding

/-- Fixed explicit quadratic polynomial in the manuscript's faithful paperLength. -/
def queryExtentPolynomial (h D L : ℕ) : ℕ :=
  queryVariableCoeff h D * (L+1) + queryPolynomial h D L

theorem queryExtentCap_input_polynomial (a b c d h D : ℕ) :
    queryExtentCap rows C D (h*keySize n r) ≤
      queryExtentPolynomial h D (paperLength rows C a b c d) :=
  Nat.add_le_add (engine_variables_input_bound rows C a b c d h D)
    (engineInputBound_input_polynomial rows C a b c d h D)

end InputEncoding

/-- Exact typed padded query witness, not merely a binary-length estimate. -/
theorem concreteQuery_extent_witness (m : ℕ) (ω : Fin (2*m+1) → Ω)
    (a b c d h D : ℕ)
    (hg : ∀ scale seed, (K.program scale seed).gates ≤ h*keySize n r)
    (key : RequestKey) (valid : ValidKey (keySize n r) r m key) :
    ∃ q : SATRequest, D*q.formula.length ≤ q.varCount ∧
      Final.concreteQuery rows C H K m ω D key = QueryCodec.encode q ∧
      requestExtent q ≤ InputEncoding.queryExtentPolynomial h D
        (InputEncoding.paperLength rows C a b c d) := by
  refine ⟨padRequest D (resolveRequest rows C H K m ω key valid),
    padRequest_density D _, Final.concreteQuery_valid rows C H K m ω D key valid, ?_⟩
  exact (resolveRequest_padded_extent rows C H K m ω D (h*keySize n r) hg key valid).trans
    (InputEncoding.queryExtentCap_input_polynomial rows C a b c d h D)

/-- Feeds the accepted capped-oracle realization without changing the query bytes. -/
theorem concreteQuery_resource_qok {kE : ℕ} {ΓE ΛE : Type}
    [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE] (E : MultiTape.Machine kE ΓE ΛE)
    (m : ℕ) (ω : Fin (2*m+1) → Ω) (a b c d h D : ℕ)
    (hg : ∀ scale seed, (K.program scale seed).gates ≤ h*keySize n r)
    (key : RequestKey) (valid : ValidKey (keySize n r) r m key) :
    (RegMachine.resourceSatOracle E D requestExtent
      (InputEncoding.queryExtentPolynomial h D (InputEncoding.paperLength rows C a b c d))).qok
      (Final.concreteQuery rows C H K m ω D key) :=
  concreteQuery_extent_witness rows C H K m ω a b c d h D hg key valid

end QecReliability.OracleCost.WholeWrapperCandidate
