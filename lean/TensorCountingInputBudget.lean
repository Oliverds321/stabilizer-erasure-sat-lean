import TensorCountingSpace
import Assembly.Poly

/-! One fixed polynomial envelope for all reachable tensor counting states.
The input measure includes Q, never the numerical inverse accuracy budget. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.Boundary
open SharedCircuit TensorCoefficientCounting SharedCircuit.LatentEncoding
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate

def stateBudget (h density L : ℕ) : ℕ :=
  10*wrapperBitPolynomial L (TensorQuery.Service.bitBound density ((2*h+2)*(L+1)))+400

theorem stateBudget_polynomial (h density : ℕ) : Assembly.PolyBounded (stateBudget h density) := by
  unfold stateBudget wrapperBitPolynomial fieldPolynomial wordPolynomial codePolynomial
    prefixPolynomial TensorQuery.Service.bitBound
  dsimp only
  poly_bounded

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))
  (h density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  {resource : SATRequest → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T resource)

theorem encoded_state_bound
    (hg : ∀ scale seed, (K.program scale seed).gates ≤ h*(keySize n ds.sum+1))
    (a b c d : ℕ) (ha : 0<a) (hc : 0<c)
    (ω : Fin (2*rationalRepetitionBudget (2*slots ds) c d+1) → Ω)
    {shape : Bool} {s : Config}
    (hs : Reachable (keySize n ds.sum) (slots ds-1) (rationalCellBudget a b)
      (rationalRepetitionBudget (2*slots ds) c d) shape
        (external rows C H K _ ω density spec) s) :
    (FL.Ty.enc Trans.Control.TCfg (Trans.Control.encCfg s)).size ≤
      stateBudget h density (resourceSize rows C a b c d) := by
  let L := resourceSize rows C a b c d
  let N := (2*h+2)*(L+1)
  obtain ⟨hn,hq,hQ,hm,hB,hr,hk,hrows,hC⟩ := resource_parameters rows C a b c d ha hc
  change n ≤ L at hn
  change keySize n ds.sum ≤ 2*L at hq
  have hLN : L ≤ N := by dsimp only [N]; nlinarith
  have hgN : h*(keySize n ds.sum+1) ≤ N := by dsimp only [N]; nlinarith
  have hb := represented_bound rows C H K _ ω density spec
    (rationalCellBudget a b) (h*(keySize n ds.sum+1)) L N hg hn hq hQ hm hB
    (hr.trans hLN) (hk.trans hLN) (hn.trans hLN) (hrows.trans hLN) (hC.trans hLN) hgN hs
  have he := Trans.Bounds.sz_encCfg_le s
  change _ ≤ 10*wrapperBitPolynomial L (TensorQuery.Service.bitBound density N)+400
  omega

end QecReliability.TensorMachine.Boundary
