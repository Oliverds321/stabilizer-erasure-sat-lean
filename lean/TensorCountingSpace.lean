import TensorQueryBoundary
import TensorQuerySize
import WholeWrapperInputBounds
import Trans.Bounds.SizeCfg

/-! Retained-state bounds for the actual tensor counting schedule. The key width
and coefficient count are independent. The resource measure charges the
structural input and the explicit coefficient-table cardinality. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.Boundary
open SharedCircuit TensorCoefficientCounting
open SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))
  (m : ℕ) (ω : Fin (2*m+1) → Ω) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  {resource : SATRequest → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T resource)

theorem query_bound (g : ℕ) (hg : ∀ scale seed, (K.program scale seed).gates ≤ g) :
    QueryBound (keySize n ds.sum) (slots ds-1) m
      (QueryCodec.sizeBound
        (max (TensorQuery.Service.variableBound rows C g)
          (density * TensorQuery.Service.clauseBound rows C g))
        (TensorQuery.Service.clauseBound rows C g))
      (external rows C H K m ω density spec) := by
  intro key valid
  change (query rows C H K m ω density key).length ≤ _
  rw [query_valid rows C H K m ω density key valid]
  cases key with
  | base side j rep =>
    exact TensorQuery.Service.encoded_padded_base rows C density g _ []
  | cell side j rep scale pre =>
    exact TensorQuery.Service.encoded_padded_cell rows C H K density g _ _ _ pre (hg _ _)

theorem endpoint_width (L : ℕ) (hn : n ≤ L) :
    (endpointDenCap (external rows C H K m ω density spec)).size ≤ 2*L+3 := by
  have h0 : (RationalOutput.Ratio.dyadic rows (circuitMap C ∅)).den ≤ 2^(2*n) :=
    Nat.pow_le_pow_right (by decide) (RationalOutput.ambiguityRank_le rows _)
  have h1 : (RationalOutput.Ratio.dyadic rows (circuitMap C Finset.univ)).den ≤ 2^(2*n) :=
    Nat.pow_le_pow_right (by decide) (RationalOutput.ambiguityRank_le rows _)
  have hp : 2^(2*n) ≤ 2^(2*L) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2^(2*L) := pow_pos (by decide) _
  apply Nat.size_le.mpr
  change (RationalOutput.Ratio.dyadic rows (circuitMap C ∅)).den +
    (RationalOutput.Ratio.dyadic rows (circuitMap C Finset.univ)).den + 1 < _
  rw [show 2*L+3 = 2*L+3 from rfl, pow_add]
  norm_num
  omega

theorem represented_bound (B g L N : ℕ)
    (hg : ∀ scale seed, (K.program scale seed).gates ≤ g)
    (hn : n ≤ L) (hq : keySize n ds.sum ≤ 2*L) (hQ : slots ds-1 ≤ L)
    (hm : 2*m+1 ≤ 6*L+5) (hB : B.size ≤ 8+2*L)
    (hrN : ds.sum ≤ N) (hkN : ds.length ≤ N) (hnN : n ≤ N)
    (hrows : rowIncidences rows ≤ N) (hC : C.gates ≤ N) (hgN : g ≤ N)
    {shape : Bool} {s : Config}
    (hs : Reachable (keySize n ds.sum) (slots ds-1) B m shape
      (external rows C H K m ω density spec) s) :
    (representedBits s).length ≤ wrapperBitPolynomial L (TensorQuery.Service.bitBound density N) :=
  reachable_all_words_input_bound hq hQ hm hB
    (endpoint_width rows C H K m ω density spec L hn)
    (query_bound rows C H K m ω density spec g hg)
    (TensorQuery.Service.sizeBound_le_bitBound rows C density g N hrN hkN hnN hrows hC hgN) hs

def resourceSize (a b c d : ℕ) : ℕ :=
  InputEncoding.paperLength rows C a b c d + ds.length + slots ds

/-- Rational accuracy enters the state envelope only through its binary width;
the number of tensor coefficients is explicitly charged by resourceSize. -/
theorem resource_parameters (a b c d : ℕ) (ha : 0<a) (hc : 0<c) :
    let L := resourceSize rows C a b c d
    n ≤ L ∧ keySize n ds.sum ≤ 2*L ∧ slots ds-1 ≤ L ∧
      2*rationalRepetitionBudget (2*slots ds) c d+1 ≤ 6*L+5 ∧
      (rationalCellBudget a b).size ≤ 8+2*L ∧
      ds.sum ≤ L ∧ ds.length ≤ L ∧ rowIncidences rows ≤ L ∧ C.gates ≤ L := by
  obtain ⟨hn,hr,hrows,hC,hprec⟩ := InputEncoding.paperLength_components rows C a b c d
  have hq := InputEncoding.keySize_le_paperLength rows C a b c d
  have hB := rationalCellBudget_size (b := b) ha
  have hrep := rational_trial_count_input_bound (slots ds-1) c d
    (resourceSize rows C a b c d) hc (by unfold resourceSize; omega)
    (by unfold resourceSize; omega)
  rw [slots_pred_succ] at hrep
  dsimp only
  unfold resourceSize at *
  omega

end QecReliability.TensorMachine.Boundary
