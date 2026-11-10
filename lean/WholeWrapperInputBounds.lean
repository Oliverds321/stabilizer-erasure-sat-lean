import WholeWrapperInputEncoding

/-! Discharge every scalar input-L premise and
the current serialized-query polynomial from the actual represented source.
The structural hash gate constant and fixed SAT padding density are explicit;
no total-runtime or final-space contract is a premise. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate.InputEncoding
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- Actual rational-budget parameter bridge: L is determined by the input,
not quantified with hypotheses saying it is large enough. -/
theorem budget_parameters {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (a b c d : ℕ) (ha : 0<a) (hc : 0<c) :
    let L := paperLength rows C a b c d
    n≤L ∧ keySize n r≤2*L ∧ r≤L ∧
      2*rationalRepetitionBudget (2*(r+1)) c d+1≤6*L+5 ∧
      (rationalCellBudget a b).size≤8+2*L := by
  obtain ⟨hn,hr,hrows,hcircuit,hprecision⟩ := paperLength_components rows C a b c d
  have hq := keySize_le_paperLength rows C a b c d
  have hb := rationalCellBudget_size (b:=b) ha
  have ht := rational_trial_count_input_bound r c d (paperLength rows C a b c d)
    hc hr (by omega)
  exact ⟨hn,hq,hr,ht,by omega⟩

/-- Conservative fixed constants. All terms depend only on h and the fixed
SAT density D; the paper input contributes polynomially through L. -/
def queryVariableCoeff (h D : ℕ) : ℕ := 46+2*h+D*(180+8*h)
def queryClauseCoeff (h : ℕ) : ℕ := 180+8*h

def queryPolynomial (h D L : ℕ) : ℕ :=
  2*(queryVariableCoeff h D*(L+1))+2*(queryClauseCoeff h*(L+1))+2+
    (queryClauseCoeff h*(L+1))*(2+3*(queryVariableCoeff h D*(L+1)+1))

/-- Concrete quantum dimensions use the actual sparse incidences and actual
supplied circuit gate count, both charged by the structural input encoding. -/
theorem concrete_dimensions_input_bound {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n) (a b c d h : ℕ) :
    let L := paperLength rows C a b c d
    QuantumService.variableBound rows C (h*keySize n r)≤(46+2*h)*(L+1) ∧
      QuantumService.clauseBound rows C (h*keySize n r)≤queryClauseCoeff h*(L+1) := by
  obtain ⟨hn,hr,hrows,hcircuit,hprecision⟩ := paperLength_components rows C a b c d
  have hq := keySize_le_paperLength rows C a b c d
  have hh := Nat.mul_le_mul_left h hq
  simp only [QuantumService.variableBound,QuantumService.clauseBound,queryClauseCoeff]
  constructor <;> nlinarith

/-- Padding density is fixed with the external SAT machine. It is not a
precision-dependent value inserted into the represented input length. -/
theorem engine_variables_input_bound {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n) (a b c d h D : ℕ) :
    QuantumService.engineVariables rows C D (h*keySize n r)≤
      queryVariableCoeff h D*(paperLength rows C a b c d+1) := by
  obtain ⟨hv,hm⟩ := concrete_dimensions_input_bound rows C a b c d h
  unfold QuantumService.engineVariables queryVariableCoeff
  apply max_le
  · exact hv.trans (Nat.mul_le_mul_right _ (by omega))
  · calc
      D*QuantumService.clauseBound rows C (h*keySize n r)
          ≤D*(queryClauseCoeff h*(paperLength rows C a b c d+1)) := Nat.mul_le_mul_left D hm
      _=(D*queryClauseCoeff h)*(paperLength rows C a b c d+1) := by ring
      _≤(46+2*h+D*(180+8*h))*(paperLength rows C a b c d+1) :=
        Nat.mul_le_mul_right _ (by unfold queryClauseCoeff; omega)

/-- Full self-delimiting SAT query, INCLUDING headers and binary literal
addresses. No idealized unit-sized literal list replaces its bit encoding. -/
theorem engineInputBound_input_polynomial {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n) (a b c d h D : ℕ) :
    QuantumService.engineInputBound rows C D (h*keySize n r)≤
      queryPolynomial h D (paperLength rows C a b c d) := by
  have hv := engine_variables_input_bound rows C a b c d h D
  have hm := (concrete_dimensions_input_bound rows C a b c d h).2
  have hvs := (audit_size_le_value
    (QuantumService.engineVariables rows C D (h*keySize n r))).trans hv
  have hms := (audit_size_le_value
    (QuantumService.clauseBound rows C (h*keySize n r))).trans hm
  unfold QuantumService.engineInputBound QueryCodec.sizeBound queryPolynomial
  gcongr

/-- A fixed explicit polynomial in the faithful paper input measure. Every
intermediate Config's represented fields are covered. Immutable input itself
and primitive execution workspaces must still be added by physical lowering. -/
def retainedPolynomial (h D L : ℕ) : ℕ :=
  wrapperBitPolynomial L (queryPolynomial h D L)

/-- Literal degree-six polynomial identity. Its coefficients depend only on
fixed hash/padding constants; no B, epsilon inverse, query count, or SAT time
occurs. The tag-size term is an absolute numeric constant. -/
theorem retainedPolynomial_expansion (h D L : ℕ) :
    retainedPolynomial h D L=
      456192*L^6+3041280*L^5+8734176*L^4+14066448*L^3+
      (9*queryVariableCoeff h D*queryClauseCoeff h+13522372)*L^2+
      (18*queryVariableCoeff h D*queryClauseCoeff h+6*queryVariableCoeff h D+
        21*queryClauseCoeff h+7425342)*L+
      9*queryVariableCoeff h D*queryClauseCoeff h+6*queryVariableCoeff h D+
        2*(22:ℕ).size+21*queryClauseCoeff h+1872548 := by
  unfold retainedPolynomial wrapperBitPolynomial fieldPolynomial wordPolynomial
    codePolynomial prefixPolynomial queryPolynomial
  ring

/-- No arbitrary L, scalar encoding bounds, QueryBound, or endpoint-width
premise remains. The gate-linear premise is the structural family theorem
supplied by the fixed all-length hash factory, not a resource contract for the
wrapper. The endpoint and query equalities are primitive boundary fidelity. -/
theorem reachable_input_representation {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (a b c d : ℕ) (ha : 0<a) (hc : 0<c)
    (ω : Fin (2*rationalRepetitionBudget (2*(r+1)) c d+1) → Ω)
    (h D : ℕ) (shape : Bool) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service
      (rationalRepetitionBudget (2*(r+1)) c d) ω D ext)
    (hg : ∀ scale seed, (K.program scale seed).gates≤h*keySize n r)
    {s : Config} (hreach : Reachable (keySize n r) r (rationalCellBudget a b)
      (rationalRepetitionBudget (2*(r+1)) c d) shape ext s) :
    (representedBits s).length≤retainedPolynomial h D (paperLength rows C a b c d) := by
  obtain ⟨hn,hq,hr,hR,hB⟩ := budget_parameters rows C a b c d ha hc
  have hquery := concrete_query_bound rows C H K service
    (rationalRepetitionBudget (2*(r+1)) c d) ω D (h*keySize n r) ext hboundary hg
  have hsize := engineInputBound_input_polynomial rows C a b c d h D
  exact reachable_all_words_input_bound hq hr hR hB
    (endpointDenCap_input_size rows C H K service
      (rationalRepetitionBudget (2*(r+1)) c d) ω D (paperLength rows C a b c d) ext hboundary hn)
    hquery hsize hreach

end QecReliability.OracleCost.WholeWrapperCandidate.InputEncoding
