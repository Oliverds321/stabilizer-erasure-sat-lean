import WholeWrapperAllWords

/-! Binary-width algebra for the complete reachable
profile. No polynomial in epsilon inverse, query count, or SAT runtime appears.
Input-encoding premises are explicit; the actual encoder must discharge them. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate

theorem audit_size_add_bound (x y : ℕ) : (x+y).size≤x.size+y.size+1 := by
  have hx : x<2^(x.size+y.size) := (Nat.lt_size_self x).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hy : y<2^(x.size+y.size) := (Nat.lt_size_self y).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  apply Nat.size_le.mpr
  rw [pow_succ]
  omega

theorem audit_pow_size (P : ℕ) : (2^P).size≤P+1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hpos : 0<2^P := pow_pos (by decide) _
  omega

theorem audit_size_le_value (x : ℕ) : x.size≤x := by
  apply Nat.size_le.mpr
  induction x with
  | zero => norm_num
  | succ x ih =>
      rw [pow_succ]
      have hp : 0<2^x := pow_pos (by decide) _
      omega

theorem storedRatioCap_size (P B : ℕ) (ext : External) :
    (storedRatioCap P B ext).size≤(endpointDenCap ext).size+P+B.size+11 := by
  have hs2 : (2 : ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
  have he := storedEstimateCap_size P B
  have hm := QecReliability.size_mul_bound 2 (storedEstimateCap P B)
  have h1 := audit_size_add_bound (endpointDenCap ext) (2*storedEstimateCap P B)
  have h2 := audit_size_add_bound (endpointDenCap ext+2*storedEstimateCap P B) 1
  norm_num at hm h2
  unfold storedRatioCap
  omega

theorem broadValueBound_size (q r B m : ℕ) (ext : External) :
    let P := (program q r m).length
    (broadValueBound q r B m ext).size≤
      3*P+q+q.size+r.size+(2*m+1).size+P.size+2*(P+1).size+
        2*B.size+(endpointDenCap ext).size+40 := by
  have hs2 : (2 : ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
  have hs20 : (20 : ℕ).size ≤ 5 := Nat.size_le.mpr (by norm_num)
  let P := (program q r m).length
  let R := 2*m+1
  let E := storedEstimateCap P B
  let C := storedCallCap q P
  let M := storedRatioCap P B ext
  have hp := audit_pow_size P
  have he := storedEstimateCap_size P B
  have hc := storedCallCap_size q P
  have hd := storedRatioCap_size P B ext
  have h2p := QecReliability.size_mul_bound 2 P
  have h1 := audit_size_add_bound 20 q
  have h2 := audit_size_add_bound (20+q) r
  have h3 := audit_size_add_bound (20+q+r) R
  have h4 := audit_size_add_bound (20+q+r+R) (2*P)
  have h5 := audit_size_add_bound (20+q+r+R+2*P) (2^P)
  have h6 := audit_size_add_bound (20+q+r+R+2*P+2^P) E
  have h7 := audit_size_add_bound (20+q+r+R+2*P+2^P+E) C
  have h8 := audit_size_add_bound (20+q+r+R+2*P+2^P+E+C) M
  norm_num at h1 h2p
  change (20+q+r+R+2*P+2^P+E+C+M).size≤_
  change _≤3*P+q+q.size+r.size+R.size+P.size+2*(P+1).size+
    2*B.size+(endpointDenCap ext).size+40
  dsimp only [E,C,M] at h6 h7 h8 ⊢
  omega

def wordPolynomial (L : ℕ) : ℕ := 6*codePolynomial L+17*L+66

/-- hd is a boundary-value width fact, NOT a runtime/space contract. Exact
source endpoints below give hd from the input dimension bound. -/
theorem broadValueBound_input_bound (q r B m L : ℕ) (ext : External)
    (hq : q≤2*L) (hr : r≤L) (hR : 2*m+1≤6*L+5)
    (hB : B.size≤8+2*L) (hd : (endpointDenCap ext).size≤2*L+3) :
    (broadValueBound q r B m ext).size≤wordPolynomial L := by
  have h := broadValueBound_size q r B m ext
  have hp := program_length_input_bound q r m L hq hr hR
  have hqs := audit_size_le_value q
  have hrs := audit_size_le_value r
  have hRs := audit_size_le_value (2*m+1)
  have hPs := audit_size_le_value (program q r m).length
  have hP1s := audit_size_le_value ((program q r m).length+1)
  dsimp only at h
  unfold wordPolynomial
  omega

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- This is the missing endpoint word-width substitution, derived from exact
source equality and ambiguityRank≤2n. Endpoint computation workspace remains a
separate machine-lowering obligation. -/
theorem endpointDenCap_input_size {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (m : ℕ) (ω : Fin (2*m+1) → Ω) (D L : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext) (hn : n≤L) :
    (endpointDenCap ext).size≤2*L+3 := by
  have hd := endpointDenCap_concrete rows C H K service m ω D ext hboundary
  apply Nat.size_le.mpr
  have hp : 2^(2*n+1)≤2^(2*L+1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0<2^(2*L+1) := pow_pos (by decide) _
  have hexp : 2^(2*L+3)=4*2^(2*L+1) := by
    rw [show 2*L+3=(2*L+1)+2 by omega,pow_add]
    norm_num
    ring
  rw [hexp]
  omega

/-- Retained representation including ALL words, all list/header cells,
current query, and native prefix stack. Qbuf is a single CURRENT buffer bound,
not a number of calls. The immutable input and peak primitive workspaces must
still be added by the actual machine simulation. -/
def wrapperBitPolynomial (L Qbuf : ℕ) : ℕ :=
  2*(22:ℕ).size+1+22*(2*fieldPolynomial L+1+
    fieldPolynomial L*(2*wordPolynomial L+1))+3*Qbuf+1+prefixPolynomial L

theorem reachable_all_words_input_bound {q r B m L Q Qbuf : ℕ}
    {shape : Bool} {ext : External} {s : Config}
    (hq : q≤2*L) (hr : r≤L) (hR : 2*m+1≤6*L+5)
    (hB : B.size≤8+2*L) (hd : (endpointDenCap ext).size≤2*L+3)
    (hfront : QueryBound q r m Q ext) (hQ : Q≤Qbuf)
    (h : Reachable q r B m shape ext s) :
    (representedBits s).length≤wrapperBitPolynomial L Qbuf := by
  have hb := reachable_representedBits_bound hfront h
  have hf := stateListBound_input_bound q r m L hq hr hR
  have hfs := (audit_size_le_value (stateListBound q r m)).trans hf
  have hw := broadValueBound_input_bound q r B m L ext hq hr hR hB hd
  have hprefix := prefix_bound_input_polynomial q B L hq hB
  have hqs := (audit_size_le_value Q).trans hQ
  have hproduct : stateListBound q r m*(2*(broadValueBound q r B m ext).size+1)≤
      fieldPolynomial L*(2*wordPolynomial L+1) :=
    Nat.mul_le_mul hf (by omega)
  unfold wrapperBitPolynomial
  omega

/-- No primitive QueryBound or endpoint-width hypothesis appears in this
source-facing theorem: exact boundaries discharge both. The remaining scalar
input premises are explicit encoding/budget facts, not resource contracts. -/
theorem reachable_concrete_all_words_input_bound {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) (D g L : ℕ) (shape : Bool) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext)
    (hg : ∀ scale seed, (K.program scale seed).gates≤g)
    (hn : n≤L) (hq : keySize n r≤2*L) (hr : r≤L)
    (hR : 2*m+1≤6*L+5) (hB : B.size≤8+2*L)
    {s : Config} (h : Reachable (keySize n r) r B m shape ext s) :
    (representedBits s).length≤
      wrapperBitPolynomial L (QuantumService.engineInputBound rows C D g) :=
  reachable_all_words_input_bound hq hr hR hB
    (endpointDenCap_input_size rows C H K service m ω D L ext hboundary hn)
    (concrete_query_bound rows C H K service m ω D g ext hboundary hg) le_rfl h

end QecReliability.OracleCost.WholeWrapperCandidate
