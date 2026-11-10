import TensorQueryService

namespace QecReliability.TensorQuery.Service
open SharedCircuit TensorCoefficientCounting OracleCost

theorem padded_dimensions (D : ℕ) (R : SATRequest) (V M : ℕ)
    (hv : R.varCount ≤ V) (hm : R.formula.length ≤ M) :
    (padRequest D R).varCount ≤ max V (D*M) ∧
      (padRequest D R).formula.length ≤ M := by
  constructor
  · change max R.varCount (D*R.formula.length) ≤ max V (D*M)
    exact max_le_max hv (Nat.mul_le_mul_left D hm)
  · simpa only [padRequest,SharedCircuit.length_rename] using hm

variable {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
  (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
  (H : HashStages Ω (Key n ds) (LatentEncoding.keySize n ds.sum))
  (K : SuppliedHashCircuits H (TensorCoefficientCounting.keyBits n ds))

theorem encoded_padded_base (D g : ℕ) (i : Index ds) (pre : List Bool) :
    (QueryCodec.encode (padRequest D (baseRequest rows C i pre))).length ≤
      QueryCodec.sizeBound (max (variableBound rows C g) (D*clauseBound rows C g))
        (clauseBound rows C g) := by
  have h := base_dimensions rows C g i pre
  have hp := padded_dimensions D _ _ _ h.1 h.2
  exact QueryCodec.encode_length_le _ _ _ hp.1 hp.2

theorem encoded_padded_cell (D g : ℕ) (i : Index ds)
    (s : Fin (LatentEncoding.keySize n ds.sum+1)) (ω : Ω) (pre : List Bool)
    (hg : (K.program s ω).gates ≤ g) :
    (QueryCodec.encode (padRequest D (cellRequest rows C H K i s ω pre))).length ≤
      QueryCodec.sizeBound (max (variableBound rows C g) (D*clauseBound rows C g))
        (clauseBound rows C g) := by
  have h := cell_dimensions rows C H K g i s ω pre hg
  have hp := padded_dimensions D _ _ _ h.1 h.2
  exact QueryCodec.encode_length_le _ _ _ hp.1 hp.2

/-- Class count is charged even for zero-degree classes. -/
theorem linear_dimensions (g N : ℕ) (hr : ds.sum ≤ N) (hk : ds.length ≤ N)
    (hn : n ≤ N) (hrows : rowIncidences rows ≤ N) (hC : C.gates ≤ N) (hg : g ≤ N) :
    variableBound rows C g ≤ 46*N+1 ∧ clauseBound rows C g ≤ 178*N+6 := by
  dsimp only [variableBound,clauseBound]
  constructor <;> omega

theorem codec_polynomial (V M : ℕ) :
    QueryCodec.sizeBound V M ≤ 2*V+2*M+2+M*(3*V+5) := by
  have hv := FL.NatSize.size_le_self V
  have hm := FL.NatSize.size_le_self M
  have hprod := Nat.mul_le_mul_left M (show 2+3*(V.size+1) ≤ 3*V+5 by omega)
  unfold QueryCodec.sizeBound
  omega

/-- Explicit coarse polynomial for encoded padded queries when all structural
dimensions are at most N and the SAT density factor D is fixed. -/
def bitBound (D N : ℕ) : ℕ :=
  let V := (46+178*D)*N+6*D+1
  let M := 178*N+6
  2*V+2*M+2+M*(3*V+5)

theorem sizeBound_le_bitBound (D g N : ℕ) (hr : ds.sum ≤ N) (hk : ds.length ≤ N)
    (hn : n ≤ N) (hrows : rowIncidences rows ≤ N) (hC : C.gates ≤ N) (hg : g ≤ N) :
    QueryCodec.sizeBound (max (variableBound rows C g) (D*clauseBound rows C g))
      (clauseBound rows C g) ≤ bitBound D N := by
  have hd := linear_dimensions rows C g N hr hk hn hrows hC hg
  let V := (46+178*D)*N+6*D+1
  let M := 178*N+6
  have hv : max (variableBound rows C g) (D*clauseBound rows C g) ≤ V := by
    apply max_le
    · dsimp [V]; nlinarith
    · have hh := Nat.mul_le_mul_left D hd.2
      dsimp [V]; nlinarith
  have hm : clauseBound rows C g ≤ M := hd.2
  apply (codec_polynomial _ _).trans
  change _ ≤ 2*V+2*M+2+M*(3*V+5)
  have hprod := Nat.mul_le_mul hm (show
    3*max (variableBound rows C g) (D*clauseBound rows C g)+5 ≤ 3*V+5 by omega)
  omega

end QecReliability.TensorQuery.Service
