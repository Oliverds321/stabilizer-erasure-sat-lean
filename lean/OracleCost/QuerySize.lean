import OracleCost.QueryCodec
import Mathlib.Tactic.GCongr

/-! Query-size declarations from OracleCost.QuantumQueryBound, isolated from
the quantum-specific bounds for the Lean 4.34 SAT adapter. -/
namespace QecReliability.OracleCost

namespace QueryCodec

def sizeBound (vcount clauses : ℕ) : ℕ :=
  2*vcount.size+2*clauses.size+2+clauses*(2+3*(vcount.size+1))

theorem encode_length_le (request : SATRequest) (V M : ℕ)
    (hv : request.varCount≤V) (hm : request.formula.length≤M) :
    (encode request).length≤sizeBound V M := by
  apply (encode_length request).trans
  unfold sizeBound
  gcongr <;> exact Nat.size_le_size (by assumption)

end QueryCodec

end QecReliability.OracleCost
