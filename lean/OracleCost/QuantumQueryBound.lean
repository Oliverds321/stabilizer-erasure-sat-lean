import OracleCost.QuerySize
import OracleCost.PhysicalConfidence

/-! Concrete serialization sizes discharge the input-size premise of the
external service contract. The supplied hash gate bound remains explicit;
no efficient uniform family is manufactured from that inequality. -/
namespace QecReliability.OracleCost


namespace QuantumService
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput QecPhysical.Stabilizer

variable {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r))

def variableBound (hashGates : ℕ) : ℕ :=
  21*r+8*n+4*rowIncidences rows+C.gates+hashGates+12

def clauseBound (hashGates : ℕ) : ℕ :=
  18*rowIncidences rows+22*n+83*r+4*C.gates+4*hashGates+53

theorem base_dimensions (g : ℕ) (i : CoefficientIndex r) (pre : List Bool) :
    (baseRequest rows C i pre).varCount≤variableBound rows C g ∧
    (baseRequest rows C i pre).formula.length≤clauseBound rows C g := by
  have h := quantumLayer_prefix_size rows C i pre
  change _≤21*r+8*n+4*rowIncidences rows+C.gates+g+12 ∧
    _≤18*rowIncidences rows+22*n+83*r+4*C.gates+4*g+53
  exact ⟨h.2.2.trans (by omega),h.2.1.trans (by omega)⟩

theorem cell_dimensions (g : ℕ) (i : CoefficientIndex r) (s : Fin (keySize n r+1))
    (seed : Ω) (pre : List Bool) (hg : (K.program s seed).gates≤g) :
    (cellRequest rows C H K i s seed pre).varCount≤variableBound rows C g ∧
    (cellRequest rows C H K i s seed pre).formula.length≤clauseBound rows C g := by
  have h := query_size rows C H K i s seed pre
  exact ⟨h.2.2.trans (by unfold variableBound; omega),
    h.2.1.trans (by unfold clauseBound; omega)⟩

theorem encoded_requests (g : ℕ) (hg : ∀ s seed, (K.program s seed).gates≤g) :
    (∀ i pre, (QueryCodec.encode (baseRequest rows C i pre)).length≤
      QueryCodec.sizeBound (variableBound rows C g) (clauseBound rows C g)) ∧
    (∀ i s seed pre, (QueryCodec.encode (cellRequest rows C H K i s seed pre)).length≤
      QueryCodec.sizeBound (variableBound rows C g) (clauseBound rows C g)) := by
  constructor
  · intro i pre
    exact QueryCodec.encode_length_le _ _ _ (base_dimensions rows C g i pre).1
      (base_dimensions rows C g i pre).2
  · intro i s seed pre
    exact QueryCodec.encode_length_le _ _ _ (cell_dimensions rows C H K g i s seed pre (hg s seed)).1
      (cell_dimensions rows C H K g i s seed pre (hg s seed)).2

variable (service : SATService) (factor time space : ℕ → ℕ)
    (hservice : ServiceBound service (fun request => (QueryCodec.encode request).length) factor time space)
    (hfactor : Monotone factor) (htime : Monotone time)

include hservice hfactor htime

theorem concrete_service_bounds (g : ℕ) (hg : ∀ s seed, (K.program s seed).gates≤g) :
    (∀ i, (service.run (baseRequest rows C i [])).time≤
      factor (QueryCodec.sizeBound (variableBound rows C g) (clauseBound rows C g))*
        time (variableBound rows C g)) ∧
    (∀ i s seed pre, (service.run (cellRequest rows C H K i s seed pre)).time≤
      factor (QueryCodec.sizeBound (variableBound rows C g) (clauseBound rows C g))*
        time (variableBound rows C g)) := by
  have he := encoded_requests rows C H K g hg
  constructor
  · intro i
    exact (hservice _).1.trans (Nat.mul_le_mul (hfactor (he.1 i []))
      (htime (base_dimensions rows C g i []).1))
  · intro i s seed pre
    exact (hservice _).1.trans (Nat.mul_le_mul (hfactor (he.2 i s seed pre))
      (htime (cell_dimensions rows C H K g i s seed pre (hg s seed)).1))

/-- The SAT time function occurs linearly. This theorem charges actual service
invocations in the coefficient preparation, not local wrapper transitions. -/
theorem prepare_concrete_oracleTime (B m g : ℕ) (hg : ∀ s seed, (K.program s seed).gates≤g)
    (ω : Fin (2*m+1) → Ω) :
    (prepareMeasured rows C H K service B m ω).oracleTime≤
      2*(r+1)*(2*m+1)*trialCallBound (keySize n r) B*
        factor (QueryCodec.sizeBound (variableBound rows C g) (clauseBound rows C g))*
        time (variableBound rows C g) := by
  have h := concrete_service_bounds rows C H K service factor time space hservice hfactor htime g hg
  have ht := prepareMeasured_time rows C H K service B m _ ω h.1
    (fun i s seed pre _ => h.2 i s seed pre)
  simpa only [Nat.mul_assoc] using ht

omit hservice hfactor htime in
/-- Explicit linear dimensions for the base iid circuit. Empty and redundant
input rows are not silently converted to an input-traversal bound. -/
theorem iid_dimensions {n : ℕ} (rows : List (List (PauliCoord n))) (c h : ℕ)
    (hn : 1≤n) (hw : rowIncidences rows≤c*n) :
    variableBound rows (Program.pure (fun i : Fin n => i)) (h*(3*n))≤(41+4*c+3*h)*n ∧
    clauseBound rows (Program.pure (fun i : Fin n => i)) (h*(3*n))≤(158+18*c+12*h)*n := by
  simp only [variableBound,clauseBound,Program.pure]
  constructor <;> nlinarith

end QuantumService
end QecReliability.OracleCost
