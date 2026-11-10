import LatentGateParserBounds
import LatentProgramParserFL

/-! Measured bounds for the actual FL chronological gate-list reader.
Dependent gates are packed only in the proof: runtime storage remains the
plain gate list parsed by `gatesF`, with no function-valued circuit storage.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ParserFL
open FL FL.Lib Trans.Wire SharedCircuit
open Trans.Query Trans.Query.Bound Trans.BoundsRest
open OracleCost.WholeWrapperCandidate.InputEncoding

abbrev PackedGate := Σ v : ℕ, Gate v

def packCircuit {r : ℕ} : {g : ℕ} → Circuit r g → List PackedGate
  | _, .nil => []
  | _, .snoc C gate => packCircuit C ++ [⟨_,gate⟩]

theorem packCircuit_length {r g : ℕ} (C : Circuit r g) : (packCircuit C).length = g := by
  induction C with
  | nil => rfl
  | snoc C gate ih => simp [packCircuit, ih]

theorem packCircuit_bits {r g : ℕ} (C : Circuit r g) :
    (packCircuit C).flatMap (fun p => gateBits p.2) = circuitBits C := by
  induction C with
  | nil => rfl
  | snoc C gate ih => simp [packCircuit, circuitBits, ih]

theorem packCircuit_encoding {r g : ℕ} (C : Circuit r g) :
    (packCircuit C).map (fun p => encGate p.2) = encCirc C := by
  induction C with
  | nil => rfl
  | snoc C gate ih => simp [packCircuit, encCirc, ih]

theorem packCircuit_dimension {r g : ℕ} (C : Circuit r g) :
    ∀ p ∈ packCircuit C, p.1 ≤ r+g := by
  induction C with
  | nil => simp [packCircuit]
  | @snoc g C gate ih =>
    intro p hp
    simp only [packCircuit, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact (ih p hp).trans (by omega)
    · change r+g ≤ r+(g+1)
      omega

theorem gate_magnitude {v : ℕ} (g : Gate v) : mag GateTy (encGate g) ≤ 2*v+6 := by
  cases g <;> simp [GateTy, encGate, Plain.constGate, mag] <;> (try split_ifs) <;> omega

theorem packed_magnitude (xs : List PackedGate) (V : ℕ)
    (hV : ∀ p ∈ xs, p.1 ≤ V) :
    mag (.list GateTy) (xs.map (fun p => encGate p.2)) ≤ xs.length*(2*V+7)+1 := by
  induction xs with
  | nil => simp [mag, magL]
  | cons p xs ih =>
    have hp := gate_magnitude p.2
    have hv := hV p (by simp)
    have ht := ih (fun q hq => hV q (by simp [hq]))
    change mag GateTy (encGate p.2) + 1 + mag (.list GateTy) (xs.map (fun q => encGate q.2)) ≤
      (xs.length+1)*(2*V+7)+1
    nlinarith

theorem circuit_magnitude {r g : ℕ} (C : Circuit r g) :
    mag (.list GateTy) (encCirc C) ≤ g*(2*(r+g)+7)+1 := by
  have h := packed_magnitude (packCircuit C) (r+g) (packCircuit_dimension C)
  simpa only [packCircuit_encoding, packCircuit_length] using h

/-- Cubic time, linear depth, quadratic maximum encoded value size. The
suffix may contain precision and all coins; its full length is charged in Q.
-/
theorem gates_bounds (L : Lib) (h : HIx) (i : Indices) {r g Q : ℕ}
    (C : Circuit r g) (rest : List Bool)
    (hQ : (circuitBits C ++ rest).length ≤ Q) (hV : r+g ≤ Q) :
    (gatesF L h i).cost (g,circuitBits C ++ rest) ≤ 3000*(Q+2)^3 ∧
    (gatesF L h i).depth (g,circuitBits C ++ rest) ≤ 32*Q+120 ∧
    (gatesF L h i).msize (g,circuitBits C ++ rest) ≤ 5000*(Q+2)^2 := by
  have hread : ∀ (p : PackedGate) rest,
      (gateF L h i.gate).den (gateBits p.2 ++ rest) = (encGate p.2, rest) :=
    fun p rest => gateF_gateBits L h i.gate p.2 rest
  have hsource : ((packCircuit C).flatMap (fun p => gateBits p.2) ++ rest).length ≤ Q := by
    simpa only [packCircuit_bits] using hQ
  have hsuf : ∀ j,
      (((packCircuit C).drop j).flatMap (fun p => gateBits p.2) ++ rest).length ≤ Q :=
    fun j => (suffix_flatMap (fun p : PackedGate => gateBits p.2)
      (packCircuit C) rest j).length_le.trans hsource
  obtain ⟨c,d,m⟩ := many_bounds L (gateF L h i.gate) i.gateStep i.gateFold i.gateMany
    (fun p : PackedGate => gateBits p.2) (fun p => encGate p.2) hread
    (packCircuit C) rest (2000*(Q+2)^2) (30*Q+100) (500*Q+500)
    (fun j _ => gate_bounds L h i.gate _ (hsuf j))
  simp only [packCircuit_length, packCircuit_bits, packCircuit_encoding] at c d m
  have hsize := sz_bools (circuitBits C ++ rest)
  have hmag := circuit_magnitude C
  have hg : g ≤ Q := by omega
  have hsquare : (g+1)*(g+1) ≤ (Q+2)^2 := by
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hwork := Nat.mul_le_mul_left (2000*(Q+2)^2+60) hg
  have hmag' : g*(2*(r+g)+7) ≤ Q*(2*Q+7) :=
    Nat.mul_le_mul hg (by omega)
  have hcube : Q*(Q+2)^2 ≤ (Q+2)^3 := (pow_facts Q).2.2.2.1
  change (manyF L (gateF L h i.gate) i.gateStep i.gateFold i.gateMany).cost _ ≤ _ ∧
    (manyF L (gateF L h i.gate) i.gateStep i.gateFold i.gateMany).depth _ ≤ _ ∧
    (manyF L (gateF L h i.gate) i.gateStep i.gateFold i.gateMany).msize _ ≤ _
  refine ⟨?_, by omega, ?_⟩
  · nlinarith
  · nlinarith

end QecReliability.LatentMachine.ParserFL
