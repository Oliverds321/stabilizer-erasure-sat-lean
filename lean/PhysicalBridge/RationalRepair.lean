import PhysicalBridge.BoundedRatios

/-! Exact rational endpoint replacement and repair of a previously prepared
cache. Endpoints are computed once by the rank algorithm. The vector builder
uses recursive prefixMinimum minima; no linear-time scan bound is asserted. -/
namespace QecReliability.RationalOutput
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open QecPhysical.Stabilizer

def endpointEntry {r : ℕ} (a ell : Ratio) (T : CoefficientTable r) (j : ℕ) : Ratio :=
  if j=0 then a else if j=r then ell else
    let i : Fin (r+1) := ⟨min j r,Nat.lt_succ_of_le (min_le_right _ _)⟩
    Ratio.counts (T.good.get i).1 (T.bad.get i).1

theorem endpointEntry_value {r : ℕ} (a ell : Ratio) (T : CoefficientTable r) (j : ℕ) :
    (endpointEntry a ell T j).value=endpointInput a.value ell.value T.ratio j := by
  unfold endpointEntry endpointInput
  split_ifs <;> try rfl
  rw [Ratio.counts_value]
  rfl

structure Vector (r : ℕ) where
  entries : Array Ratio
  length_eq : entries.size=r+1

namespace Vector
def get {r : ℕ} (v : Vector r) (j : Fin (r+1)) : Ratio :=
  v.entries[j.val]'(by rw [v.length_eq]; exact j.isLt)

def build {r : ℕ} (f : Fin (r+1) → Ratio) : Vector r := ⟨Array.ofFn f,by simp⟩

@[simp] theorem get_build {r : ℕ} (f : Fin (r+1) → Ratio) (j : Fin (r+1)) :
    (build f).get j=f j := by simp [get,build]

noncomputable def curve {r : ℕ} (v : Vector r) : ℝ → ℝ :=
  bernsteinCurve r (fun j => (v.get j).value)

def evaluate {r : ℕ} (v : Vector r) (u d : ℕ) : ℕ × ℕ :=
  evaluateRationalCurve (fun j => (v.get j).num) (fun j => (v.get j).den) u d

theorem evaluate_correct {r u d : ℕ} (v : Vector r) (hud : u≤d) (hd : 0<d) :
    ((v.evaluate u d).1:ℝ)/(v.evaluate u d).2=v.curve ((u:ℝ)/d) :=
  evaluateRationalCurve_semantics _ _ (fun j => (v.get j).den_pos) hud hd

theorem evaluate_valid {r u d : ℕ} (v : Vector r) (hud : u≤d) (hd : 0<d) :
    0<(v.evaluate u d).2 ∧ (v.evaluate u d).1≤(v.evaluate u d).2 :=
  ⟨evaluateRationalCurve_den_pos _ _ (fun j => (v.get j).den_pos) hd,
    evaluateRationalCurve_num_le_den _ _ (fun j => (v.get j).den_pos)
      (fun j => (v.get j).num_le_den) hud hd⟩

def payload {r : ℕ} (v : Vector r) : ℕ := (v.entries.toList.map Ratio.payload).sum
end Vector

def endpointVector {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) : Vector r :=
  let a := Ratio.dyadic rows (circuitMap C ∅)
  let ell := Ratio.dyadic rows (circuitMap C Finset.univ)
  Vector.build (fun j => endpointEntry a ell T j.val)

def shapeVector {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) : Vector r :=
  let a := Ratio.dyadic rows (circuitMap C ∅)
  let ell := Ratio.dyadic rows (circuitMap C Finset.univ)
  let e := endpointEntry a ell T
  Vector.build (fun j => Ratio.greater ell (Ratio.prefixMinimum e j.val))

theorem endpointVector_curve {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) :
    (endpointVector rows C T).curve=cachedEndpointCurve (rowSpace rows) (circuitMap C) T := by
  funext p
  unfold Vector.curve cachedEndpointCurve
  congr 1
  funext j
  simp only [endpointVector,Vector.get_build,endpointEntry_value,Ratio.dyadic_value]

theorem shapeVector_curve {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) :
    (shapeVector rows C T).curve=cachedShapeCurve (rowSpace rows) (circuitMap C) T := by
  funext p
  unfold Vector.curve cachedShapeCurve
  congr 1
  funext j
  simp only [shapeVector,Vector.get_build,Ratio.greater_value,Ratio.prefixMinimum_value,
    endpointEntry_value,Ratio.dyadic_value,repaired]

theorem endpointVector_evaluate {n r u d : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) (hud : u≤d) (hd : 0<d) :
    (((endpointVector rows C T).evaluate u d).1:ℝ)/((endpointVector rows C T).evaluate u d).2=
      cachedEndpointCurve (rowSpace rows) (circuitMap C) T ((u:ℝ)/d) := by
  rw [Vector.evaluate_correct _ hud hd,endpointVector_curve]

theorem shapeVector_evaluate {n r u d : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (T : CoefficientTable r) (hud : u≤d) (hd : 0<d) :
    (((shapeVector rows C T).evaluate u d).1:ℝ)/((shapeVector rows C T).evaluate u d).2=
      cachedShapeCurve (rowSpace rows) (circuitMap C) T ((u:ℝ)/d) := by
  rw [Vector.evaluate_correct _ hud hd,shapeVector_curve]

end QecReliability.RationalOutput
