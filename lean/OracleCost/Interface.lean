import QecReliability.PrefixCNF
import Mathlib.Tactic.Ring

/-! Oracle boundaries for the total-cost integration.

An oracle invocation is one atomic external service action. Its time and peak
workspace are charged directly, never passed through a polynomial simulation.
Local instruction costs, concrete bit encodings and their implementations must
be derived separately; this interface supplies no wrapper complexity premise.
-/
namespace QecReliability.OracleCost

structure SATRequest where
  varCount : ℕ
  formula : PrefixCNF.Formula varCount
  width : PrefixCNF.Width 3 formula

/-- External SAT service measurements. These do not measure query construction. -/
structure SATReply where
  value : Bool
  time : ℕ
  workspace : ℕ

/-- This is the external exact decision service, not a counting oracle. -/
structure SATService where
  run : SATRequest → SATReply
  correct : ∀ request, (run request).value = true ↔
    ∃ assignment, PrefixCNF.eval request.formula assignment = true

/-- Quantitative hypotheses on the external service alone. The input-bit
measure will be instantiated only after a concrete serialization is proved. -/
def ServiceBound (service : SATService) (inputBits : SATRequest → ℕ)
    (timeFactor timeByVariables spaceByBits : ℕ → ℕ) : Prop :=
  ∀ request,
    (service.run request).time ≤
      timeFactor (inputBits request) * timeByVariables request.varCount ∧
    (service.run request).workspace ≤ spaceByBits (inputBits request)

/-- Separate sequential time from peak live storage. The left-hand storage is
released at a serial boundary; retained buffers must be charged by `reserve`. -/
structure Usage where
  wrapperTime : ℕ
  oracleTime : ℕ
  oracleCalls : ℕ
  peakBits : ℕ
  deriving DecidableEq

def Usage.serial (a b : Usage) : Usage :=
  ⟨a.wrapperTime+b.wrapperTime, a.oracleTime+b.oracleTime,
    a.oracleCalls+b.oracleCalls, max a.peakBits b.peakBits⟩

def Usage.reserve (bits : ℕ) (u : Usage) : Usage :=
  { u with peakBits := bits+u.peakBits }

def Usage.totalTime (u : Usage) : ℕ := u.wrapperTime+u.oracleTime

theorem serial_totalTime (a b : Usage) :
    (a.serial b).totalTime = a.totalTime+b.totalTime := by
  simp only [Usage.serial, Usage.totalTime]
  omega

theorem serial_linear_oracle (a b : Usage) (bound : ℕ)
    (ha : a.oracleTime ≤ a.oracleCalls*bound)
    (hb : b.oracleTime ≤ b.oracleCalls*bound) :
    (a.serial b).oracleTime ≤ (a.serial b).oracleCalls*bound := by
  dsimp only [Usage.serial]
  calc
    a.oracleTime+b.oracleTime ≤ a.oracleCalls*bound+b.oracleCalls*bound := Nat.add_le_add ha hb
    _ = (a.oracleCalls+b.oracleCalls)*bound := by ring

theorem totalTime_linear_oracle (u : Usage) (bound : ℕ)
    (h : u.oracleTime ≤ u.oracleCalls*bound) :
    u.totalTime ≤ u.wrapperTime+u.oracleCalls*bound :=
  Nat.add_le_add_left h u.wrapperTime

theorem serial_peak (a b : Usage) (cap : ℕ)
    (ha : a.peakBits ≤ cap) (hb : b.peakBits ≤ cap) :
    (a.serial b).peakBits ≤ cap := max_le ha hb

theorem reserve_peak (u : Usage) (retained cap : ℕ) (h : u.peakBits ≤ cap) :
    (u.reserve retained).peakBits ≤ retained+cap := Nat.add_le_add_left h retained

end QecReliability.OracleCost
