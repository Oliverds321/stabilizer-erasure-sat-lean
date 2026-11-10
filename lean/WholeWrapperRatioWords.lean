import WholeWrapperStoredValues

/-! Every reachable ratio and repair accumulator word is
bounded. Comparison selects existing pairs; it never stores denominator products.
External endpoint denominators are retained explicitly until source fidelity
specializes them. No endpoint runtime/space bound is postulated here. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open RationalOutput

def endpointDenCap (ext : External) : ℕ :=
  (ext.endpoint false).value.den+(ext.endpoint true).value.den+1

def storedRatioCap (P B : ℕ) (ext : External) : ℕ :=
  endpointDenCap ext+2*storedEstimateCap P B+1

structure RatioWords (M : ℕ) (s : Config) : Prop where
  endpoint0 : s.endpoint0.den≤M
  endpoint1 : s.endpoint1.den≤M
  previous : s.previous.den≤M
  maximum : s.maxAccumulatorDen≤M
  outputRev : ∀ x∈s.outputRev, x.den≤M
  output : ∀ x∈s.output, x.den≤M

theorem step_ratio_words {q r B m P : ℕ} {shape : Bool} {ext : External}
    {s : Config} {edge : Edge}
    (hest : EstimateWords (storedEstimateCap P B) s)
    (hs : RatioWords (storedRatioCap P B ext) s)
    (he : step q r B m shape ext s=some edge) :
    RatioWords (storedRatioCap P B ext) edge.next := by
  let M := storedRatioCap P B ext
  have h1 : 1≤M := by unfold M storedRatioCap; omega
  have hep0 : (ext.endpoint false).value.den≤M := by
    unfold M storedRatioCap endpointDenCap; omega
  have hep1 : (ext.endpoint true).value.den≤M := by
    unfold M storedRatioCap endpointDenCap; omega
  have hpair : ∀ g∈s.repairGood, ∀ b∈s.repairBad, g.1+b.1≤M := by
    intro g hg b hb
    have hg' := hest.repairGood g hg
    have hb' := hest.repairBad b hb
    unfold M storedRatioCap
    omega
  have hentry : ∀ g∈s.repairGood, ∀ b∈s.repairBad,
      (LinearRepair.sourceEntry r s.endpoint0 s.endpoint1 s.repairIndex g b).den≤M := by
    intro g hg b hb
    exact LinearRepair.sourceEntry_den_le _ _ _ _ hs.endpoint0 hs.endpoint1 h1
      (hpair g hg b hb)
  have hcurrent : ∀ g∈s.repairGood, ∀ b∈s.repairBad,
      (if s.repairIndex=0 then
        LinearRepair.sourceEntry r s.endpoint0 s.endpoint1 s.repairIndex g b
      else Ratio.lesser s.previous
        (LinearRepair.sourceEntry r s.endpoint0 s.endpoint1 s.repairIndex g b)).den≤M := by
    intro g hg b hb
    split_ifs
    · exact hentry g hg b hb
    · exact Ratio.lesser_den_le hs.previous (hentry g hg b hb)
  have hout : ∀ g∈s.repairGood, ∀ b∈s.repairBad,
      (if shape then Ratio.greater s.endpoint1
        (if s.repairIndex=0 then
          LinearRepair.sourceEntry r s.endpoint0 s.endpoint1 s.repairIndex g b
        else Ratio.lesser s.previous
          (LinearRepair.sourceEntry r s.endpoint0 s.endpoint1 s.repairIndex g b))
      else LinearRepair.sourceEntry r s.endpoint0 s.endpoint1 s.repairIndex g b).den≤M := by
    intro g hg b hb
    cases shape
    · exact hentry g hg b hb
    · exact Ratio.greater_den_le hs.endpoint1 (hcurrent g hg b hb)
  change RatioWords M s at hs
  rcases hs with ⟨he0,he1,hprev,hmax,hrev,houtlist⟩
  change RatioWords M edge.next
  cases hp : s.pc <;> simp only [step,hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge,Option.some.injEq] at he; subst edge)
    | split at he
  all_goals constructor
  all_goals try assumption
  all_goals try dsimp only
  all_goals try simp_all only [List.forall_mem_cons,List.forall_mem_map,
    List.mem_nil_iff,false_implies,true_implies,forall_const,and_true,true_and,and_self,
    Nat.zero_le,Prod.fst,Prod.snd,max_le_iff]
  all_goals first | assumption | (intros; trivial)

/-- This derives denominator preservation from the ACTUAL step together with
proved estimate propagation. The endpoint bound is the concrete pair of values
returned by ext, not a final-state or resource hypothesis. -/
theorem reachable_ratio_words {q r B m : ℕ} {shape : Bool} {ext : External}
    {s : Config} (h : Reachable q r B m shape ext s) :
    RatioWords (storedRatioCap (program q r m).length B ext) s := by
  obtain ⟨totals,events,h⟩ := h
  have all := h.preserves
    (fun s => PrefixTransitions.Valid q (4*B+1) s.prefixState ∧
      EntryCapacity (program q r m).length s ∧
      SelectionCapacity (program q r m).length s ∧
      EstimateWords (storedEstimateCap (program q r m).length B) s ∧
      RatioWords (storedRatioCap (program q r m).length B ext) s)
    (by
      intro s e hs he
      exact ⟨step_prefix_valid hs.1 he,
        step_entry_capacity hs.2.1 he,
        step_selection_capacity hs.2.1 hs.2.2.1 he,
        step_estimate_words hs.1 hs.2.2.1 hs.2.2.2.1 he,
        step_ratio_words hs.2.2.2.1 hs.2.2.2.2 he⟩)
    (by
      refine ⟨initial_prefix_valid q r B m,?_,?_,?_,?_⟩
      · simp [EntryCapacity,entryMass,cellPending,trialPending,initial]
      · constructor <;> simp [initial]
      · constructor <;> simp [initial]
      · constructor <;> simp [initial,oneRatio,storedRatioCap])
  exact all.2.2.2.2

/-- The numerator bound comes from Ratio's proof-erased data invariant. -/
theorem ratio_num_le_cap {M : ℕ} {x : Ratio} (h : x.den≤M) : x.num≤M :=
  x.num_le_den.trans h

open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

/-- Exact dyadic endpoint equality discharges the endpoint-size part. No
extra whole-controller correctness hypothesis is introduced. -/
theorem endpointDenCap_concrete {Ω : Type*} [Fintype Ω] {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (service : SATService)
    (m : ℕ) (ω : Fin (2*m+1) → Ω) (D : ℕ) (ext : External)
    (hboundary : BoundaryCorrect rows C H K service m ω D ext) :
    endpointDenCap ext≤2^(2*n+1)+1 := by
  have h0 : (Ratio.dyadic rows (circuitMap C ∅)).den≤2^(2*n) :=
    Nat.pow_le_pow_right (by decide) (ambiguityRank_le rows _)
  have h1 : (Ratio.dyadic rows (circuitMap C Finset.univ)).den≤2^(2*n) :=
    Nat.pow_le_pow_right (by decide) (ambiguityRank_le rows _)
  unfold endpointDenCap
  rw [hboundary.endpoint0,hboundary.endpoint1,pow_succ]
  omega

end QecReliability.OracleCost.WholeWrapperCandidate
