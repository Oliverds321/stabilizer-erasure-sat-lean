import WholeWrapperCacheTrace

/-! Strengthened actual rational-repair loop:
the complete original operation report and untouched raw tables are retained. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate
open RationalOutput

/-- Proof-only scratch normalization. The persistent cache and endpoints are
not erased. No state representation or operational transition is changed. -/
def repairFrame (s : Config) : Config :=
  { s with
    pc := .fetch,repairGood := [],repairBad := [],repairIndex := 0,
    previous := oneRatio,outputRev := [],output := [],pairVisits := 0,
    ratioBuilds := 0,orderComparisons := 0,endpointTests := 0,maxAccumulatorDen := 1 }

theorem repair_framed (q r B m : ℕ) (shape : Bool) (ext : External)
    (gs bs : List Entry) (s : Config) (hpc : s.pc=.repair)
    (hg : s.repairGood=gs) (hb : s.repairBad=bs) (hlen : gs.length=bs.length)
    (hden : s.previous.den≤s.maxAccumulatorDen) :
    ∃ t, LocalTrace q r B m shape ext s (gs.length+1) t ∧ t.pc=.reverseOutput ∧
      let source := RationalOutput.LinearRepair.run shape r s.endpoint0 s.endpoint1
        s.repairIndex s.previous gs bs
      t.outputRev=source.values.reverse++s.outputRev ∧
      t.pairVisits=s.pairVisits+source.pairVisits ∧
      t.ratioBuilds=s.ratioBuilds+source.ratioBuilds ∧
      t.orderComparisons=s.orderComparisons+source.orderComparisons ∧
      t.endpointTests=s.endpointTests+source.endpointTests ∧
      t.maxAccumulatorDen=max s.maxAccumulatorDen source.maxAccumulatorDen ∧
      t.output=[] ∧ repairFrame t=repairFrame s := by
  induction gs generalizing bs s with
  | nil =>
      have hbs : bs=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      cases hbs
      let t : Config := { s with pc := .reverseOutput, output := [] }
      refine ⟨t,LocalTrace.single ?_,rfl,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
      · simp [step,hpc,hg,hb,localEdge,t]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run]
      · simp [t,RationalOutput.LinearRepair.run,max_eq_left hden]
  | cons g gs ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          let e := RationalOutput.LinearRepair.sourceEntry r s.endpoint0 s.endpoint1
            s.repairIndex g b
          let current := if s.repairIndex=0 then e else RationalOutput.Ratio.lesser s.previous e
          let out := if shape then RationalOutput.Ratio.greater s.endpoint1 current else e
          let nxt : Config := { s with
            repairGood := gs, repairBad := bs,
            repairIndex := s.repairIndex+1, previous := current, outputRev := out::s.outputRev,
            pairVisits := s.pairVisits+1,
            ratioBuilds := s.ratioBuilds+(if s.repairIndex=0 ∨ s.repairIndex=r then 0 else 1),
            orderComparisons := s.orderComparisons+(if s.repairIndex=0 then 0 else 1)+(if shape then 1 else 0),
            endpointTests := s.endpointTests+(if s.repairIndex=0 then 1 else 2),
            maxAccumulatorDen := max s.maxAccumulatorDen
              (max s.previous.den (max e.den (max current.den out.den))) }
          have hs : step q r B m shape ext s=localEdge nxt := by
            simp [step,hpc,hg,hb,nxt,e,current,out,localEdge]
          have hd : nxt.previous.den≤nxt.maxAccumulatorDen := by
            dsimp only [nxt]
            exact (le_max_left _ _).trans
              ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
          obtain ⟨t,ht,hpc',hvalues,hvisits,hratios,hcomparisons,htests,hmax,houtput,hframe⟩ :=
            ih bs nxt (by simpa [nxt] using hpc) rfl rfl (by simpa using hlen) hd
          refine ⟨t,?_,hpc',?_,?_,?_,?_,?_,?_,houtput,?_⟩
          · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using LocalTrace.cons hs ht
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,
              List.reverse_cons,List.append_assoc] using hvalues
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using hvisits
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using hratios
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using hcomparisons
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using htests
          · simpa [nxt,RationalOutput.LinearRepair.run,e,current,out,max_assoc,
              max_comm,max_left_comm] using hmax

          · simpa [repairFrame,nxt] using hframe

end QecReliability.OracleCost.WholeWrapperCandidate
