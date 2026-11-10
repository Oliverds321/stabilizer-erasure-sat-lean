import TensorMachineInitializerPaper
import TensorMachineInputExtent
import TensorMachineAgreement
import TensorMachineCallbackRuns
import Final.Init.Bounds

/-! Uniform input-sensitive resources for the fixed tensor initializer.
All grid, seed and counting-code callee bounds are discharged here. -/

set_option autoImplicit false
namespace QecReliability.TensorMachine.InitializerFL
open FL Trans.BoundsQH Trans.BoundsRest OracleCost

def initPolynomial (N : PolynomialEnvelope) (Kg Cg Ks Cs Ki Ci L : ℕ) : ℕ :=
  initialBudget (N.eval L) (GridFL.gridBudget Kg Cg (N.eval L))
    (G Ks Cs (2*N.eval L)) (G Ki Ci (7*N.eval L+5))

theorem initPolynomial_polynomial (N : PolynomialEnvelope) (Kg Cg Ks Cs Ki Ci : ℕ) :
    Assembly.PolyBounded (initPolynomial N Kg Cg Ks Cs Ki Ci) := by
  have hn : Assembly.PolyBounded (fun L => N.eval L) := by poly_bounded
  have hg := G_comp_pb Kg Cg (show Assembly.PolyBounded (fun L => 100*(N.eval L+2)^3) by poly_bounded)
  have hb := G_comp_pb 2 300 (show Assembly.PolyBounded (fun L => 100*(N.eval L+2)^3) by poly_bounded)
  have hs := G_comp_pb Ks Cs (show Assembly.PolyBounded (fun L => 2*N.eval L) by poly_bounded)
  have hi := G_comp_pb Ki Ci (show Assembly.PolyBounded (fun L => 7*N.eval L+5) by poly_bounded)
  unfold initPolynomial initialBudget basicBudget GridFL.gridBudget
  poly_bounded

end QecReliability.TensorMachine.InitializerFL

noncomputable section
namespace QecReliability.TensorMachine.Runtime
open FL Trans.Wire Trans.Control Trans.Query.Bound Trans.BoundsQH
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t)

/-- Chosen before every runtime input, the envelope bounds all actual initializer
measures and the complete encoded input. No additional callee bound remains. -/
theorem initializer_budget : ∃ P : PolynomialEnvelope, ∀ (source : FL.Program)
    {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool),
    let L := Boundary.resourceSize rows C a b c d
    let w := input ds rows C a b c d (List.ofFn coins)
    let F := Program.initializer source (data hD hd A).base (data hD hd A).den
    F.cost w≤P.eval L ∧ F.depth w≤P.eval L ∧ F.msize w≤P.eval L ∧
      ((Ty.list .bool).enc w).size≤P.eval L := by
  obtain ⟨Kg,Cg,hg⟩ := GridFL.grid_resources Install.wL Installed.gridIndices
  obtain ⟨Ks,Cs,hs⟩ := Final.Init.seed_inst hD hd A
  obtain ⟨Ki,Ci,hi⟩ := Final.Init.initF_P Install.yI
  obtain ⟨N,hN⟩ := InputExtent.input_envelope hD hd A
  obtain ⟨P,hP⟩ := (InitializerFL.initPolynomial_polynomial N Kg Cg Ks Cs Ki Ci).envelope
  refine ⟨P,?_⟩
  intro source n ds rows C a b c d ha hc coins
  obtain ⟨hw,hdim,hr,hprec,hlen,hslots,hm⟩ := hN rows C a b c d ha hc coins
  obtain ⟨b1,b2,b3,b4⟩ := InitializerFL.initial_paper_bounds source
    (data hD hd A).base (data hD hd A).den hg hs hi rows C a b c d
    (List.ofFn coins) hw hdim hr hprec hlen hslots hm
  have hp := hP (Boundary.resourceSize rows C a b c d)
  change InitializerFL.initialBudget _ _ _ _ ≤ P.eval _ at hp
  exact ⟨b1.trans hp,b2.trans hp,b3.trans hp,b4.trans hp⟩

/-- Numerical `CallBounds` for the actual installed initializer. -/
theorem initializer_call_bounds : ∃ P : PolynomialEnvelope, ∀ (source : FL.Program)
    {n : ℕ} {ds : List ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program ds.sum n) (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool),
    let L := Boundary.resourceSize rows C a b c d
    CallBounds (Program.initializer source (data hD hd A).base (data hD hd A).den)
      (input ds rows C a b c d (List.ofFn coins)) (P.eval L) (P.eval L) (P.eval L) := by
  obtain ⟨P,hP⟩ := initializer_budget hD hd A
  refine ⟨P,?_⟩
  intro source n ds rows C a b c d ha hc coins
  obtain ⟨h1,h2,h3,h4⟩ := hP source rows C a b c d ha hc coins
  exact ⟨h3,h4,h1,h2⟩

end QecReliability.TensorMachine.Runtime
end
