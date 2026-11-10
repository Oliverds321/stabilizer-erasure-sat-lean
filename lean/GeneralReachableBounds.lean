import TensorRepairFLFullBounds
import GeneralInstalled
import TensorMachineArgumentEnvelope
import TensorRepairFLInputParts

/-! A single polynomial envelope for the installed GENERAL callback at every
reachable counting state, including the encoded size of the repaired output. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachine.GeneralResources
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Control
open Trans.Query.Bound Trans.BoundsQH Trans.BoundsRest
open RepairFL GeneralRepairFL RepairResources OracleCost OracleCost.WholeWrapperCandidate

theorem generalUniformBudget_monoQ (kd cd kc cc kr cr M B N S : ℕ) {q Q : ℕ} (h : q ≤ Q) :
    generalUniformBudget kd cd kc cc kr cr M B N S q ≤
      generalUniformBudget kd cd kc cc kr cr M B N S Q := by
  unfold generalUniformBudget generalCombinedBudget fullAnchorCost anchorTableBudget anchorStepBudget
  gcongr


open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate OracleCost.MultiTape

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent)

set_option maxHeartbeats 2000000 in
theorem callback_envelope : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool)
      (s : Config),
    Reachable (keySize n ds.sum) (slots ds-1) (rationalCellBudget a b)
      (rationalRepetitionBudget (2*slots ds) c d) false
      (Runtime.external hD hd A density spec rows C _ coins) s →
    CallBounds GeneralInstalled.callback
      (Runtime.contextData hD hd A ds rows C (List.ofFn coins),s.goodTable,s.badTable)
      (P.eval (Boundary.resourceSize rows C a b c d))
      (P.eval (Boundary.resourceSize rows C a b c d))
      (P.eval (Boundary.resourceSize rows C a b c d)) ∧
    (TOutput.enc (GeneralInstalled.callback.den
      (Runtime.contextData hD hd A ds rows C (List.ofFn coins),s.goodTable,s.badTable))).size ≤
      P.eval (Boundary.resourceSize rows C a b c d) := by
  obtain ⟨Pm,hm⟩ := QueryResources.argument_bound hD hd A
  obtain ⟨Ps,hs⟩ := Runtime.argument_envelope hD hd A density spec
  obtain ⟨kd,cd,kc,cc,kr,cr,hfull⟩ := general_resources Install.wL GeneralInstalled.ri
    GeneralInstalled.ci Install.yR GeneralInstalled.ai GeneralInstalled.wi GeneralInstalled.gi
  obtain ⟨ko,co,koc,coc,hout⟩ := anchorData_uniform Install.wL FullRepairInstalled.ci
    Install.yR FullRepairInstalled.ai
  have gd : Assembly.PolyBounded (fun L => G kd cd (2*Pm.eval L+1)) :=
    G_comp_pb kd cd (by poly_bounded)
  have gc : Assembly.PolyBounded (fun L => G kc cc (2*Pm.eval L+1)) :=
    G_comp_pb kc cc (by poly_bounded)
  have gr : Assembly.PolyBounded (fun L => G kr cr (2*Pm.eval L+1)) :=
    G_comp_pb kr cr (by poly_bounded)
  have go : Assembly.PolyBounded (fun L => G ko co (2*Pm.eval L+1)) :=
    G_comp_pb ko co (by poly_bounded)
  have hp : Assembly.PolyBounded (fun L =>
      generalUniformBudget kd cd kc cc kr cr (Pm.eval L) (Ps.eval L)
        (Pm.eval L+Ps.eval L) (3*Ps.eval L+10) (Pm.eval L) + 3*Ps.eval L+10 +
      (8*max (2*Ps.eval L+1) (G ko co (2*Pm.eval L+1)+1)+4)*Pm.eval L+1) := by
    unfold generalUniformBudget generalCombinedBudget fullRatioBits fullAnchorCost
      anchorTableBudget anchorStepBudget dyadicBudget countDataBudget countStepBudget
      tableFoldBudget tableStepBudget scanFunctionBudget scanBudget
      scanStepBudget comparisonBitsBudget sndFoldBudget sndBudget
    poly_bounded
  obtain ⟨P,hP⟩ := hp.envelope
  refine ⟨P,?_⟩
  intro n ds rows C a b c d ha hc coins s hreach
  let L := Boundary.resourceSize rows C a b c d
  let X := Runtime.contextData hD hd A ds rows C (List.ofFn coins)
  let m := rationalRepetitionBudget (2*slots ds) c d
  have hkey : ValidKey (keySize n ds.sum) (slots ds-1) m (.base false 0 0) := by
    constructor <;> omega
  have hmag := hm rows C a b c d ha hc coins (.base false 0 0) hkey
  have hX : mag ContextFL.TX X ≤ Pm.eval L := by
    change mag ContextFL.TX X+mag Trans.Control.TKey (encKey (.base false 0 0))+1 ≤ Pm.eval L at hmag
    omega
  obtain ⟨hctx,hkeys,hQ⟩ := callback_structural_parts X (Pm.eval L) hX
  have harg := hs rows C a b c d ha hc coins s hreach
  obtain ⟨hg,hb,hgn,hbn,hinput⟩ := callback_input_parts (keySize n ds.sum) (slots ds-1)
    (rationalCellBudget a b) m X s (Ps.eval L) harg
  have hrun := hfull (Pm.eval L) (Ps.eval L) (Pm.eval L+Ps.eval L) (3*Ps.eval L+10)
    X s.goodTable s.badTable hctx hkeys hg hb
    (hQ.trans (Nat.le_add_right _ _)) (hgn.trans (Nat.le_add_left _ _))
    (hbn.trans (Nat.le_add_left _ _)) hinput
  have hbudget := generalUniformBudget_monoQ kd cd kc cc kr cr (Pm.eval L) (Ps.eval L)
    (Pm.eval L+Ps.eval L) (3*Ps.eval L+10) hQ
  have hpoly := hP L
  have hfinal : generalUniformBudget kd cd kc cc kr cr (Pm.eval L) (Ps.eval L)
      (Pm.eval L+Ps.eval L) (3*Ps.eval L+10) X.2.1.length ≤ P.eval L :=
    hbudget.trans (by omega)
  change CallBounds GeneralInstalled.callback (X,s.goodTable,s.badTable)
    (P.eval L) (P.eval L) (P.eval L) ∧
    (TOutput.enc (GeneralInstalled.callback.den (X,s.goodTable,s.badTable))).size ≤ P.eval L
  constructor
  · exact ⟨hrun.2.2.trans hfinal,hinput.trans (by omega),hrun.1.trans hfinal,hrun.2.1.trans hfinal⟩
  · obtain ⟨_,hab⟩ := hout (Pm.eval L) (externalAnchorCtx X) X.2.1 hctx hkeys
    have hdb := countDataR_bound (Pm.eval L) (Ps.eval L) X.2.1 s.goodTable s.badTable hkeys hg hb
    let B := max (2*Ps.eval L+1) (G ko co (2*Pm.eval L+1)+1)
    have ha' : TableBound (Pm.eval L) B (anchorDataR (externalAnchorCtx X) X.2.1) :=
      tableBound_mono hab le_rfl (Nat.le_max_right _ _)
    have hd' : TableBound (Pm.eval L) B (countDataR X.2.1 s.goodTable s.badTable) :=
      tableBound_mono hdb le_rfl (Nat.le_max_left _ _)
    have hB : 1 ≤ B := by dsimp [B]; omega
    have hsb := substituteR_bound hd' ha'
    have hrb : ∀ z ∈ generalR X s.goodTable s.badTable, RB B z := by
      intro z hz
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz
      exact (hsb e he).2
    have ho := output_encoded_size hrb
    have hlen : (generalR X s.goodTable s.badTable).length = X.2.1.length := by
      simp only [generalR,substituteR,List.length_map,countDataR_length]
    rw [hlen] at ho
    have hsize : (TOutput.enc (generalR X s.goodTable s.badTable)).size ≤ (8*B+4)*Pm.eval L+1 :=
      ho.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hQ) 1)
    change (TOutput.enc ((generalF Install.wL GeneralInstalled.ri GeneralInstalled.ci
      Install.yR GeneralInstalled.ai GeneralInstalled.wi GeneralInstalled.gi).den
        (X,s.goodTable,s.badTable))).size ≤ P.eval L
    rw [generalF_den]
    exact hsize.trans (by dsimp [B]; omega)

end QecReliability.TensorMachine.GeneralResources
