import TensorMachineAuxiliaryBounds
import TensorArgumentMagnitude
import TensorCountingInputBudget
import TensorFactoryResourceBounds

/-! Uniform envelopes for complete encoded tensor controller arguments and
the actual observer/resume/output callbacks. The cell cap is charged by its
binary width inside the context. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachine.Runtime
open FL Trans.Control Trans.Query.Bound
open SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.MultiTape

private theorem argument_polynomial (Pa : PolynomialEnvelope) (factor density : ℕ) :
    Assembly.PolyBounded (fun L => 5*Pa.eval L+
      Boundary.stateBudget factor density L+40*L+100) := by
  have hstate := Boundary.stateBudget_polynomial factor density
  poly_bounded

private theorem external_magnitude_le {TX : Ty} (X : TX.den) (key : TKey.den) (M : ℕ)
    (h : mag (.prod TX TKey) (X,key)≤M) : mag TX X≤M := by
  change mag TX X+mag TKey key+1≤M at h
  omega

private theorem encoded_argument_le {TX : Ty} (X : TX.den) (s : Config)
    (q r B m L M K : ℕ) (hX : mag TX X≤M) (hstate : (Ty.enc TCfg (encCfg s)).size≤K)
    (hq : q≤2*L) (hr : r≤L) (hm : 2*m+1≤6*L+5) (hB : B.size≤8+2*L) :
    (Ty.enc (TArg TX) (encCtx q r B m X,encCfg s)).size≤5*M+K+40*L+100 := by
  have hXS := (size_le_mag TX X).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 5 hX) 1)
  have eq := Enc.nat_size_le q
  have er := Enc.nat_size_le r
  have eb := Enc.nat_size_le B
  have em := Enc.nat_size_le m
  have nq := NatSize.size_le_self q
  have nr := NatSize.size_le_self r
  have nm := NatSize.size_le_self m
  have hcsize : (Ty.enc (TCtx TX) (encCtx q r B m X)).size=
      (Enc.nat q).size+(Enc.nat r).size+(Enc.nat B).size+(Enc.nat m).size+
      (Ty.enc TX X).size+4 := by
    simp only [encCtx,TCtx,Ty.sz_prod,Ty.enc_nat]
    omega
  rw [Trans.Bounds.shape2,hcsize]
  omega

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : Machine kE ΓE ΛE} {Pt Ps : PolynomialEnvelope} {T : ℕ → ℕ}
  (spec : ResourceEncodedSAT E density Pt Ps T requestExtent)

theorem argument_envelope : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool)
      (s : Config),
    Reachable (keySize n ds.sum) (slots ds-1) (rationalCellBudget a b)
      (rationalRepetitionBudget (2*slots ds) c d) false
      (external hD hd A density spec rows C _ coins) s →
    (Ty.enc (TArg ContextFL.TX)
      (encCtx (keySize n ds.sum) (slots ds-1) (rationalCellBudget a b)
        (rationalRepetitionBudget (2*slots ds) c d)
        (contextData hD hd A ds rows C (List.ofFn coins)),encCfg s)).size≤
      P.eval (Boundary.resourceSize rows C a b c d) := by
  obtain ⟨Pa,ha⟩ := QueryResources.argument_bound hD hd A
  have hp := argument_polynomial Pa (data hD hd A).Cfixed density
  obtain ⟨P,hP⟩ := hp.envelope
  refine ⟨P,?_⟩
  intro n ds rows C a b c d hapos hc coins s hs
  let L := Boundary.resourceSize rows C a b c d
  let m := rationalRepetitionBudget (2*slots ds) c d
  let X := contextData hD hd A ds rows C (List.ofFn coins)
  have hkey : ValidKey (keySize n ds.sum) (slots ds-1) m (.base false 0 0) := by
    constructor <;> omega
  have hm := ha rows C a b c d hapos hc coins (.base false 0 0) hkey
  have hX : mag ContextFL.TX X≤Pa.eval L := external_magnitude_le X _ _ hm
  have hstate := Boundary.encoded_state_bound rows C (Factory.system hD hd A n ds).stages
    (Factory.circuits hD hd A n ds) (data hD hd A).Cfixed density spec
    (Factory.gates_all hD hd A n ds) a b c d hapos hc
    (LatentMachine.decodeCoins (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m coins) hs
  obtain ⟨_,hq,hr,hm',hB,_⟩ := Boundary.resource_parameters rows C a b c d hapos hc
  have htotal := encoded_argument_le X s (keySize n ds.sum) (slots ds-1)
    (rationalCellBudget a b) m L (Pa.eval L)
    (Boundary.stateBudget (data hD hd A).Cfixed density L) hX hstate hq hr hm' hB
  exact htotal.trans (hP L)

end QecReliability.TensorMachine.Runtime

namespace QecReliability.TensorMachine.Auxiliary
open FL Trans.Control OracleCost OracleCost.WholeWrapperCandidate

/-- A shared envelope for all auxiliary callbacks, usable also on the final
repaired state once its encoded size has been established. -/
theorem envelopes (S : PolynomialEnvelope) : ∃ P : PolynomialEnvelope,
    ∀ {TX : Ty} (x : Ix TX) (o : Trans.Bounds.OIx) (c : (TCtx TX).den)
      (s : Config) (L : ℕ), (Ty.enc (TArg TX) (c,encCfg s)).size≤S.eval L →
    CallBounds (isInvokeF x) (c,encCfg s) (P.eval L) (P.eval L) (P.eval L) ∧
    CallBounds (isDoneF x) (c,encCfg s) (P.eval L) (P.eval L) (P.eval L) ∧
    CallBounds (queryOfF x) (c,encCfg s) (P.eval L) (P.eval L) (P.eval L) ∧
    (∀ answer, CallBounds (Trans.Bounds.resumeTopF o x) (answer,(c,encCfg s))
      (P.eval L) (P.eval L) (P.eval L)) ∧
    CallBounds (Trans.Bounds.outputF o TX) (c,encCfg s) (P.eval L) (P.eval L) (P.eval L) := by
  have hp : Assembly.PolyBounded (fun L => space (S.eval L)+time (S.eval L)+depth (S.eval L)) := by
    unfold space time depth
    poly_bounded
  obtain ⟨P,hP⟩ := hp.envelope
  refine ⟨P,?_⟩
  intro TX x o c s L hs
  have lift {a b : Ty} (F : FnSig a b) (z : a.den)
      (h : CallBounds F z (space (S.eval L)) (time (S.eval L)) (depth (S.eval L))) :
      CallBounds F z (P.eval L) (P.eval L) (P.eval L) := by
    have hp := hP L
    exact ⟨by have := h.space; omega,by have := h.argument; omega,
      by have := h.time; omega,by have := h.depth; omega⟩
  exact ⟨lift _ _ (isInvoke_bounds x c s _ hs),lift _ _ (isDone_bounds x c s _ hs),
    lift _ _ (query_bounds x c s _ hs),fun answer => lift _ _ (resume_bounds x c s _ hs o answer),
    lift _ _ (output_bounds c s _ hs o)⟩

end QecReliability.TensorMachine.Auxiliary
