import LatentCompileInputBudget
import Trans.BoundsRest.Endpoint

/-! Exact-rank endpoint evaluation has polynomial bit storage even though its
rational denominator can be exponential. Only resource bounds, not the numeric
result magnitude, are transferred through the result-forgetting signature. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.EndpointBounds
open FL FL.Lib FL.Tm Trans.Wire Trans.Control Trans.Query.Bound
open Trans.BoundsQH Trans.BoundsRest

/-- Same actual argument computation, including charged latent-dimension recovery. -/
def resourceBody (L : Lib) (y : IxR) : Tm [.prod TX .bool] .nat :=
  .app (cdmSig (endpointF y)) (.pair (.pair (Xn (.fst v0))
    (.pair (WrappersFL.Xr L (.fst v0)) (.pair (Xrows (.fst v0)) (XC (.fst v0))))) (.snd v0))

theorem endpoint_bound (L : Lib) (c : CIx) (y : IxR) : ∃ K C',
    ∀ w : (Ty.prod TX .bool).den,
      (WrappersFL.endpointWF L c y).cost w ≤ G K C' (mag (.prod TX .bool) w) ∧
      (WrappersFL.endpointWF L c y).depth w ≤ G K C' (mag (.prod TX .bool) w) ∧
      (WrappersFL.endpointWF L c y).msize w ≤ G K C' (mag (.prod TX .bool) w) := by
  obtain ⟨K,C',h⟩ := polyB_bodySig c.endpointW (resourceBody L y)
    (by simp [Tm.CallsP,resourceBody,WrappersFL.Xr,polyB,endpointF_cdm_P])
  refine ⟨K,C',fun w => ?_⟩
  obtain ⟨h1,h2,h3,_⟩ := h w
  exact ⟨h1,h2,h3⟩

end QecReliability.LatentMachine.EndpointBounds

noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Query.Bound Trans.BoundsQH
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)

theorem endpoint_valid : ∀ x, (controller hD hd A density).endpoint.ValidAt
    (program hD hd A density) x :=
  (ControllerInstalled.library_valid (data hD hd A).base (data hD hd A).den density
    (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)
    (Install.theHash_ok hD hd A density)).endpoint

/-- Actual endpoint evaluation, including both endpoint values for arbitrary C,
within one structural input polynomial, uniformly in side and coin contents. -/
theorem endpoint_computes : ∃ P : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool) (side : Bool),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    Computes (program hD hd A density) (controller hD hd A density).endpoint.idx
      ((Ty.prod TX Ty.bool).enc (contextData hD hd A rows C m coins,side))
      (Trans.Control.TR.enc (Trans.Control.toR (Final.concreteEndpoint rows C side).value))
      (P.eval L) (P.eval L) (P.eval L) := by
  obtain ⟨Pm,hm⟩ := argument_bound hD hd A
  obtain ⟨K,C',hb⟩ := EndpointBounds.endpoint_bound Install.wL WrappersInstalled.indices Install.yR
  have hpm : Assembly.PolyBounded Pm.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hg := Trans.BoundsRest.G_comp_pb K C' hpm
  have hsum : Assembly.PolyBounded (fun L => G K C' (Pm.eval L)+5*Pm.eval L+1) := by poly_bounded
  obtain ⟨P,hP⟩ := hsum.envelope
  refine ⟨P,?_⟩
  intro n r rows C a b c d ha hc coins side
  let L := InputEncoding.paperLength rows C a b c d
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let y : (Ty.prod TX Ty.bool).den := (contextData hD hd A rows C m coins,side)
  have hy0 := hm rows C a b c d ha hc coins (.base false 0 0) (by constructor <;> omega)
  have hy : mag (.prod TX .bool) y ≤ Pm.eval L := by
    change mag TX (contextData hD hd A rows C m coins)+8+1 ≤ Pm.eval L at hy0
    change mag TX (contextData hD hd A rows C m coins)+1+1 ≤ Pm.eval L
    omega
  obtain ⟨ht,hdp,hms⟩ := hb y
  have hgrow := G_mono (k:=K) (c:=C') le_rfl le_rfl hy
  change (controller hD hd A density).endpoint.cost y ≤ _ at ht
  change (controller hD hd A density).endpoint.depth y ≤ _ at hdp
  change (controller hD hd A density).endpoint.msize y ≤ _ at hms
  have harg := sz_le (.prod TX .bool) y
  have hdom := hP L
  have hms' : (controller hD hd A density).endpoint.msize y ≤ P.eval L := by omega
  have harg' : ((Ty.prod TX Ty.bool).enc y).size ≤ P.eval L := by omega
  obtain ⟨hi,time,depth,htime,hdepth,heval⟩ :=
    (endpoint_valid hD hd A density y).computes hms' harg'
  have he := endpoint_agrees hD hd A density rows C m coins side
  change (controller hD hd A density).endpoint.den y = _ at he
  rw [he] at heval
  exact ⟨hi,time,depth,(by change time ≤ P.eval L; omega),
    (by change depth ≤ P.eval L; omega),heval⟩

end QecReliability.LatentMachine.Runtime
