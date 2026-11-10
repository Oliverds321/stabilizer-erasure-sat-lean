import LatentContextInputSize
import LatentResourceRuntime
import LatentFactoryResourceBounds
import Trans.Bounds.SizeCfg
import WholeWrapperInputBounds

/-! Actual false-mode reachable FL state storage, on the SAT-bearing branch.
The context is charged by the concrete initializer; configuration words use
the generic proved representation invariant with the actual resource service
and fixed-factory circuit gate bound. The r=0 terminal initializer is separate. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
  {E : MultiTape.Machine kE ΓE ΛE} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
  {resource : SATRequest → ℕ} (spec : ResourceEncodedSAT E density PtE PsE T resource)

/-- Uniform in every reachable state, not merely a successful terminal run.
Numerical B enters only through the representation theorem's bit-size bound. -/
theorem resource_state_size_bound : ∃ P : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c → 0<r →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool)
      (s : Config),
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    Reachable (keySize n r) r (rationalCellBudget a b) m false
      (resourceExternal hD hd A density spec rows C m coins) s →
    ((TArg TX).enc
      (encCtx (keySize n r) r (rationalCellBudget a b) m
        (contextData hD hd A rows C m coins),encCfg s)).size ≤ P.eval L := by
  obtain ⟨Pc,hPc⟩ := context_size_bound hD hd A
  have hp : Assembly.PolyBounded Pc.eval := by unfold PolynomialEnvelope.eval; poly_bounded
  have hrp : Assembly.PolyBounded
      (InputEncoding.retainedPolynomial (gateConstant hD hd A) density) := by
    change Assembly.PolyBounded (fun L => InputEncoding.retainedPolynomial (gateConstant hD hd A) density L)
    simp only [InputEncoding.retainedPolynomial_expansion]
    poly_bounded
  have hsum : Assembly.PolyBounded (fun L => Pc.eval L+
      10*InputEncoding.retainedPolynomial (gateConstant hD hd A) density L+401) := by
    poly_bounded
  obtain ⟨P,hP⟩ := hsum.envelope
  refine ⟨P,?_⟩
  intro n r rows C a b c d ha hc hr coins s
  dsimp only
  intro hs
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let L := InputEncoding.paperLength rows C a b c d
  have hb := Final.Resource.concreteExternal_boundary rows C
    (actualCodeHash (Factory.system hD hd A n r)) (Factory.circuits hD hd A n r) m
    (decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins) density spec
  have hrep := InputEncoding.reachable_input_representation rows C
    (actualCodeHash (Factory.system hD hd A n r)) (Factory.circuits hD hd A n r) spec.service
    a b c d ha hc
    (decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins)
    (gateConstant hD hd A) density false
    (resourceExternal hD hd A density spec rows C m coins) hb
    (Factory.gates_of_latent_positive hD hd A hr) hs
  have hcfg := Trans.Bounds.sz_encCfg_le s
  have hctx := hPc rows C a b c d ha hc coins
  have hdom := hP L
  change ((Ty.prod (TCtx TX) TCfg).enc
    (encCtx (keySize n r) r (rationalCellBudget a b) m
      (contextData hD hd A rows C m coins),encCfg s)).size ≤ P.eval L
  rw [Ty.sz_prod (TCtx TX) TCfg]
  dsimp only [L,m] at *
  omega

end QecReliability.LatentMachine.Runtime
