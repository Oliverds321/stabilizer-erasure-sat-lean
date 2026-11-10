import LatentArgumentMagnitude

/-! Concrete callback evaluation within structural-input polynomial budgets.
The same envelope bounds argument/value storage, cost and depth for the actual
installed FL program. No macro zero-cost bookkeeping is used. These are FL
evaluation budgets; tape-interpreter overhead is still to be applied. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Query.Bound Trans.BoundsQH
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate OracleCost.StoredCodeHashConfidence

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)

theorem compile_valid : ∀ x, (controller hD hd A density).compile.ValidAt
    (program hD hd A density) x :=
  (ControllerInstalled.library_valid (data hD hd A).base (data hD hd A).den density
    (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG)
    (Install.theHash_ok hD hd A density)).compile

/-- One actual-program execution envelope, chosen before the runtime circuit,
dimensions or precision. Dependence on numerical B never enters this budget. -/
theorem compile_computes : ∃ P : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool)
      (key : RequestKey), ValidKey (keySize n r) r (rationalRepetitionBudget (2*(r+1)) c d) key →
    let m := rationalRepetitionBudget (2*(r+1)) c d
    let L := InputEncoding.paperLength rows C a b c d
    Computes (program hD hd A density) (controller hD hd A density).compile.idx
      ((Ty.prod TX Trans.Control.TKey).enc (contextData hD hd A rows C m coins,Trans.Control.encKey key))
      ((Ty.list Ty.bool).enc (Final.concreteQuery rows C
        (actualCodeHash (Factory.system hD hd A n r)) (Factory.circuits hD hd A n r) m
        (decodeCoins (Factory.length hD hd A n r) (Factory.width hD hd A n r) m coins) density key))
      (P.eval L) (P.eval L) (P.eval L) := by
  obtain ⟨Pm,hm⟩ := argument_bound hD hd A
  obtain ⟨K,C',hb⟩ := compile_bound hD hd A density
  have hpm : Assembly.PolyBounded Pm.eval := by
    unfold PolynomialEnvelope.eval
    poly_bounded
  have hg := Trans.BoundsRest.G_comp_pb K C' hpm
  have hsum : Assembly.PolyBounded (fun L => G K C' (Pm.eval L)+5*Pm.eval L+1) := by
    poly_bounded
  obtain ⟨P,hP⟩ := hsum.envelope
  refine ⟨P,?_⟩
  intro n r rows C a b c d ha hc coins key hk
  let L := InputEncoding.paperLength rows C a b c d
  let m := rationalRepetitionBudget (2*(r+1)) c d
  let y : (Ty.prod TX Trans.Control.TKey).den :=
    (contextData hD hd A rows C m coins,Trans.Control.encKey key)
  have hy := hm rows C a b c d ha hc coins key hk
  change mag (.prod TX Trans.Control.TKey) y ≤ Pm.eval L at hy
  obtain ⟨ht,hdp,hms,_,_⟩ := hb (Pm.eval L) y hy
  have harg := sz_le (.prod TX Trans.Control.TKey) y
  have hdom := hP L
  have hms' : (controller hD hd A density).compile.msize y ≤ P.eval L := by omega
  have harg' : ((Ty.prod TX Trans.Control.TKey).enc y).size ≤ P.eval L := by omega
  obtain ⟨hi,time,depth,htime,hdepth,heval⟩ :=
    (compile_valid hD hd A density y).computes hms' harg'
  have he := compile_agrees hD hd A density rows C m coins key hk
  change (controller hD hd A density).compile.den y = _ at he
  rw [he] at heval
  exact ⟨hi,time,depth,(by change time ≤ P.eval L; omega),
    (by change depth ≤ P.eval L; omega),heval⟩

end QecReliability.LatentMachine.Runtime
