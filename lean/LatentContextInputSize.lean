import LatentInitializerComputes

/-! Retained runtime context storage is charged by the actual initializer
subcomputation. This includes binary B, independent n/r, the entire encoded
circuit/rows, seed-width field and every supplied coin bit. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.InitializerFL
open FL Trans.Wire Trans.Control ParserFL ContextFL

/-- Structural subterm bound before any concrete certificate is substituted. -/
theorem context_msize_le_initial (L : Lib) (h : HIx) (p : PIx) (i : ParserFL.Indices)
    (a : AIx) (y : IxI) (z : IxR)
    (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
    (base den ctxIdx terminalIdx topIdx : ℕ) (w : List Bool) :
    (contextF L a Fp base den ctxIdx).msize ((parseF L h p i).den w) ≤
      (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).msize w := by
  change (contextF L a Fp base den ctxIdx).msize ((parseF L h p i).den w) ≤
    max (max 0 ((parseF L h p i).msize w))
      (max (max 0 ((contextF L a Fp base den ctxIdx).msize ((parseF L h p i).den w))) _)
  exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))

end QecReliability.LatentMachine.InitializerFL

noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate
open InitializerFL ContextFL ParserFL

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

theorem context_size_le_initializer {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (a b c d : ℕ) (coins : List Bool) :
    ((TCtx TX).enc (encCtx (keySize n r) r (rationalCellBudget a b)
      (rationalRepetitionBudget (2*(r+1)) c d)
      (externalData (data hD hd A).base (data hD hd A).den rows C coins))).size ≤
        (initializer hD hd A).msize (input rows C a b c d coins) := by
  have hc := context_result_size Install.wL Install.wA Install.paramsFn
    (data hD hd A).base (data hD hd A).den InitializerInstalled.ctxIdx
    (n,r,Trans.Query.encRows rows,Trans.Query.encProg C,a,b,c,d,coins)
  rw [context_den Install.wL Install.wA Install.paramsFn _ _ _ (fun _ => rfl)] at hc
  have hsub := context_msize_le_initial Install.wL Install.wH Install.wP ParserInstalled.indices
    Install.wA Install.yI Install.yR Install.paramsFn (data hD hd A).base (data hD hd A).den
    InitializerInstalled.ctxIdx InitializerInstalled.terminalIdx InitializerInstalled.topIdx
    (input rows C a b c d coins)
  change (contextF Install.wL Install.wA Install.paramsFn _ _ _).msize
    ((parseF Install.wL Install.wH Install.wP ParserInstalled.indices).den
      (InputEncoding.problemBits rows C a b c d ++ coins)) ≤ _ at hsub
  rw [ParserFL.parseF_problemBits] at hsub
  exact hc.trans hsub

/-- The actual retained context has one fixed structural-input polynomial bound,
not a bound in the numeric cell budget or the endpoint denominator. -/
theorem context_size_bound : ∃ P : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool),
    ((TCtx TX).enc (encCtx (keySize n r) r (rationalCellBudget a b)
      (rationalRepetitionBudget (2*(r+1)) c d)
      (contextData hD hd A rows C (rationalRepetitionBudget (2*(r+1)) c d) coins))).size ≤
        P.eval (InputEncoding.paperLength rows C a b c d) := by
  obtain ⟨P,hP⟩ := initializer_budget hD hd A
  refine ⟨P,?_⟩
  intro n r rows C a b c d ha hc coins
  have hms := (hP rows C a b c d ha hc coins).2.2.1
  exact (context_size_le_initializer hD hd A rows C a b c d (List.ofFn coins)).trans hms

end QecReliability.LatentMachine.Runtime
