import LatentInitializerInputBudget

/-! Exact installed initialization, with separate latent-zero and positive
branches and a discharged polynomial evaluation budget. This is an FL run,
not yet the register/tape interpreter's whole-run guarantee. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

def initialConfiguration {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (m : ℕ) : Config :=
  if r=0 then InitializerFL.terminal (RationalOutput.Ratio.dyadic rows (circuitMap C ∅))
  else initial (keySize n r) r m

def initializedValue {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (a b c d : ℕ) (coins : List Bool) : (TArg TX).den :=
  (encCtx (keySize n r) r (rationalCellBudget a b)
    (rationalRepetitionBudget (2*(r+1)) c d)
    (ContextFL.externalData (data hD hd A).base (data hD hd A).den rows C coins),
   encCfg (initialConfiguration rows C (rationalRepetitionBudget (2*(r+1)) c d)))

theorem initializer_den {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (a b c d : ℕ) (coins : List Bool) :
    (initializer hD hd A).den (input rows C a b c d coins) =
      initializedValue hD hd A rows C a b c d coins := by
  by_cases hr : r=0
  · subst r
    exact InitializerFL.initial_zero Install.wL Install.wH Install.wP ParserInstalled.indices
      Install.wA Install.yI Install.yR Install.paramsFn (data hD hd A).base (data hD hd A).den
      InitializerInstalled.ctxIdx InitializerInstalled.terminalIdx InitializerInstalled.topIdx
      (fun _ => rfl) rows C a b c d coins
  · simpa only [initializer,initializedValue,initialConfiguration,if_neg hr] using
      InitializerFL.initial_pos Install.wL Install.wH Install.wP ParserInstalled.indices
        Install.wA Install.yI Install.yR Install.paramsFn (data hD hd A).base (data hD hd A).den
        InitializerInstalled.ctxIdx InitializerInstalled.terminalIdx InitializerInstalled.topIdx
        (fun _ => rfl) hr rows C a b c d coins

/-- Literal encoded output and measured actual installed initializer execution;
no assumed run-equivalence, seed law or caller-supplied polynomial bound. -/
theorem initializer_computes (density : ℕ) : ∃ P : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool),
    let L := InputEncoding.paperLength rows C a b c d
    Computes (program hD hd A density) (initializer hD hd A).idx
      ((Ty.list .bool).enc (input rows C a b c d (List.ofFn coins)))
      ((TArg TX).enc (initializedValue hD hd A rows C a b c d (List.ofFn coins)))
      (P.eval L) (P.eval L) (P.eval L) := by
  obtain ⟨P,hP⟩ := initializer_budget hD hd A
  refine ⟨P,?_⟩
  intro n r rows C a b c d ha hc coins
  obtain ⟨ht,hdp,hms,hin⟩ := hP rows C a b c d ha hc coins
  obtain ⟨hi,time,depth,htime,hdepth,heval⟩ :=
    (initializer_valid hD hd A density (input rows C a b c d (List.ofFn coins))).computes hms hin
  rw [initializer_den hD hd A rows C a b c d (List.ofFn coins)] at heval
  exact ⟨hi,time,depth,htime.trans ht,hdepth.trans hdp,heval⟩

end QecReliability.LatentMachine.Runtime
