import LatentInitializerComputes
import LatentAuxiliaryExecution
import Assembly.Poly

/-! Actual zero-latent FL execution. The output is the exact C(empty) endpoint,
not necessarily one; the entire context and sampled coin tape remain charged. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.InitializerFL
open FL Trans.Wire Trans.Control

/-- Root shape: two let-bindings followed by a pair. The pair's measured
allocation charges the complete returned state, before concrete data substitution. -/
theorem initial_result_size (L : Lib) (h : HIx) (p : PIx) (i : ParserFL.Indices)
    (a : AIx) (y : IxI) (z : IxR)
    (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams)
    (base den ctxIdx terminalIdx topIdx : ℕ) (w : List Bool) :
    (Ty.enc (TArg TX)
      ((initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).den w)).size ≤
      (initialF L h p i a y z Fp base den ctxIdx terminalIdx topIdx).msize w :=
  le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

end QecReliability.LatentMachine.InitializerFL

noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

theorem initialized_size_le_msize {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : SharedCircuit.Program r n) (a b c d : ℕ) (coins : List Bool) :
    (Ty.enc (TArg TX) (initializedValue hD hd A rows C a b c d coins)).size ≤
      (initializer hD hd A).msize (input rows C a b c d coins) := by
  rw [← initializer_den hD hd A rows C a b c d coins]
  exact InitializerFL.initial_result_size _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem computes_enlarge {P : FL.Program} {f m t d m' t' d' : ℕ} {x y : Val}
    (h : Computes P f x y m t d) (hm : m ≤ m') (ht : t ≤ t') (hd : d ≤ d') :
    Computes P f x y m' t' d' := by
  obtain ⟨hx,ct,cd,hct,hcd,he⟩ := h
  exact ⟨hx.trans hm,ct,cd,hct.trans ht,hcd.trans hd,FL.Eval.mono hm he⟩

/-- One fixed polynomial envelope for initialization, terminal test and exact
singleton output. No SAT call, no n=0 assumption, and no discarded random bits. -/
theorem zero_execution (density : ℕ) : ∃ Q : PolynomialEnvelope, ∀ {n : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program 0 n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n 0)
      (Factory.width hD hd A n 0) (rationalRepetitionBudget (2*(0+1)) c d)) → Bool),
    let L := InputEncoding.paperLength rows C a b c d
    let v := Ty.enc (TArg TX) (initializedValue hD hd A rows C a b c d (List.ofFn coins))
    Computes (program hD hd A density) assemblyIndices.init
      (Ty.enc (.list .bool) (input rows C a b c d (List.ofFn coins))) v
      (Q.eval L) (Q.eval L) (Q.eval L) ∧
    v.size ≤ Q.eval L ∧
    Computes (program hD hd A density) assemblyIndices.isDone v (Enc.bool true)
      (Q.eval L) (Q.eval L) (Q.eval L) ∧
    Computes (program hD hd A density) assemblyIndices.output v
      (Assembly.bitsVal (Assembly.ratioWord [RationalOutput.Ratio.dyadic rows (circuitMap C ∅)]))
      (Q.eval L) (Q.eval L) (Q.eval L) := by
  obtain ⟨P,hP⟩ := initializer_budget hD hd A
  have hp : Assembly.PolyBounded P.eval := ⟨P.coefficient,P.degree,fun _ => le_rfl⟩
  have hpoly : Assembly.PolyBounded (fun L => P.eval L + auxiliaryValue (P.eval L) +
      auxiliaryCost (P.eval L) + auxiliaryDepth (P.eval L)) := by
    unfold auxiliaryValue auxiliaryCost auxiliaryDepth
    poly_bounded
  obtain ⟨Q,hQ⟩ := hpoly.envelope
  refine ⟨Q,?_⟩
  intro n rows C a b c d ha hc coins
  let L := InputEncoding.paperLength rows C a b c d
  let S := P.eval L
  have hsum := hQ L
  have h0 : S ≤ Q.eval L := by dsimp only [S]; omega
  have hv : auxiliaryValue S ≤ Q.eval L := by dsimp only [S]; omega
  have ht : auxiliaryCost S ≤ Q.eval L := by dsimp only [S]; omega
  have hd' : auxiliaryDepth S ≤ Q.eval L := by dsimp only [S]; omega
  obtain ⟨hic,hid,him,hia⟩ := hP rows C a b c d ha hc coins
  have hi := (initializer_valid hD hd A density (input rows C a b c d (List.ofFn coins))).computes him hia
  have hi' := computes_enlarge hi h0 (hic.trans h0) (hid.trans h0)
  rw [initializer_den hD hd A rows C a b c d (List.ofFn coins)] at hi'
  have hs := (initialized_size_le_msize hD hd A rows C a b c d (List.ofFn coins)).trans him
  let ctxData := ContextFL.externalData (data hD hd A).base (data hD hd A).den rows C (List.ofFn coins)
  let terminal := InitializerFL.terminal (RationalOutput.Ratio.dyadic rows (circuitMap C ∅))
  have hstop := auxiliary_isDone_computes hD hd A density (keySize n 0) 0
    (rationalCellBudget a b) (rationalRepetitionBudget (2*(0+1)) c d) ctxData terminal S
    (by simp [terminal,InitializerFL.terminal]) hs
  have hout := auxiliary_output_computes hD hd A density (keySize n 0) 0
    (rationalCellBudget a b) (rationalRepetitionBudget (2*(0+1)) c d) ctxData terminal S hs
  exact ⟨hi',hs.trans h0,computes_enlarge hstop hv ht hd',computes_enlarge hout hv ht hd'⟩

end QecReliability.LatentMachine.Runtime
end
