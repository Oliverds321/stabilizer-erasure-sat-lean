import LatentInitializerBudget
import LatentEndpointInputBudget

/-! Fixed-factory discharge and structural-input envelope for the actually
installed initializer. The polynomial includes the entire sampled coin tape,
and applies to r=0 as well as every positive r and physical dimension n. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.InitializerFL
open FL Trans.BoundsQH Trans.BoundsRest OracleCost

def inputExtent (Ks Cs L : ℕ) : ℕ := L+(6*L+5)*G Ks Cs (2*L)

def initPolynomial (Ks Cs Ki Ci Ke Ce L : ℕ) : ℕ :=
  let Q := inputExtent Ks Cs L
  initialBudget Q (G Ks Cs (2*Q)) (G Ki Ci (7*Q+5)) (G Ke Ce (10*(Q+2)^2))

theorem initialBudget_mono {Q Q' S S' I I' E E' : ℕ}
    (hq : Q≤Q') (hs : S≤S') (hi : I≤I') (he : E≤E') :
    initialBudget Q S I E ≤ initialBudget Q' S' I' E' := by
  unfold initialBudget
  gcongr

theorem initPolynomial_pb (Ks Cs Ki Ci Ke Ce : ℕ) :
    Assembly.PolyBounded (initPolynomial Ks Cs Ki Ci Ke Ce) := by
  have g0 : Assembly.PolyBounded (fun L => G Ks Cs (2*L)) := G_comp_pb _ _ (by poly_bounded)
  have hQ : Assembly.PolyBounded (inputExtent Ks Cs) := by unfold inputExtent; poly_bounded
  have g1 : Assembly.PolyBounded (fun L => G Ks Cs (2*inputExtent Ks Cs L)) :=
    G_comp_pb _ _ (by poly_bounded)
  have g2 : Assembly.PolyBounded (fun L => G Ki Ci (7*inputExtent Ks Cs L+5)) :=
    G_comp_pb _ _ (by poly_bounded)
  have g3 : Assembly.PolyBounded (fun L => G Ke Ce (10*(inputExtent Ks Cs L+2)^2)) :=
    G_comp_pb _ _ (by poly_bounded)
  unfold initPolynomial initialBudget
  poly_bounded

end QecReliability.LatentMachine.InitializerFL

noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Query.Bound Trans.BoundsQH
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate
open InitializerFL

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

def initializer := initialF Install.wL Install.wH Install.wP ParserInstalled.indices
  Install.wA Install.yI Install.yR Install.paramsFn (data hD hd A).base (data hD hd A).den
  InitializerInstalled.ctxIdx InitializerInstalled.terminalIdx InitializerInstalled.topIdx

theorem initializer_valid (density : ℕ) : ∀ w, (initializer hD hd A).ValidAt
    (program hD hd A density) w := fun w =>
  Install.ValidAt.extend
    (ControllerInstalled.extends_wrappers (data hD hd A).base (data hD hd A).den density
      (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG))
    (WrappersInstalled.initializer_valid (data hD hd A).base (data hD hd A).den density
      (Trans.HashCallees.encConsts D A) (Install.thePg hD hd A) (Trans.Hash.gNbr actualMGG) w)

/-- No residual seed, circuit evaluator, endpoint or initializer bound premise. -/
theorem initializer_budget : ∃ P : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool),
    let L := InputEncoding.paperLength rows C a b c d
    let w := input rows C a b c d (List.ofFn coins)
    (initializer hD hd A).cost w ≤ P.eval L ∧
    (initializer hD hd A).depth w ≤ P.eval L ∧
    (initializer hD hd A).msize w ≤ P.eval L ∧
    ((Ty.list .bool).enc w).size ≤ P.eval L := by
  obtain ⟨Ks,Cs,hs⟩ := Final.Init.seed_inst hD hd A
  obtain ⟨Ki,Ci,hi⟩ := Final.Init.initF_P Install.yI
  obtain ⟨Ke,Ce,he⟩ := Trans.BoundsRest.endpointF_cdm_P Install.yR
  obtain ⟨P,hP⟩ := (initPolynomial_pb Ks Cs Ki Ci Ke Ce).envelope
  refine ⟨P,?_⟩
  intro n r rows C a b c d ha hc coins
  let L := InputEncoding.paperLength rows C a b c d
  let Q := L+(List.ofFn coins).length
  obtain ⟨_,hq,_,hm,_⟩ := InputEncoding.budget_parameters rows C a b c d ha hc
  have hsval := (hs (keySize n r)).2.2.2
  rw [seedBF_den Install.wL Install.wA Install.paramsFn _ _ (fun _ => rfl)] at hsval
  have hsm : seedB (data hD hd A).base (data hD hd A).den (keySize n r) ≤ G Ks Cs (2*L) :=
    hsval.trans (G_mono le_rfl le_rfl hq)
  have hbits : CodeHash.seedBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) ≤ G Ks Cs (2*L) := by
    rw [← Factory.seed_length hD hd A n r]
    exact hsm
  have hcoins : (List.ofFn coins).length ≤ (6*L+5)*G Ks Cs (2*L) := by
    rw [List.length_ofFn]
    change (2*rationalRepetitionBudget (2*(r+1)) c d+1)*
      CodeHash.seedBits (Factory.length hD hd A n r) (Factory.width hD hd A n r) ≤ _
    exact Nat.mul_le_mul hm hbits
  have hQ : Q ≤ inputExtent Ks Cs L := by dsimp only [Q,inputExtent]; omega
  obtain ⟨b1,b2,b3,b4⟩ := initial_paper_bounds Install.wL Install.wH Install.wP
    ParserInstalled.indices Install.wA Install.yI Install.yR Install.paramsFn
    (data hD hd A).base (data hD hd A).den InitializerInstalled.ctxIdx
    InitializerInstalled.terminalIdx InitializerInstalled.topIdx (fun _ => rfl)
    hs hi he rows C a b c d (List.ofFn coins) ha hc
  have hsq : (Q+2)^2 ≤ (inputExtent Ks Cs L+2)^2 := by
    rw [sq,sq]
    exact Nat.mul_le_mul (Nat.add_le_add_right hQ 2) (Nat.add_le_add_right hQ 2)
  have hB := initialBudget_mono hQ
    (G_mono (k:=Ks) (c:=Cs) le_rfl le_rfl (show 2*Q≤2*inputExtent Ks Cs L by omega))
    (G_mono (k:=Ki) (c:=Ci) le_rfl le_rfl (show 7*Q+5≤7*inputExtent Ks Cs L+5 by omega))
    (G_mono (k:=Ke) (c:=Ce) le_rfl le_rfl
      (Nat.mul_le_mul_left 10 hsq))
  have hp := hP L
  change initialBudget (inputExtent Ks Cs L) _ _ _ ≤ P.eval L at hp
  have htotal := hB.trans hp
  change initialBudget Q _ _ _ ≤ P.eval L at htotal
  dsimp only [Q,L,initializer] at htotal b1 b2 b3 b4 ⊢
  exact ⟨b1.trans htotal,b2.trans htotal,b3.trans htotal,b4.trans htotal⟩

end QecReliability.LatentMachine.Runtime
