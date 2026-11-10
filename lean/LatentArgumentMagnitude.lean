import LatentCompileBounds
import Final.Init.Bounds

/-! Full compile-argument magnitude in structural extent n+r+encoded input.
Every circuit gate/output occurrence, wire address, row incidence, seed block,
coin bit and valid-key field is charged. Numeric B is absent: confidence costs
enter through the proved bit-precision bound on repetition count. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ArgumentMagnitude
open FL Trans.Wire Trans.Query Trans.Query.Bound
open SharedCircuit SharedCircuit.LatentEncoding
open OracleCost OracleCost.WholeWrapperCandidate
open Trans.BoundsRest

theorem program_magnitude {n r : ℕ} (C : SharedCircuit.Program r n) :
    mag WProg (encProg C) ≤ C.gates*(2*(r+C.gates)+7)+n*(r+C.gates+1)+3 := by
  have hg := ParserFL.circuit_magnitude C.circuit
  have ho := ParserFL.naturals_magnitude (List.ofFn (fun i => (C.output i).val))
    (r+C.gates) (by
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact (C.output i).isLt.le)
  rw [List.length_ofFn] at ho
  change mag (.list ParserFL.GateTy) (encCirc C.circuit) +
    mag (.list .nat) (List.ofFn (fun i => (C.output i).val)) + 1 ≤ _
  omega

theorem argument_magnitude (base den : ℕ) {n r m Q S N : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n) (coins : List Bool)
    (hq : n+r+C.gates ≤ Q) (hrows : rows.length+rowIncidences rows ≤ Q)
    (hseed : seedB base den (keySize n r) ≤ S) (hcoins : coins.length ≤ N)
    (hm : 2*m+1 ≤ 6*Q+5) {key : RequestKey} (hk : ValidKey (keySize n r) r m key) :
    mag (.prod TX Trans.Control.TKey)
      (ContextFL.externalData base den rows C coins,Trans.Control.encKey key) ≤
      10*(Q+2)^2+S+2*N+20*Q+30 := by
  have hr := mag_rows_le rows
  have hp := program_magnitude C
  have hb := mag_bools_le coins
  have hkey := key_mag_le hk
  have hq' : keySize n r ≤ 2*Q := by unfold keySize; omega
  have hrowprod : rowIncidences rows*(n+2) ≤ Q*(Q+2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hgprod : C.gates*(2*(r+C.gates)+7) ≤ Q*(2*Q+7) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hoprod : n*(r+C.gates+1) ≤ Q*(Q+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hrow : mag TRowsW (encRows rows) ≤ Q*(Q+2)+2*Q+1 := by omega
  have hprog : mag WProg (encProg C) ≤ Q*(2*Q+7)+Q*(Q+1)+3 := by omega
  have hcontext : mag TX (ContextFL.externalData base den rows C coins) =
      n+mag TRowsW (encRows rows)+mag WProg (encProg C)+keySize n r+
        seedB base den (keySize n r)+mag (.list .bool) coins+5 := by
    change n+(mag TRowsW (encRows rows)+(mag WProg (encProg C)+
      (keySize n r+(seedB base den (keySize n r)+mag (.list .bool) coins+1)+1)+1)+1)+1 = _
    omega
  change mag TX (ContextFL.externalData base den rows C coins)+mag Trans.Control.TKey
    (Trans.Control.encKey key)+1 ≤ _
  rw [hcontext]
  nlinarith only [hrow,hprog,hb,hkey,hq',hseed,hcoins,hm,hq]

end QecReliability.LatentMachine.ArgumentMagnitude

noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Query.Bound Trans.BoundsQH
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)

/-- One polynomial for the whole actual argument, chosen before n/r/C/precision.
The seed bound is valid also at q=0; no dispatched-Unit seed convention is used. -/
theorem argument_bound : ∃ P : PolynomialEnvelope, ∀ {n r : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program r n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n r)
      (Factory.width hD hd A n r) (rationalRepetitionBudget (2*(r+1)) c d)) → Bool)
      (key : RequestKey), ValidKey (keySize n r) r (rationalRepetitionBudget (2*(r+1)) c d) key →
      mag (.prod TX Trans.Control.TKey)
        (contextData hD hd A rows C (rationalRepetitionBudget (2*(r+1)) c d) coins,
          Trans.Control.encKey key) ≤ P.eval (InputEncoding.paperLength rows C a b c d) := by
  obtain ⟨Ks,Cs,hs⟩ := Final.Init.seed_inst hD hd A
  have hg : Assembly.PolyBounded (fun L => G Ks Cs (2*L)) :=
    Trans.BoundsRest.G_comp_pb Ks Cs (by poly_bounded)
  have hp : Assembly.PolyBounded (fun L =>
      10*(L+2)^2+(2*(6*L+5)+1)*G Ks Cs (2*L)+20*L+30) := by poly_bounded
  obtain ⟨P,hP⟩ := hp.envelope
  refine ⟨P,?_⟩
  intro n r rows C a b c d ha hc coins key hk
  let L := InputEncoding.paperLength rows C a b c d
  obtain ⟨_,hq,_,hm,_⟩ := InputEncoding.budget_parameters rows C a b c d ha hc
  obtain ⟨_,_,hrows,_,_⟩ := InputEncoding.paperLength_components rows C a b c d
  have hstruct := satExtent_le_paperLength rows C a b c d
  have hdim : n+r+C.gates ≤ L := by
    dsimp only [satExtent,circuitExtent] at hstruct
    omega
  have hsval := (hs (keySize n r)).2.2.2
  rw [seedBF_den Install.wL Install.wA Install.paramsFn _ _
    (fun _ => rfl)] at hsval
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
  have hb := ArgumentMagnitude.argument_magnitude (data hD hd A).base (data hD hd A).den
    rows C (List.ofFn coins) hdim hrows hsm hcoins hm hk
  change mag (.prod TX Trans.Control.TKey)
    (ContextFL.externalData _ _ rows C (List.ofFn coins),Trans.Control.encKey key) ≤ _
  have he : 10*(L+2)^2+G Ks Cs (2*L)+2*((6*L+5)*G Ks Cs (2*L))+20*L+30 =
      10*(L+2)^2+(2*(6*L+5)+1)*G Ks Cs (2*L)+20*L+30 := by ring
  rw [he] at hb
  exact hb.trans (hP L)

end QecReliability.LatentMachine.Runtime
