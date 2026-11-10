import LatentArgumentMagnitude
import TensorCountingSpace
import TensorMachineGridSpace
import TensorMachineContextFL
import TensorFactorySeeds

/-! Magnitude of every actual tensor query argument. The degree-list length
and the cached coefficient-table cardinality are explicitly charged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace QecReliability.TensorMachine.ArgumentMagnitude
open FL Trans.Wire Trans.Query Trans.Query.Bound Trans.BoundsQH
open SharedCircuit SharedCircuit.LatentEncoding
open OracleCost OracleCost.WholeWrapperCandidate Trans.BoundsRest

def magnitudeBound (L S N : ℕ) : ℕ :=
  10*(L+2)^2+S+2*N+22*L+35+L*(L*(L+1)+2)

theorem argument_magnitude (base den : ℕ) {n m L S N : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (coins : List Bool) (hn : n≤L) (hr : ds.sum≤L) (hC : C.gates≤L)
    (hrows : rows.length+rowIncidences rows≤L) (hlen : ds.length≤L)
    (hslots : slots ds≤L) (hseed : seedB base den (keySize n ds.sum)≤S)
    (hcoins : coins.length≤N) (hm : 2*m+1≤6*L+5)
    {key : RequestKey} (hk : ValidKey (keySize n ds.sum) (slots ds-1) m key) :
    mag (.prod ContextFL.TX Trans.Control.TKey)
      (ContextFL.externalData base den ds rows C coins,Trans.Control.encKey key) ≤
        magnitudeBound L S N := by
  have hrow := mag_rows_le rows
  have hprog := LatentMachine.ArgumentMagnitude.program_magnitude C
  have hb := mag_bools_le coins
  have hkey := key_mag_le hk
  have hg := GridFL.grid_magnitude_bound ds L L L hr hlen hslots
  have hds := GridFL.natList_mag ds
  have hq : keySize n ds.sum≤3*L := by unfold keySize; omega
  have hp1 : rowIncidences rows*(n+2)≤L*(L+2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hp2 : C.gates*(2*(ds.sum+C.gates)+7)≤L*(4*L+7) :=
    Nat.mul_le_mul hC (by omega)
  have hp3 : n*(ds.sum+C.gates+1)≤L*(2*L+1) :=
    Nat.mul_le_mul hn (by omega)
  have hc : mag Trans.Wire.TX (LatentMachine.ContextFL.externalData base den rows C coins) =
      n+mag TRowsW (encRows rows)+mag WProg (encProg C)+keySize n ds.sum+
        seedB base den (keySize n ds.sum)+mag (.list .bool) coins+5 := by
    change n+(mag TRowsW (encRows rows)+(mag WProg (encProg C)+
      (keySize n ds.sum+(seedB base den (keySize n ds.sum)+
        mag (.list .bool) coins+1)+1)+1)+1)+1 = _
    omega
  change (mag (.list .nat) ds + (mag GridFL.Table (grid ds) +
    mag Trans.Wire.TX (LatentMachine.ContextFL.externalData base den rows C coins)+1)+1)+
    mag Trans.Control.TKey (Trans.Control.encKey key)+1 ≤ _
  rw [hc,hds]
  unfold GridFL.tableMagnitudeBound at hg
  unfold magnitudeBound
  nlinarith only [hrow,hprog,hb,hkey,hg,hq,hp1,hp2,hp3,hn,hr,hC,hrows,
    hlen,hslots,hseed,hcoins,hm,Nat.sub_le (slots ds) 1]

end QecReliability.TensorMachine.ArgumentMagnitude

noncomputable section
namespace QecReliability.TensorMachine.QueryResources
open FL Trans.Wire Trans.Query.Bound Trans.BoundsQH Trans.BoundsRest
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t)

/-- A single polynomial is chosen before the dimensions, degree list, circuit,
accuracy parameters, random tape, and valid query key. -/
theorem argument_bound : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool)
      (key : RequestKey),
    ValidKey (keySize n ds.sum) (slots ds-1) (rationalRepetitionBudget (2*slots ds) c d) key →
    mag (.prod ContextFL.TX Trans.Control.TKey)
      (ContextFL.externalData (data hD hd A).base (data hD hd A).den ds rows C
        (List.ofFn coins),Trans.Control.encKey key) ≤ P.eval (Boundary.resourceSize rows C a b c d) := by
  obtain ⟨Ks,Cs,hs⟩ := Final.Init.seed_inst hD hd A
  have hg : Assembly.PolyBounded (fun L => G Ks Cs (2*L)) :=
    G_comp_pb Ks Cs (by poly_bounded)
  have hp : Assembly.PolyBounded (fun L => ArgumentMagnitude.magnitudeBound L
      (G Ks Cs (2*L)) ((6*L+5)*G Ks Cs (2*L))) := by
    unfold ArgumentMagnitude.magnitudeBound
    poly_bounded
  obtain ⟨P,hP⟩ := hp.envelope
  refine ⟨P,?_⟩
  intro n ds rows C a b c d ha hc coins key hk
  let L := Boundary.resourceSize rows C a b c d
  obtain ⟨hn,hq,_,hm,_,hr,hlen,_,hC⟩ := Boundary.resource_parameters rows C a b c d ha hc
  obtain ⟨_,_,hrows,_,_⟩ := InputEncoding.paperLength_components rows C a b c d
  have hrows' : rows.length+rowIncidences rows≤L := by
    dsimp only [L,Boundary.resourceSize]; omega
  have hslots : slots ds≤L := by dsimp only [L,Boundary.resourceSize]; omega
  have hsval := (hs (keySize n ds.sum)).2.2.2
  rw [seedBF_den Install.wL Install.wA Install.paramsFn _ _ (fun _ => rfl)] at hsval
  have hsm : seedB (data hD hd A).base (data hD hd A).den (keySize n ds.sum)≤G Ks Cs (2*L) :=
    hsval.trans (G_mono le_rfl le_rfl hq)
  have hbits : CodeHash.seedBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds)≤G Ks Cs (2*L) := by
    rw [← Factory.seed_length hD hd A n ds]
    exact hsm
  have hcoins : (List.ofFn coins).length≤(6*L+5)*G Ks Cs (2*L) := by
    rw [List.length_ofFn]
    change (2*rationalRepetitionBudget (2*slots ds) c d+1)*
      CodeHash.seedBits (Factory.length hD hd A n ds) (Factory.width hD hd A n ds)≤_
    exact Nat.mul_le_mul hm hbits
  exact (ArgumentMagnitude.argument_magnitude (data hD hd A).base (data hD hd A).den
    rows C (List.ofFn coins) hn hr hC hrows' hlen hslots hsm hcoins hm hk).trans (hP L)

end QecReliability.TensorMachine.QueryResources
