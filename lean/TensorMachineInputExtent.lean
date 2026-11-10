import TensorMachineInput
import TensorFactoryResourceBounds
import Assembly.Poly

/-! One uniform initializer input extent, including degree headers and the
entire sampled coin tape. No numerical cell budget enters this extent. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.InputExtent
open FL OracleCost OracleCost.WholeWrapperCandidate SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate

private theorem headers_length (ds : List ℕ) :
    (ds.flatMap QueryCodec.natHeader).length≤2*ds.sum+ds.length := by
  induction ds with
  | nil => simp
  | cons r ds ih =>
    have hr := NatSize.size_le_self r
    simp only [List.flatMap_cons,List.length_append,QueryCodec.natHeader_length,
      List.sum_cons,List.length_cons]
    omega

theorem degrees_length (ds : List ℕ) : (degreesBits ds).length≤2*ds.sum+3*ds.length+1 := by
  have hh := headers_length ds
  have hn := NatSize.size_le_self ds.length
  simp only [degreesBits,List.length_append,QueryCodec.natHeader_length]
  omega

def extent (seedFactor L : ℕ) : ℕ := 6*L+1+(6*L+5)*(seedFactor*(2*L+1))

theorem extent_polynomial (seedFactor : ℕ) : Assembly.PolyBounded (extent seedFactor) := by
  unfold extent
  poly_bounded

noncomputable section
variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t)

/-- One polynomial is fixed before all runtime data. The repetition bound is
provided in the shape consumed by the actual context compiler. -/
theorem input_envelope : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool),
    let N := P.eval (Boundary.resourceSize rows C a b c d)
    (input ds rows C a b c d (List.ofFn coins)).length≤N ∧
    n+ds.sum+C.gates≤N ∧ rows.length+rowIncidences rows≤N ∧
    a.size+b.size+c.size+d.size≤N ∧ ds.length≤N ∧ slots ds≤N ∧
    rationalRepetitionBudget (2*slots ds) c d≤3*N+2 := by
  obtain ⟨P,hP⟩ := (extent_polynomial (data hD hd A).Cseed).envelope
  refine ⟨P,?_⟩
  intro n ds rows C a b c d ha hc coins
  let L := Boundary.resourceSize rows C a b c d
  let m := rationalRepetitionBudget (2*slots ds) c d
  obtain ⟨_,hq,_,hm,_,hr,hlen,_,_⟩ := Boundary.resource_parameters rows C a b c d ha hc
  obtain ⟨_,_,hrows,_,hprec⟩ := InputEncoding.paperLength_components rows C a b c d
  have hv := LatentMachine.satExtent_le_paperLength rows C a b c d
  have hdim : n+ds.sum+C.gates≤L := by
    dsimp only [LatentMachine.satExtent,LatentMachine.circuitExtent] at hv
    dsimp only [L,Boundary.resourceSize]
    omega
  have hpaper : InputEncoding.paperLength rows C a b c d≤L := by
    dsimp only [L,Boundary.resourceSize]; omega
  have hslots : slots ds≤L := by dsimp only [L,Boundary.resourceSize]; omega
  have hseed := Factory.seed_all hD hd A n ds
  have hsbound : CodeHash.seedBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds)≤(data hD hd A).Cseed*(2*L+1) :=
    hseed.trans (Nat.mul_le_mul_left _ (by omega))
  have hcoins : (List.ofFn coins).length≤(6*L+5)*((data hD hd A).Cseed*(2*L+1)) := by
    rw [List.length_ofFn]
    change (2*m+1)*CodeHash.seedBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds)≤_
    exact Nat.mul_le_mul hm hsbound
  have hdegrees := degrees_length ds
  have hproblem : (InputEncoding.problemBits rows C a b c d).length≤L := by
    unfold InputEncoding.paperLength at hpaper
    omega
  have hinput : (input ds rows C a b c d (List.ofFn coins)).length≤extent (data hD hd A).Cseed L := by
    rw [input_length]
    unfold extent
    change ds.sum≤L at hr
    change ds.length≤L at hlen
    omega
  have hLN : L≤P.eval L := by
    have hp := hP L
    unfold extent at hp
    omega
  dsimp only
  refine ⟨hinput.trans (hP L),hdim.trans hLN,(hrows.trans hpaper).trans hLN,
    (hprec.trans hpaper).trans hLN,hlen.trans hLN,hslots.trans hLN,?_⟩
  change 2*m+1≤6*L+5 at hm
  change m≤3*P.eval L+2
  omega

end
end QecReliability.TensorMachine.InputExtent
