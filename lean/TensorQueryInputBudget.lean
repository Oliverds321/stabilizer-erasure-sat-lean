import TensorArgumentMagnitude
import TensorRuntimeQueryBounds

/-! Fixed-factory input envelopes for the actual multiclass query compiler.
The bound includes table lookup, seed slicing, hash construction, CNF
construction, serialization, and the complete serialized output. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.QueryResources
open FL Trans.Query.Bound Trans.BoundsQH Trans.BoundsRest
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  (density : ℕ) (i : TensorQuery.FLCompiler.Indices) (compilerIdx : ℕ)

/-- One polynomial bounds each actual query call, with no residual compiler,
hash-constructor, grid-lookup, or argument-magnitude assumption. -/
theorem compiler_budget : ∃ P : PolynomialEnvelope, ∀ {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (a b c d : ℕ), 0<a → 0<c →
    ∀ (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) (rationalRepetitionBudget (2*slots ds) c d)) → Bool)
      (key : RequestKey),
    ValidKey (keySize n ds.sum) (slots ds-1) (rationalRepetitionBudget (2*slots ds) c d) key →
    let p := (ContextFL.externalData (data hD hd A).base (data hD hd A).den ds rows C
        (List.ofFn coins),Trans.Control.encKey key)
    let L := Boundary.resourceSize rows C a b c d
    (compiler hD hd A density i compilerIdx).cost p ≤ P.eval L ∧
    (compiler hD hd A density i compilerIdx).depth p ≤ P.eval L ∧
    (compiler hD hd A density i compilerIdx).msize p ≤ P.eval L ∧
    mag (.list .bool) ((compiler hD hd A density i compilerIdx).den p) ≤ P.eval L ∧
    (Ty.enc (.list .bool) ((compiler hD hd A density i compilerIdx).den p)).size ≤ P.eval L := by
  obtain ⟨Pa,ha⟩ := argument_bound hD hd A
  obtain ⟨k,c,h⟩ := compiler_bounds hD hd A density i compilerIdx
  have hg : Assembly.PolyBounded (fun L => G k c (Pa.eval L)) :=
    G_comp_pb k c (by poly_bounded)
  have hp : Assembly.PolyBounded (fun L => 5*G k c (Pa.eval L)+1) := by poly_bounded
  obtain ⟨P,hP⟩ := hp.envelope
  refine ⟨P,?_⟩
  intro n ds rows C a b c' d hapos hc coins key hk
  have hm := ha rows C a b c' d hapos hc coins key hk
  obtain ⟨hcost,hdepth,hspace,hmag,hsize⟩ := h _ _ hm
  have hb := hP (Boundary.resourceSize rows C a b c' d)
  dsimp only
  exact ⟨by omega,by omega,by omega,by omega,hsize.trans hb⟩

end QecReliability.TensorMachine.QueryResources
