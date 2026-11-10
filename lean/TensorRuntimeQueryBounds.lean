import TensorMachineQueryFL
import TensorQueryFLBounds
import Install.Callees

/-! Local time, depth and workspace bounds for the actual tensor query
callback, including cached-grid lookup, seed slicing, hash construction,
multiclass counters, and serialized SAT output. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace QecReliability.TensorMachine.QueryFL
open FL FL.Lib FL.Tm Trans.Wire Trans.Query.Bound Trans.BoundsQH
open Trans.Control (TKey)

/-- The callback's only non-global bound is the hash constructor at its fixed
factory constants. All its runtime arguments remain universally quantified. -/
theorem compile_P (L : Lib) (c : CIx) (Q : FnSig CompilerArg (.list .bool))
    (H : FnSig Trans.Hash.THashArg WProg) (base den D getIdx idx : ℕ)
    (hQ : PolyB Q) {kH cH : ℕ}
    (hH : ∀ q r bits, FnBAt (G kH cH) H (base,den,q,r,bits)) :
    PolyB (compileF L c Q H base den D getIdx idx) := by
  have hW := hashWF_P L c base den hH
  exact polyB_bodySig _ _ (by
    simp [Tm.CallsP,compileBody,mkArg,degrees,table,oldX,polyB,hQ,hW])

end QecReliability.TensorMachine.QueryFL

namespace QecReliability.TensorMachine.QueryResources
open FL FL.Lib Trans.Query.Bound Trans.BoundsQH
open SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open Trans.Control (TKey)

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  (density : ℕ) (i : TensorQuery.FLCompiler.Indices) (compilerIdx : ℕ)

noncomputable def compiler := QueryFL.compileF Install.wL Install.wC
  (TensorQuery.FLCompiler.queryF Trans.Query.stdIx i) (Install.theHash hD hd A)
  (data hD hd A).base (data hD hd A).den density 16 compilerIdx

/-- The real all-length hash family discharges the hash bound: no runtime
query-compiler, seed-slicer, or grid-lookup complexity hypothesis remains. -/
theorem compiler_P : PolyB (compiler hD hd A density i compilerIdx) := by
  obtain ⟨kH,cH,hH⟩ := Install.theHash_bound hD hd A
  exact QueryFL.compile_P Install.wL Install.wC
    (TensorQuery.FLCompiler.queryF Trans.Query.stdIx i) (Install.theHash hD hd A)
    (data hD hd A).base (data hD hd A).den density 16 compilerIdx
    (TensorQuery.FLCompiler.query_P _ _) hH

/-- A single bound for every reachable query call once its retained context
and request key have bounded magnitude. The grid cardinality is present in
that context; it is not suppressed from this resource measure. -/
theorem compiler_bounds : ∃ k c : ℕ, ∀ (M : ℕ)
    (p : (Ty.prod ContextFL.TX TKey).den), mag (.prod ContextFL.TX TKey) p ≤ M →
      (compiler hD hd A density i compilerIdx).cost p ≤ G k c M ∧
      (compiler hD hd A density i compilerIdx).depth p ≤ G k c M ∧
      (compiler hD hd A density i compilerIdx).msize p ≤ G k c M ∧
      mag (.list .bool) ((compiler hD hd A density i compilerIdx).den p) ≤ G k c M ∧
      (Ty.enc (.list .bool) ((compiler hD hd A density i compilerIdx).den p)).size ≤
        5*G k c M+1 :=
  (compiler_P hD hd A density i compilerIdx).le_of_mag

/-- Explicit polynomial form of the actual callback's local-work bounds. -/
theorem compiler_polynomial : ∃ k c : ℕ, ∀ (M : ℕ)
    (p : (Ty.prod ContextFL.TX TKey).den), mag (.prod ContextFL.TX TKey) p ≤ M →
      (compiler hD hd A density i compilerIdx).cost p ≤ 26^(2^k-1)*(M+c+4)^(2^k) ∧
      (compiler hD hd A density i compilerIdx).depth p ≤ 26^(2^k-1)*(M+c+4)^(2^k) ∧
      (compiler hD hd A density i compilerIdx).msize p ≤ 26^(2^k-1)*(M+c+4)^(2^k) ∧
      (Ty.enc (.list .bool) ((compiler hD hd A density i compilerIdx).den p)).size ≤
        5*(26^(2^k-1)*(M+c+4)^(2^k))+1 := by
  obtain ⟨k,c,h⟩ := compiler_bounds hD hd A density i compilerIdx
  refine ⟨k,c,fun M p hp => ?_⟩
  have hb := h M p hp
  have hg := G_poly k c M
  exact ⟨by omega,by omega,by omega,by omega⟩

end QecReliability.TensorMachine.QueryResources
