import LatentRuntimeAgreement
import Install.Callees

/-! Actual measured latent query-wrapper bounds. The newly introduced add/sub
for r=q-(n+n) is charged by the same concrete FL composition calculus as every
other primitive. The final theorem discharges the hash premise with the fixed
factory; magnitude-to-input-length and all-tape lowering remain separate. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.CompileBounds
open FL FL.Lib Trans.Wire Trans.Query.Bound
open Trans.BoundsQH
open Trans.Control (TKey)
open Trans.Hash (THashArg)

variable (L : Lib) (c : CIx) {Q : FnSig WQArg (.list .bool)}
  {H : FnSig THashArg WProg} (base den density : ℕ)

theorem cell_poly (hQ : PolyB Q) (hH : PolyB (hashWF L c H base den)) :
    PolyB (WrappersFL.cellQF L c Q H base den density) :=
  polyB_bodySig _ _ (by
    simp [Tm.CallsP,WrappersFL.cellQBody,WrappersFL.Xr,polyB,hQ,hH])

theorem base_poly (hQ : PolyB Q) : PolyB (WrappersFL.baseQF L c Q density) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,WrappersFL.baseQBody,WrappersFL.Xr,polyB,hQ])

theorem compile_poly (hQ : PolyB Q) {kH cH : ℕ}
    (hH : ∀ q r bits, FnBAt (G kH cH) H (base,den,q,r,bits)) :
    PolyB (WrappersFL.compileF L c Q H base den density) :=
  polyB_bodySig _ _ (by
    simp [Tm.CallsP,WrappersFL.compileBody,
      cell_poly L c base den density hQ (hashWF_P L c base den hH),base_poly L c density hQ])

end QecReliability.LatentMachine.CompileBounds

noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Query.Bound Trans.BoundsQH
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)

/-- Uniform measured bound for the actual installed callback, with no hash
resource premise. The numeric magnitude M is not yet identified with paper L. -/
theorem compile_bound : ∃ K C', ∀ (M : ℕ) (y : (Ty.prod TX Trans.Control.TKey).den),
    mag (.prod TX Trans.Control.TKey) y ≤ M →
      (controller hD hd A density).compile.cost y ≤ G K C' M ∧
      (controller hD hd A density).compile.depth y ≤ G K C' M ∧
      (controller hD hd A density).compile.msize y ≤ G K C' M ∧
      mag (.list .bool) ((controller hD hd A density).compile.den y) ≤ G K C' M ∧
      (Ty.enc (.list .bool) ((controller hD hd A density).compile.den y)).size ≤ 5*G K C' M+1 := by
  obtain ⟨kH,cH,hH⟩ := Install.theHash_bound hD hd A
  have h := CompileBounds.compile_poly Install.wL WrappersInstalled.indices
    (data hD hd A).base (data hD hd A).den density
    (queryFnF_P Trans.Query.stdIx) hH
  exact h.le_of_mag

end QecReliability.LatentMachine.Runtime
