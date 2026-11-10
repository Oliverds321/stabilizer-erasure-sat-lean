import Assembly.Run

/-! Widen only the verified register invariant. Actual primitive executions,
primitive costs, oracle requests and oracle costs are unchanged. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.Runtime
open RegMachine

private theorem bigStep_invariant_mono {P S : Type} {σ : PrimSem P S}
    {I J : S → Prop} (hIJ : ∀ s, I s → J s) {st : Stmt P} {s t : S} {N C : ℕ}
    (h : Stmt.BigStep σ I st s N C t) : Stmt.BigStep σ J st s N C t := by
  induction h with
  | prim hs hp he ht => exact .prim (hIJ _ hs) hp he (hIJ _ ht)
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | iteT hs hp he _ ih => exact .iteT (hIJ _ hs) hp he ih
  | iteF hs hp he _ ih => exact .iteF (hIJ _ hs) hp he ih
  | loopF hs hp he hb ht => exact .loopF (hIJ _ hs) hp he hb (hIJ _ ht)
  | loopT hs hp he _ _ ih1 ih2 => exact .loopT (hIJ _ hs) hp he ih1 ih2

/-- No replay, resampling, or changed cost is introduced when enlarging the
register-size certificate for the same actual run. -/
theorem oruns_space_mono {O : OracleSpec} {S S' : ℕ} {st : Stmt (OInstr 20)}
    {s t : Regs 20} {c : ℕ} (h : Assembly.ORuns O S st s t c) (hS : S ≤ S') :
    Assembly.ORuns O S' st s t c := by
  obtain ⟨N,C,hr,hc⟩ := h
  exact ⟨N,C,bigStep_invariant_mono (fun s hs r => (hs r).trans hS) hr,hc⟩

end QecReliability.LatentMachine.Runtime
