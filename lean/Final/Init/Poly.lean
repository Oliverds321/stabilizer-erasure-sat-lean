import Trans.BoundsQH.HParams
import Trans.Wire.Init

/-!
# Final.Init.Poly: magnitude bounds of the init callees

* `initF_P`: Control's `initF` (the initial configuration `initial q r m`) is `PolyB`
  (`polyB_bodySig` chain over the library compositions).
* `seedB_on`: `seedBF` is bounded by one `G K C` at every `q`, given the same for its
  hash-parameter function `Fp` at `(base, den, q)` (e.g. `BoundsQH.paramsF_on`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QecReliability.Final.Init
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH
open QecReliability.Trans.Control (bodySig)

/-! ## Control's `initF` -/

section InitF
open QecReliability.Trans.Control
variable (y : IxI)

theorem cellOpF_P : PolyB (cellOpF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, cellOpBody])

theorem cellsTailF_P : PolyB (cellsTailF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, cellsTailBody, polyB, mapF_P (cellOpF_P y)])

theorem trialOpF_P : PolyB (trialOpF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, trialOpBody])

theorem coefOpF_P : PolyB (coefOpF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, coefOpBody])

theorem idOpsF_P : PolyB (idOpsF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, idOpsBody])

theorem flattenF_P : PolyB (flattenF y) := flatMapF_P (idOpsF_P y) _

theorem trialsF_P : PolyB (trialsF y) :=
  polyB_bodySig _ _ (by
    simp [Tm.CallsP, trialsBody, polyB, flattenF_P y, mapEnvH_P (trialOpF_P y), cellsTailF_P y])

theorem coefsF_P : PolyB (coefsF y) :=
  polyB_bodySig _ _ (by
    simp [Tm.CallsP, coefsBody, polyB, flattenF_P y, mapEnvH_P (coefOpF_P y)])

theorem programF_P : PolyB (programF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, programBody, polyB, trialsF_P y, coefsF_P y])

theorem initF_P : PolyB (initF y) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, initBody, polyB, programF_P y])

end InitF

/-! ## `seedBF` -/

theorem fnBAtE_of_at {a b : Ty} {F : FnSig a b} {y : a.den} {k c K C : ℕ}
    (h : FnBAt (G k c) F y) (hk : k ≤ K) (hc : c ≤ C) (M : ℕ) : FnBAtE (G K C) F y M := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e := G_mono (m := mag a y) (m' := max (mag a y) M) hk hc (le_max_left _ _)
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e⟩

theorem seedB_on (L : Trans.Wire.Lib) (a : Trans.Wire.AIx)
    (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams) (base den : ℕ) {kp cp : ℕ}
    (hp : ∀ q, FnBAt (G kp cp) Fp (base, den, q)) :
    ∃ K C, ∀ q, FnBAt (G K C) (Trans.Wire.seedBF L a Fp base den) q := by
  obtain ⟨km, cm, hm⟩ := mulF_P (i := L.mul)
  obtain ⟨ks, cs, hs⟩ := succF_P (i := L.succ)
  obtain ⟨K', C', h⟩ := fnBOn_of_bodyE (K := kp + km + ks) (C := cp + cm + cs)
    (Trans.Wire.seedBF L a Fp base den) (Trans.Wire.seedBBody L Fp base den)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl) (fun _ => True)
    (fun q _ => by
      have em : ∀ y M, FnBAtE (G (kp + km + ks + 1) (cp + cm + cs)) (mulF L.mul) y M :=
        fun y M => fnBAtE_of hm (by omega) (by omega) y M
      have es : ∀ y M, FnBAtE (G (kp + km + ks + 1) (cp + cm + cs)) (succF L.succ) y M :=
        fun y M => fnBAtE_of hs (by omega) (by omega) y M
      have ep : ∀ M, FnBAtE (G (kp + km + ks + 1) (cp + cm + cs)) Fp (base, den, q) M :=
        fun M => fnBAtE_of_at (hp q) (by omega) (by omega) M
      simp only [Tm.CallsBE, Trans.Wire.seedBBody, Tm.den, Env.get, Env.one, em, es, ep,
        true_and, and_true])
  exact ⟨K', C', fun q => h q trivial⟩

end QecReliability.Final.Init
