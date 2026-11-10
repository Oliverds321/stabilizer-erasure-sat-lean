import Trans.BoundsEnc.Basic

/-!
# Trans.BoundsEnc.Gates: the encoder's polynomially bounded callees

`PolyB` (one `G k c` in the argument's magnitude, all arguments) for
* the MGG rotation: `coordF_P`, `mggRotF_P`, `lazyRotF_P`, the walk step `pwStepF_P`;
* the coefficient lookup `testBitF_P` (closed form);
* the base program: `baseGateF_P`, `baseOutF_P`, **`baseF_P`**;
* the amplifier outputs `ampOutF_P`;
* the composition `pcF_P` (`PcIx.pcF`) and **`oneCopyF_P`**.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.BoundsEnc
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH QecReliability.Trans.Hash QecReliability.Trans.HashCallees
open QecReliability.Trans.Query.Plain

/-! ## The MGG rotation -/

theorem coordF_P (L : HashCallees.Lib) (i : ℕ) : PolyB (coordF L i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨n, a, b, c, inv⟩ := x
      cases inv <;> simp [tm_simp, coordBody, coordP])
    (by simp [Tm.CallsP, coordBody, polyB, divModF_P])

theorem mggRotF_P (L : HashCallees.Lib) (icoord i : ℕ) : PolyB (mggRotF L icoord i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨n, v, p⟩ := x
      simp only [mggRotBody, tm_simp, Lib.dmF_den, addF_den, mulF_den, predF_den, succF_den,
        oddF_den, div2F_den, coordF, exactSig_den, mggRotP, Env.one])
    (by simp [Tm.CallsP, mggRotBody, polyB, divModF_P, coordF_P])

theorem lazyRotF_P (L : HashCallees.Lib) (icoord irot i : ℕ) : PolyB (lazyRotF L icoord irot i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨n, v, p⟩ := x
      simp only [lazyRotBody, tm_simp, ltF_den, mggRotF, exactSig_den, lazyRotP, Env.one]
      split_ifs <;> simp_all)
    (by simp [Tm.CallsP, lazyRotBody, polyB, mggRotF_P])

theorem pwStepF_P (L : HashCallees.Lib) (R : RotIx) (i : ℕ) : PolyB (pwStepF L R i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨⟨s, v, w, acc⟩, j⟩ := x
      simp [tm_simp, pwStepBody, HashCallees.powStep, lazyRotF, RotIx.lazyF])
    (by simp [Tm.CallsP, pwStepBody, polyB, divModF_P, lazyRotF_P])

/-! ## Coefficient lookup -/

theorem testBitF_B (L : HashCallees.Lib) (i : ℕ) : FnB (G 2 100) (testBitF L i) :=
  fnB_quad _ _ fun y => by
    obtain ⟨(a : ℕ), (p : ℕ)⟩ := y
    have ha := natSize_le a
    have hp := natSize_le p
    have hm : mag (.prod .nat .nat) (a, p) = a + p + 1 := rfl
    have hr : mag .bool ((testBitF L i).den (a, p)) = 1 := rfl
    rw [hm, hr]
    simp only [testBitF_cost, testBitF_depth, testBitF_msize]
    have e1 : (p + 1) * (25 * p.size + 60) ≤ (a + p + 1 + 1) * (85 * (a + p + 1 + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e2 : (a + p + 1 + 1) * (85 * (a + p + 1 + 1)) =
        85 * ((a + p + 1 + 1) * (a + p + 1 + 1)) := by ring
    have e3 := sq_ge (a + p + 1)
    refine ⟨by omega, by omega, by omega, by omega⟩

theorem testBitF_P (L : HashCallees.Lib) (i : ℕ) : PolyB (testBitF L i) := ⟨_, _, testBitF_B L i⟩

/-! ## The base program -/

theorem baseGateF_P (L : HashCallees.Lib) (itb i : ℕ) : PolyB (baseGateF L itb i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨⟨code, k, h, n⟩, g⟩ := x
      simp only [baseGateBody, tm_simp, Lib.dmF_den, addF_den, mulF_den, testBitF_den, gateP,
        baseRef, coeffP, exactSig_den, Env.one, Tm.den_isZero]
      by_cases h0 : g % k = 0 <;> simp [h0, Nat.mul_comm])
    (by simp [Tm.CallsP, baseGateBody, polyB, divModF_P, testBitF_P])

theorem baseOutF_P (L : HashCallees.Lib) (i : ℕ) : PolyB (baseOutF L i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, baseOutBody])
    (by simp [Tm.CallsP, baseOutBody, polyB])

theorem baseF_P (L : HashCallees.Lib) (I : BaseIx) : PolyB (baseF L I) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨D, code⟩ := x
      simp only [baseBody, tm_simp, addF_den, div2F_den, mulF_den, mapEnvF_den, rangeF_den,
        appendF_den, replicateF_den, baseGateF, baseOutF, exactSig_den, Env.one, baseP, emitP,
        Nat.div_div_eq_div_mul]
      try simp [List.append_assoc])
    (by simp [Tm.CallsP, baseBody, polyB, mapEnvH_P (baseGateF_P L I.tb I.gate) I.gmap,
      mapEnvH_P (baseOutF_P L I.out) I.omap])

/-! ## Amplifier outputs -/

theorem ampOutF_P (L : HashCallees.Lib) (i : ℕ) : PolyB (ampOutF L i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨⟨T, m, c⟩, j⟩ := x
      simp only [ampOutBody, tm_simp, ltF_den, addF_den, mulF_den, succF_den, exactSig_den,
        Env.one]
      split_ifs <;> simp_all)
    (by simp [Tm.CallsP, ampOutBody, polyB])

/-! ## Composition and one copy -/

theorem pcF_P (L : HashCallees.Lib) (I : PcIx) : PolyB (I.pcF L) := by
  have htwd : ∀ x, (I.twF L).den x = tableWire x.1 x.2 := fun _ => rfl
  exact pcomposeF_P (tabGatesF_P (twF_P _ _ _ _ _) htwd _ _) (tabWiresF_P (twF_P _ _ _ _ _) _)
    (fun _ => rfl) (fun x => tabWiresF_den _ _ htwd x.1 x.2) _

theorem oneCopyF_P (L : HashCallees.Lib) (I : PcIx) (i : ℕ) : PolyB (oneCopyF L I i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, oneCopyBody, oneCopyP])
    (by simp [Tm.CallsP, oneCopyBody, polyB, pcF_P])

end QecReliability.Trans.BoundsEnc
