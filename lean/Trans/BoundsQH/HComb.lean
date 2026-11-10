import Trans.BoundsQH.QLayer
import Trans.Hash.Main

/-!
# Trans.BoundsQH.HComb: polynomial bounds of the hash program's non-recursive combinators

`polyB_exactH` (`Hash.exactSig`), and `PolyB` for `twF gmapF tabGatesF tabWiresF getD0F
pselectF pcomposeF padF` (`Trans/Hash/FLWire.lean`), `ipairsF setStepF setF dropLastF`
(`FLList`), `divModF` (closed form) `visStepF` (`FLWalk`), `addWireF scatStepF revStepF`
(`FLTrans`), `abitStepF affStepF rowF seedRowsF` (`FLAffine`), `dyStepF csStepF powStepF`
(`FLScalar`). Signature parameters (`itw`, `iset`, `iaw`, …) are assumed `PolyB` together with
the meaning equations of the `*_valid` theorems.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Hash QecReliability.Trans.Query.Plain

/-- `exactSig` functions are polynomially bounded when their callees are. -/
theorem polyB_exactH {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den)
    (hden : ∀ x, body.den (Env.one x) = den x) (hc : Tm.CallsP body) :
    PolyB (exactSig i body den) :=
  polyB_of_body _ body (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun x => (hden x).symm) hc

/-! ## Wires and programs (`FLWire`) -/

section Wire

@[polyB] theorem twF_P (ilt igd iadd isub i : ℕ) : PolyB (twF ilt igd iadd isub i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨⟨os, k, b⟩, w⟩ := x
      simp only [twBody, tm_simp, ltF_den, getDF_den, addF_den, subF_den, tableWire]
      split_ifs <;> simp_all)
    (by simp [Tm.CallsP, twBody, polyB])

theorem gmapF_P {itw : FnSig (.prod TTab .nat) .nat} (htw : PolyB itw)
    (htwd : ∀ x, itw.den x = tableWire x.1 x.2) (i : ℕ) : PolyB (gmapF itw i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨e, ⟨u, s, a, b⟩⟩ := x
      simp only [gmapBody, tm_simp, gmapW, htwd])
    (by simp [Tm.CallsP, gmapBody, htw])

theorem tabGatesF_P {itw : FnSig (.prod TTab .nat) .nat} (htw : PolyB itw)
    (htwd : ∀ x, itw.den x = tableWire x.1 x.2) (igm i : ℕ) : PolyB (tabGatesF itw igm i) :=
  mapEnvH_P (gmapF_P htw htwd igm) i

theorem tabWiresF_P {itw : FnSig (.prod TTab .nat) .nat} (htw : PolyB itw) (i : ℕ) :
    PolyB (tabWiresF itw i) := mapEnvH_P htw i

@[polyB] theorem getD0F_P (igd i : ℕ) : PolyB (getD0F igd i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, getD0Body])
    (by simp [Tm.CallsP, getD0Body, polyB])

theorem pselectF_P {igd ig is : ℕ} (i : ℕ) :
    PolyB (pselectF (mapEnvF (getD0F igd ig) is) i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, pselectBody, pselect, getD0F])
    (by simp [Tm.CallsP, pselectBody, mapEnvH_P (getD0F_P igd ig) is])

theorem pcomposeF_P {ilen iadd iapp : ℕ} {itg : FnSig (.prod TTab (.list TGate)) (.list TGate)}
    {itw : FnSig (.prod TTab (.list .nat)) (.list .nat)} (htg : PolyB itg) (htw : PolyB itw)
    (htgd : ∀ x, itg.den x = tabGates x.1 x.2) (htwd : ∀ x, itw.den x = tabWires x.1 x.2)
    (i : ℕ) : PolyB (pcomposeF ilen iadd iapp itg itw i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, pcomposeBody, pcompose, htgd, htwd])
    (by simp [Tm.CallsP, pcomposeBody, polyB, htg, htw])

theorem padF_P {imt : FnSig (.prod .nat (.list .nat)) (.list .nat)} {irange isucc ilen isub irep
    iappw : ℕ} {itg : FnSig (.prod TTab (.list TGate)) (.list TGate)}
    {itw : FnSig (.prod TTab (.list .nat)) (.list .nat)} (hmt : PolyB imt)
    (hmtd : ∀ x, imt.den x = x.2.map (fun j => min x.1 j)) (htg : PolyB itg) (htw : PolyB itw)
    (htgd : ∀ x, itg.den x = tabGates x.1 x.2) (htwd : ∀ x, itw.den x = tabWires x.1 x.2)
    (i : ℕ) : PolyB (padF imt irange isucc ilen isub irep iappw itg itw i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, padBody, padP, htgd, htwd, hmtd, padTable_eq])
    (by simp [Tm.CallsP, padBody, polyB, hmt, htg, htw])

end Wire

/-! ## Lists (`FLList`) -/

section Lists

theorem ipCost_le {α : Type} (xs : List α) (k : ℕ) :
    ipCost xs k ≤ (xs.length + 1) * (25 * (k + xs.length) + 70) := by
  induction xs generalizing k with
  | nil => simp [ipCost]
  | cons x xs ih =>
    have h1 := ih (k + 1)
    have h2 := natSize_le k
    simp only [ipCost, List.length_cons]
    nlinarith

theorem ipDepth_le {α : Type} (xs : List α) (k : ℕ) : ipDepth xs k ≤ xs.length + k + xs.length + 2 := by
  induction xs generalizing k with
  | nil => simp [ipDepth]
  | cons x xs ih =>
    have h1 := ih (k + 1)
    have h2 := natSize_le k
    simp only [ipDepth, List.length_cons]
    omega

theorem mag_ipairs (t : Ty) (xs : List t.den) (k : ℕ) :
    mag (.list (.prod t .nat)) (ipairs xs k) ≤ mag (.list t) xs * (k + xs.length + 3) := by
  induction xs generalizing k with
  | nil =>
    have h1 : mag (.list (.prod t .nat)) (ipairs ([] : List t.den) k) = 1 := rfl
    have h2 : mag (.list t) ([] : List t.den) = 1 := rfl
    rw [h1, h2]; simp
  | cons x xs ih =>
    have h1 := ih (k + 1)
    have hl := mag_list_len t xs
    have e1 : mag (.list (.prod t .nat)) (ipairs (x :: xs) k) =
        mag t x + k + 1 + 1 + mag (.list (.prod t .nat)) (ipairs xs (k + 1)) := rfl
    have e2 : mag (.list t) (x :: xs) = mag t x + 1 + mag (.list t) xs := rfl
    rw [e1, e2]
    simp only [List.length_cons]
    nlinarith

theorem ipairsF_B (t : Ty) (i : ℕ) : FnB (G 3 3000) (ipairsF t i) := fun p => by
  obtain ⟨xs, (k : ℕ)⟩ := p
  have hm : mag (.prod (.list t) .nat) (xs, k) = mag (.list t) xs + k + 1 := rfl
  rw [hm]
  generalize hM : mag (.list t) xs + k + 1 = m
  have hl := mag_list_len t xs
  have c1 := ipCost_le xs k
  have d1 := ipDepth_le xs k
  have r1 := mag_ipairs t xs k
  have s1 := sz_le (.list (.prod t .nat)) (ipairs xs k)
  have s2 := sz_le (.list t) xs
  have s3 := natSize_le (k + xs.length)
  have q := quad_le 3000 m
  have hX := sq_ge m
  have g3 : 5 * G 2 3000 m + 16 ≤ G 3 3000 m := G_succ 2 3000 m
  have p1 : (xs.length + 1) * (25 * (k + xs.length) + 70) ≤ 70 * ((m + 1) * (m + 1)) := by
    have : (xs.length + 1) * (25 * (k + xs.length) + 70) ≤ (m + 1) * (70 * (m + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have p2 : mag (.list t) xs * (k + xs.length + 3) ≤ 3 * ((m + 1) * (m + 1)) := by
    have : mag (.list t) xs * (k + xs.length + 3) ≤ (m + 1) * (3 * (m + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  simp only [ipairsF_cost, ipairsF_depth, ipairsF_msize, ipairsF_den]
  refine ⟨by omega, by omega, by omega, by omega⟩

@[polyB] theorem ipairsF_P (t : Ty) (i : ℕ) : PolyB (ipairsF t i) := ⟨_, _, ipairsF_B t i⟩

@[polyB] theorem setStepF_P (ieq i : ℕ) : PolyB (setStepF ieq i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, setStepBody])
    (by simp [Tm.CallsP, setStepBody, polyB])

theorem hsetF_P (iip ieq is im i : ℕ) : PolyB (setF iip (mapEnvF (setStepF ieq is) im) i) :=
  polyB_exactH _ _ _
    (fun x => by
      simp only [setBody, tm_simp, mapEnvF_den, ipairsF_den, setStepF, exactSig_den]
      rw [set_eq_map])
    (by simp [Tm.CallsP, setBody, polyB, mapEnvH_P (setStepF_P ieq is) im])

@[polyB] theorem dropLastF_P (ilen ipred itake i : ℕ) : PolyB (dropLastF ilen ipred itake i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, dropLastBody, List.dropLast_eq_take])
    (by simp [Tm.CallsP, dropLastBody, polyB])

end Lists

/-! ## Walks and transposes -/

section Walk

theorem divModF_B (ile isub i : ℕ) : FnB (G 2 400) (divModF ile isub i) := fnB_quad _ _ fun y => by
  obtain ⟨(a : ℕ), (b : ℕ)⟩ := y
  have ha := natSize_le a
  have hb := natSize_le b
  have hX := sq_ge (a + b + 1)
  have hm : (a.size + 1) * (b.size + 2) ≤ (a + b + 1 + 1) * (a + b + 1 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : 300 * (a.size + 1) * (b.size + 2) = 300 * ((a.size + 1) * (b.size + 2)) := by ring
  have h1 : a / b ≤ a := Nat.div_le_self a b
  have h2 : a % b ≤ a := Nat.mod_le a b
  simp only [mag_prod, mag_nat, divModF_cost, divModF_depth, divModF_msize, divModF_den, e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

@[polyB] theorem divModF_P (ile isub i : ℕ) : PolyB (divModF ile isub i) := ⟨_, _, divModF_B ile isub i⟩

theorem visStepF_P {inb : FnSig (.prod .nat (.prod .nat .nat)) .nat}
    {idm : FnSig (.prod .nat .nat) (.prod .nat .nat)} (hnb : PolyB inb) (hdm : PolyB idm)
    (hdmd : ∀ x, idm.den x = (x.1 / x.2, x.1 % x.2)) (i : ℕ) : PolyB (visStepF inb idm i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, visStepBody, hdmd])
    (by simp [Tm.CallsP, visStepBody, hnb, hdm])

theorem addWireF_P {iapp : ℕ} {igd0 : FnSig (.prod (.list .nat) .nat) .nat}
    {iset : FnSig (.prod (.list .nat) (.prod .nat .nat)) (.list .nat)} {iadd ilen : ℕ}
    (hgd : PolyB igd0) (hgdd : ∀ x, igd0.den x = x.1.getD x.2 0) (hset : PolyB iset)
    (hsetd : ∀ x, iset.den x = x.1.set x.2.1 x.2.2) (i : ℕ) :
    PolyB (addWireF iapp igd0 iset iadd ilen i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, addWireBody', pAddWire, hgdd, hsetd])
    (by simp [Tm.CallsP, addWireBody', polyB, hgd, hset])

theorem scatStepF_P {iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg}
    (haw : PolyB iaw) (hawd : ∀ x, iaw.den x = pAddWire x.1 x.2.1 x.2.2.1 x.2.2.2) (i : ℕ) :
    PolyB (scatStepF iaw i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, scatStepBody, scatStep, hawd])
    (by simp [Tm.CallsP, scatStepBody, haw])

theorem revStepF_P {iaw : FnSig (.prod .nat (.prod TProg (.prod .nat .nat))) TProg}
    {idl : FnSig (.list .nat) (.list .nat)} {igd0 : FnSig (.prod (.list .nat) .nat) .nat}
    {ipred ilen : ℕ} (haw : PolyB iaw)
    (hawd : ∀ x, iaw.den x = pAddWire x.1 x.2.1 x.2.2.1 x.2.2.2) (hdl : PolyB idl)
    (hdld : ∀ x, idl.den x = x.dropLast) (hgd : PolyB igd0)
    (hgdd : ∀ x, igd0.den x = x.1.getD x.2 0) (i : ℕ) :
    PolyB (revStepF iaw idl igd0 ipred ilen i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨_, ⟨u, _⟩⟩ := x
      cases u <;> simp [tm_simp, revStepBody, revStep, hawd, hdld, hgdd])
    (by simp [Tm.CallsP, revStepBody, polyB, haw, hdl, hgd])

end Walk

/-! ## Affine hashing and scans -/

section Affine

@[polyB] theorem abitStepF_P (iapp iadd ilen i : ℕ) : PolyB (abitStepF iapp iadd ilen i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨⟨c, _⟩, _⟩ := x
      cases c <;> simp [tm_simp, abitStepBody, abitStep])
    (by simp [Tm.CallsP, abitStepBody, polyB])

theorem affStepF_P {iabit : FnSig (.prod .nat (.prod (.list .bool) (.prod .bool .nat)))
    (.prod (.list TGate) .nat)} {imul irange iadd ilen iapp : ℕ}
    {itg : FnSig (.prod TTab (.list TGate)) (.list TGate)}
    {itw : FnSig (.prod TTab (.list .nat)) (.list .nat)} (habit : PolyB iabit)
    (habitd : ∀ x, iabit.den x = abit x.1 x.2.1 x.2.2.1 x.2.2.2) (htg : PolyB itg)
    (htw : PolyB itw) (htgd : ∀ x, itg.den x = tabGates x.1 x.2)
    (htwd : ∀ x, itw.den x = tabWires x.1 x.2) (i : ℕ) :
    PolyB (affStepF iabit imul irange iadd ilen iapp itg itw i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, affStepBody, affStep, habitd, htgd, htwd, Nat.mul_comm])
    (by simp [Tm.CallsP, affStepBody, polyB, habit, htg, htw])

@[polyB] theorem rowF_P (isucc imul idrop itake igd iadd i : ℕ) :
    PolyB (rowF isucc imul idrop itake igd iadd i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, rowBody])
    (by simp [Tm.CallsP, rowBody, polyB])

theorem seedRowsF_P {irange : ℕ} {F : FnSig (.prod (.prod .nat (.list .bool)) .nat) TRow}
    {im : ℕ} (hF : PolyB F)
    (hFd : ∀ x, F.den x = ((x.1.2.drop ((x.1.1 + 1) * x.2)).take x.1.1,
      x.1.2.getD ((x.1.1 + 1) * x.2 + x.1.1) false)) (i : ℕ) :
    PolyB (seedRowsF irange (mapEnvF F im) i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, seedRowsBody, hFd, seedRows_map])
    (by simp [Tm.CallsP, seedRowsBody, polyB, mapEnvH_P hF im])

@[polyB] theorem dyStepF_P (ile isucc imul i : ℕ) : PolyB (dyStepF ile isucc imul i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨⟨T, d, e, p⟩, j⟩ := x
      cases d <;> simp [tm_simp, dyStepBody, dyStep] <;> split_ifs <;> simp)
    (by simp [Tm.CallsP, dyStepBody, polyB])

@[polyB] theorem csStepF_P (ile isucc imul i : ℕ) : PolyB (csStepF ile isucc imul i) :=
  polyB_exactH _ _ _
    (fun x => by
      obtain ⟨⟨N, d, s⟩, j⟩ := x
      cases d <;> simp [tm_simp, csStepBody, csStep] <;> split_ifs <;> simp)
    (by simp [Tm.CallsP, csStepBody, polyB])

@[polyB] theorem powStepF_P (imul i : ℕ) : PolyB (powStepF imul i) :=
  polyB_exactH _ _ _ (fun x => by simp [tm_simp, powStepBody, powStep])
    (by simp [Tm.CallsP, powStepBody, polyB])

end Affine

end QecReliability.Trans.BoundsQH
