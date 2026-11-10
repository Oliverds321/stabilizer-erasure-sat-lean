import Trans.BoundsRest.InitParse
import Final.Init.Poly
import Final.Init.Ctx

/-!
# Final.Init.Top: the init function `initTopF` at the machine input

* `top_split`: `initTopF = pair ctx (ite isZero zeroCfg (initF …))` after `parseF` and `ctxF`:
  its cost/depth/msize are below the sums of the parts (the literal `encCfg zeroCfg` enters by
  its encoded size, kept as an atom).
* **`top_le`**: at `problemBits rows (iidProgram n) a b c d ++ coins`, with one size parameter
  `Q` (input length, `n`, rows, precision sizes, `m ≤ 3Q+3`), cost, depth, msize and the input's
  encoded size are `≤ topB … Q`, a fixed polynomial in `Q` and the two `G` bounds of the
  callees `seedBF` (at `3n`) and Control's `initF` (at `(3n, n, m)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QecReliability.Final.Init
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH (G FnBAt PolyB G_mono sz_le)
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_cost bodySig_depth bodySig_msize
  TCtx TArg TCfg encCfg IxI initF)
open QecReliability.Trans.Wire
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding

private theorem top_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem top_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable (L : Lib) (h : HIx) (p : PIx) (a : AIx) (y : IxI)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams) (base den : ℕ)

theorem init_res_le (I : (Ty.prod .nat (.prod .nat .nat)).den) :
    (Ty.enc TCfg ((initF y).den I)).size ≤ (initF y).msize I :=
  le_max_of_le_right (le_max_right _ _)

/-- The size of the zero-length configuration literal. -/
abbrev zc : ℕ := (Ty.enc TCfg (encCfg zeroCfg)).size

theorem top_split (w : List Bool) (X : TParsed.den) (hX : (parseF L h p).den w = X)
    (C : (TCtx TX).den) (hC : (ctxF L a Fp base den).den X = C) :
    (initTopF L h p a y Fp base den).cost w ≤ (parseF L h p).cost w +
        (ctxF L a Fp base den).cost X + (initF y).cost (C.1.1, X.1, C.1.2.2.2) + zc + 50 ∧
      (initTopF L h p a y Fp base den).depth w ≤ (parseF L h p).depth w +
        (ctxF L a Fp base den).depth X + (initF y).depth (C.1.1, X.1, C.1.2.2.2) + 10 ∧
      (initTopF L h p a y Fp base den).msize w ≤ (parseF L h p).msize w +
        2 * (ctxF L a Fp base den).msize X + 2 * (initF y).msize (C.1.1, X.1, C.1.2.2.2) +
        2 * zc + 2 * (Ty.enc (.prod .nat (.prod .nat .nat)) (C.1.1, X.1, C.1.2.2.2)).size + 50 := by
  have ez : zc = (Ty.enc TCfg (encCfg zeroCfg)).size := rfl
  have r1 := ctx_res_le L a Fp base den X
  rw [hC] at r1
  have r2 := init_res_le y (C.1.1, X.1, C.1.2.2.2)
  have r3 : (Ty.enc (.prod .nat (.prod .nat .nat)) (C.1.1, X.1, C.1.2.2.2)).size =
      1 + (Ty.enc .nat C.1.1).size + (Ty.enc (.prod .nat .nat) (X.1, C.1.2.2.2)).size := rfl
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [initTopF, bodySig_cost, initTopBody, Tm.cost, Tm.den, Env.one, top_get_zero, top_get_succ]
    rw [hX, hC]
    split_ifs <;> omega
  · dsimp only [initTopF, bodySig_depth, initTopBody, Tm.depth, Tm.den, Env.one, top_get_zero, top_get_succ]
    rw [hX, hC]
    split_ifs <;> omega
  · dsimp only [initTopF, bodySig_msize, initTopBody, Tm.msize, Tm.den, Env.one, top_get_zero, top_get_succ]
    rw [hX, hC, Ty.sz_prod (TCtx TX) TCfg]
    split_ifs <;> simp only [max_le_iff] <;> omega

/-- The common bound of `top_le`. -/
def topB (Ks Cs Ki Ci Q : ℕ) : ℕ :=
  7000 * (Q + 2) ^ 4 + 4000 * ((2 * Q + 10) * (2 * Q + 10)) + 20 * G Ks Cs (3 * Q) +
    20 * G Ki Ci (7 * Q + 5) + 10 * zc + 1000

theorem rows_sz_le {n Q : ℕ} (rows : List (List (PauliCoord n))) (hn : n ≤ Q)
    (hrows : rows.length + rowIncidences rows ≤ Q) :
    (Ty.enc TRowsW (Trans.Query.encRows rows)).size ≤ 10 * ((2 * Q + 10) * (2 * Q + 10)) := by
  have h1 := sz_le TRowsW (Trans.Query.encRows rows)
  have h2 := Trans.BoundsRest.mag_rows_le rows
  have h3 : rowIncidences rows * (n + 2) ≤ Q * (Q + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 : 5 * (Q * (Q + 2)) + 10 * Q + 10 ≤ 10 * ((2 * Q + 10) * (2 * Q + 10)) := by nlinarith
  omega

theorem top_arith (Q pc pd pm cc cd cm ic id im zs Is ws Sg Ig : ℕ)
    (f1 : (Q + 2) ^ 2 ≤ (Q + 2) ^ 4) (q : 2 * Q + 10 ≤ (2 * Q + 10) * (2 * Q + 10))
    (hpc : pc ≤ 7000 * (Q + 2) ^ 4) (hpd : pd ≤ 20 * Q + 200) (hpm : pm ≤ 2000 * (Q + 2) ^ 2)
    (hcc : cc ≤ 3000 * ((2 * Q + 10) * (2 * Q + 10)) + Sg)
    (hcd : cd ≤ 100 * Q + 1000 + Sg) (hcm : cm ≤ 1000 * ((2 * Q + 10) * (2 * Q + 10)) + 10 * Sg)
    (hic : ic ≤ Ig) (hid : id ≤ Ig) (him : im ≤ Ig) (hIs : Is ≤ 35 * Q + 26) (hws : ws ≤ 4 * Q + 1) :
    pc + cc + ic + zs + 50 ≤
        7000 * (Q + 2) ^ 4 + 4000 * ((2 * Q + 10) * (2 * Q + 10)) + 20 * Sg + 20 * Ig + 10 * zs + 1000 ∧
      pd + cd + id + 10 ≤
        7000 * (Q + 2) ^ 4 + 4000 * ((2 * Q + 10) * (2 * Q + 10)) + 20 * Sg + 20 * Ig + 10 * zs + 1000 ∧
      pm + 2 * cm + 2 * im + 2 * zs + 2 * Is + 50 ≤
        7000 * (Q + 2) ^ 4 + 4000 * ((2 * Q + 10) * (2 * Q + 10)) + 20 * Sg + 20 * Ig + 10 * zs + 1000 ∧
      ws ≤
        7000 * (Q + 2) ^ 4 + 4000 * ((2 * Q + 10) * (2 * Q + 10)) + 20 * Sg + 20 * Ig + 10 * zs + 1000 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **`initTopF` at the machine input.** -/
theorem top_le {Ks Cs Ki Ci : ℕ} (hs : ∀ q, FnBAt (G Ks Cs) (seedBF L a Fp base den) q)
    (hi : FnB (G Ki Ci) (initF y)) {n Q : ℕ} (rows : List (List (PauliCoord n)))
    (x z c d : ℕ) (coins : List Bool) (w : List Bool)
    (hw : w = InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) x z c d ++ coins)
    (hQ : w.length ≤ Q) (hn : n ≤ Q) (hrows : rows.length + rowIncidences rows ≤ Q)
    (hsz : x.size + z.size + c.size + d.size ≤ Q)
    (hm : rationalRepetitionBudget (2 * (n + 1)) c d ≤ 3 * Q + 3) :
    (initTopF L h p a y Fp base den).cost w ≤ topB Ks Cs Ki Ci Q ∧
      (initTopF L h p a y Fp base den).depth w ≤ topB Ks Cs Ki Ci Q ∧
      (initTopF L h p a y Fp base den).msize w ≤ topB Ks Cs Ki Ci Q ∧
      (Ty.enc (.list .bool) w).size ≤ topB Ks Cs Ki Ci Q := by
  have hws := Trans.BoundsRest.sz_bools w
  subst hw
  have hco : coins.length ≤ Q := by simp only [List.length_append] at hQ; omega
  have hX := parseF_problemBits L h p rows x z c d coins
  obtain ⟨p1, p2, p3⟩ := Trans.BoundsRest.parse_le L h p rows x z c d coins hQ hn hrows
  obtain ⟨s1, s2, s3, s4⟩ := hs (n + (n + n))
  have gS : G Ks Cs (mag .nat (n + (n + n))) ≤ G Ks Cs (3 * Q) :=
    G_mono le_rfl le_rfl (show n + (n + n) ≤ 3 * Q by omega)
  have s4' : (seedBF L a Fp base den).den (n + (n + n)) ≤ G Ks Cs (3 * Q) := le_trans s4 gS
  obtain ⟨c1, c2, c3⟩ := ctx_le L a Fp base den n (Trans.Query.encRows rows) x z c d coins Q
    (G Ks Cs (3 * Q)) hn hsz (rows_sz_le rows hn hrows) hco (s1.trans gS) (s2.trans gS)
    (s3.trans gS) s4'
  have e1 : ((ctxF L a Fp base den).den (n, Trans.Query.encRows rows, x, z, c, d, coins)).1.1 =
      n + (n + n) := rfl
  have e2 : ((ctxF L a Fp base den).den (n, Trans.Query.encRows rows, x, z, c, d, coins)).1.2.2.2 =
      rationalRepetitionBudget (2 * (n + 1)) c d := repBF_den L a n c d
  obtain ⟨t1, t2, t3⟩ := top_split L h p a y Fp base den _ _ hX _ rfl
  generalize (ctxF L a Fp base den).den (n, Trans.Query.encRows rows, x, z, c, d, coins) = C at e1 e2 t1 t2 t3
  dsimp only at t1 t2 t3
  have hmI : mag (.prod .nat (.prod .nat .nat)) (C.1.1, n, C.1.2.2.2) ≤ 7 * Q + 5 := by
    obtain ⟨u, hu⟩ : ∃ u : ℕ, C.1.1 = u := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : ℕ, C.1.2.2.2 = v := ⟨_, rfl⟩
    have e1' : u = n + (n + n) := hu ▸ e1
    have e2' : v = rationalRepetitionBudget (2 * (n + 1)) c d := hv ▸ e2
    have em : mag (.prod .nat (.prod .nat .nat)) (C.1.1, n, C.1.2.2.2) = u + (n + v + 1) + 1 := by
      rw [hu, hv]; rfl
    omega
  have gI := G_mono (k := Ki) (c := Ci) le_rfl le_rfl hmI
  obtain ⟨i1, i2, i3, -⟩ := hi (C.1.1, n, C.1.2.2.2)
  have hIs := sz_le (.prod .nat (.prod .nat .nat)) (C.1.1, n, C.1.2.2.2)
  have hIs' : _ ≤ 35 * Q + 26 := le_trans hIs (by omega)
  have hws' : _ ≤ 4 * Q + 1 := le_trans hws (by omega)
  obtain ⟨f1, f2, f3, -⟩ := Trans.BoundsRest.pow_facts Q
  have q : 2 * Q + 10 ≤ (2 * Q + 10) * (2 * Q + 10) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨u1, u2, u3, u4⟩ := top_arith Q _ _ _ _ _ _ _ _ _ zc _ _ (G Ks Cs (3 * Q))
    (G Ki Ci (7 * Q + 5)) (f2.trans f3) q p1 p2 p3 c1 c2 c3 (i1.trans gI) (i2.trans gI)
    (i3.trans gI) hIs' hws'
  exact ⟨t1.trans u1, t2.trans u2, t3.trans u3, u4⟩

end QecReliability.Final.Init
