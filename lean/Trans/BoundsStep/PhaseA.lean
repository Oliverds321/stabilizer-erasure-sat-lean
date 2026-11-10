import Trans.BoundsStep.Base

/-!
# Trans.BoundsStep.PhaseA: closed forms of the list-shuffling phases (Control/StepA)

For every phase `F` of `Control/StepA.lean` and every argument `a`, with
`S = (Ty.enc (TArg TX') a).size`: `F.cost a`, `F.depth a` and the side budget
`Tm'.ex body a` (so `F.msize a ≤ size (F.den a) + ex`, `Control.bodySig_msize_le`) are bounded
by explicit polynomials in `S` (only `selectScan` is quadratic, through `mulF`).

Recipe (see `Base.lean`): `dsimp only` (NOT `simp only`: `simp` times out on `ite` with large
branches), then `fin_le`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (TR TEnt TKey TPre TOp TG0 TG1 TG2 TG3 TG4 TG5 TG6 TCfg TCtx
  TArg bodySig bodySig_cost bodySig_depth bodySig_msize)
open QecReliability.Trans.Bounds (shape2 shape4 shape5 shape6 shape7 shape8)


private theorem phaseA_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem phaseA_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable {TX' : Ty} (x : Control.Ix TX')

theorem mulCost_sq (u v S : ℕ) (h : u.size + v.size ≤ S) : mulCost u v ≤ 100 * (S + 1) ^ 2 := by
  have := mulCost_le u v S h
  nlinarith

/-! ## reverseCells -/

theorem reverseCells_cost (a : (TArg TX').den) : (Control.reverseCellsF x).cost a ≤ 2000 := by
  obtain ⟨c, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  have l6 := lit_sz 6 (by omega)
  rcases ps with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseCellsF, bodySig_cost, Control.reverseCellsBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat]
    fin_le

theorem reverseCells_depth (a : (TArg TX').den) : (Control.reverseCellsF x).depth a ≤ 1 := by
  suffices h : (Control.reverseCellsBody (TX := TX')).depth (Env.one a) ≤ 0 by
    simp only [Control.reverseCellsF, bodySig_depth]; omega
  obtain ⟨c, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rcases ps with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseCellsBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

theorem reverseCells_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.reverseCellsBody (TX := TX')) (Env.one a) ≤ 0 := by
  obtain ⟨c, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rcases ps with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseCellsBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

/-! ## selectScan -/

theorem selectScan_cost (a : (TArg TX').den) :
    (Control.selectScanF x).cost a ≤ 2000 * ((Ty.enc (TArg TX') a).size + 1) ^ 2 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := Ty.list TEnt)] at hS
  have hsq : S + 1 ≤ (S + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have l7 := lit_sz 7 (by omega)
  rcases ps with _ | ⟨⟨e1, e2⟩, tl⟩
  · dsimp only [Control.selectScanF, bodySig_cost, Control.selectScanBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat]
    fin_le
  · rw [Ty.sz_list_cons, sz_nn e1 e2] at hS
    simp only [Ty.enc_nat] at hS
    have b1 := bl e1; have b2 := bl sf; have b3 := bl si; have b4 := bl B
    have m1 := mulCost_sq sf e1 S (by omega)
    have m2 := NatSize.size_mul_le sf e1
    have m3 := NatSize.size_bitNat_le false B
    have m4 := NatSize.size_bitNat_le false (bitNat false B)
    have m5 : (1 : ℕ).size ≤ 1 := NatSize.size_le_self 1
    dsimp only [Control.selectScanF, bodySig_cost, Control.selectScanBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat, leF_cost, leF_den, maxF_cost, mulF_cost, succF_cost, mulF_den]
    fin_le

theorem selectScan_depth (a : (TArg TX').den) :
    (Control.selectScanF x).depth a ≤ 10 * (Ty.enc (TArg TX') a).size + 20 := by
  suffices h : (Control.selectScanBody x).depth (Env.one a) ≤
      10 * (Ty.enc (TArg TX') a).size + 19 by
    simp only [Control.selectScanF, bodySig_depth]; omega
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := Ty.list TEnt)] at hS
  rcases ps with _ | ⟨⟨e1, e2⟩, tl⟩
  · dsimp only [Control.selectScanBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le
  · rw [Ty.sz_list_cons, sz_nn e1 e2] at hS
    simp only [Ty.enc_nat] at hS
    have b1 := bl e1; have b2 := bl sf; have b3 := bl si; have b4 := bl B
    have m2 := NatSize.size_mul_le sf e1
    have m3 := NatSize.size_bitNat_le false B
    have m4 := NatSize.size_bitNat_le false (bitNat false B)
    have m5 : (1 : ℕ).size ≤ 1 := NatSize.size_le_self 1
    dsimp only [Control.selectScanBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ, leF_depth, leF_den,
      maxF_depth, mulF_depth, succF_depth, mulF_den]
    fin_le

theorem selectScan_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.selectScanBody x) (Env.one a) ≤
      40 * (Ty.enc (TArg TX') a).size + 100 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := Ty.list TEnt)] at hS
  rcases ps with _ | ⟨⟨e1, e2⟩, tl⟩
  · dsimp only [Control.selectScanBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le
  · rw [Ty.sz_list_cons, sz_nn e1 e2] at hS
    simp only [Ty.enc_nat] at hS
    have b1 := bl e1; have b2 := bl sf; have b3 := bl si; have b4 := bl B
    have m2 := NatSize.size_mul_le sf e1
    have m3 := NatSize.size_bitNat_le false B
    have m4 := NatSize.size_bitNat_le false (bitNat false B)
    have m5 : (1 : ℕ).size ≤ 1 := NatSize.size_le_self 1
    have z1 := enc_bitNat_le false B
    have z2 := enc_bitNat_le false (bitNat false B)
    have z3 := enc_bitNat_le false sf
    have z4 : (Enc.nat (sf * e1)).size ≤ 4 * (sf * e1).size + 1 := Ty.sz_nat_le _
    dsimp only [Control.selectScanBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ, leF_msize,
      leF_den, maxF_msize, mulF_msize, succF_msize, mulF_den, Ty.enc_prod, Ty.enc_nat]
    fin_le

/-! ## trialCommit -/

theorem trialCommit_cost (a : (TArg TX').den) :
    (Control.trialCommitF x).cost a ≤ 200 * (Ty.enc (TArg TX') a).size + 1000 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, ⟨req, qu, rp, pre, cc, tc, kc⟩,
    ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := TKey), shape7 (a := Ty.list TEnt)] at hS
  simp only [Ty.enc_nat] at hS
  have b1 := bl kc; have b2 := bl tc
  dsimp only [Control.trialCommitF, bodySig_cost, Control.trialCommitBody, Tm.cost, Tm.den,
    Env.one, phaseA_get_zero, phaseA_get_succ, addF_cost, Ty.enc_nat]
  fin_le

theorem trialCommit_depth (a : (TArg TX').den) :
    (Control.trialCommitF x).depth a ≤ (Ty.enc (TArg TX') a).size + 10 := by
  suffices h : (Control.trialCommitBody x).depth (Env.one a) ≤ (Ty.enc (TArg TX') a).size + 9 by
    simp only [Control.trialCommitF, bodySig_depth]; omega
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, ⟨req, qu, rp, pre, cc, tc, kc⟩,
    ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := TKey), shape7 (a := Ty.list TEnt)] at hS
  simp only [Ty.enc_nat] at hS
  have b1 := bl kc; have b2 := bl tc
  dsimp only [Control.trialCommitBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ, addF_depth]
  fin_le

theorem trialCommit_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.trialCommitBody x) (Env.one a) ≤
      10 * (Ty.enc (TArg TX') a).size + 40 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, ⟨req, qu, rp, pre, cc, tc, kc⟩,
    ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := TKey), shape7 (a := Ty.list TEnt)] at hS
  simp only [Ty.enc_nat] at hS
  have b1 := bl kc; have b2 := bl tc
  dsimp only [Control.trialCommitBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ, addF_msize,
    Ty.enc_prod, Ty.enc_nat]
  fin_le

/-! ## sortNext (call-free) -/

theorem sortNext_cost (a : (TArg TX').den) : (Control.sortNextF x).cost a ≤ 2000 := by
  obtain ⟨c, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  have l9 := lit_sz 9 (by omega); have l11 := lit_sz 11 (by omega)
  rcases st with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.sortNextF, bodySig_cost, Control.sortNextBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat]
    fin_le

theorem sortNext_depth (a : (TArg TX').den) : (Control.sortNextF x).depth a ≤ 1 := by
  suffices h : (Control.sortNextBody (TX := TX')).depth (Env.one a) ≤ 0 by
    simp only [Control.sortNextF, bodySig_depth]; omega
  obtain ⟨c, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rcases st with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.sortNextBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

theorem sortNext_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.sortNextBody (TX := TX')) (Env.one a) ≤ 0 := by
  obtain ⟨c, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rcases st with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.sortNextBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

/-! ## insertScan -/

theorem insertScan_cost (a : (TArg TX').den) :
    (Control.insertScanF x).cost a ≤ 200 * (Ty.enc (TArg TX') a).size + 2000 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := Ty.list .nat)] at hS
  have l10 := lit_sz 10 (by omega)
  rcases ir with _ | ⟨h, tl⟩
  · dsimp only [Control.insertScanF, bodySig_cost, Control.insertScanBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat]
    fin_le
  · rw [Ty.sz_list_cons] at hS
    simp only [Ty.enc_nat] at hS
    have b1 := bl iv; have b2 := bl h
    dsimp only [Control.insertScanF, bodySig_cost, Control.insertScanBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat, leF_cost, leF_den]
    fin_le

theorem insertScan_depth (a : (TArg TX').den) :
    (Control.insertScanF x).depth a ≤ (Ty.enc (TArg TX') a).size + 10 := by
  suffices h : (Control.insertScanBody x).depth (Env.one a) ≤ (Ty.enc (TArg TX') a).size + 9 by
    simp only [Control.insertScanF, bodySig_depth]; omega
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := Ty.list .nat)] at hS
  rcases ir with _ | ⟨h, tl⟩
  · dsimp only [Control.insertScanBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le
  · rw [Ty.sz_list_cons] at hS
    simp only [Ty.enc_nat] at hS
    have b1 := bl iv; have b2 := bl h
    dsimp only [Control.insertScanBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ, leF_depth, leF_den]
    fin_le

theorem insertScan_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.insertScanBody x) (Env.one a) ≤
      10 * (Ty.enc (TArg TX') a).size + 40 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := Ty.list .nat)] at hS
  rcases ir with _ | ⟨h, tl⟩
  · dsimp only [Control.insertScanBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le
  · rw [Ty.sz_list_cons] at hS
    simp only [Ty.enc_nat] at hS
    have b1 := bl iv; have b2 := bl h
    dsimp only [Control.insertScanBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ, leF_msize,
      leF_den, Ty.enc_prod, Ty.enc_nat]
    fin_le

/-! ## insertRestore (call-free) -/

theorem insertRestore_cost (a : (TArg TX').den) : (Control.insertRestoreF x).cost a ≤ 2000 := by
  obtain ⟨c, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  have l8 := lit_sz 8 (by omega)
  rcases il with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.insertRestoreF, bodySig_cost, Control.insertRestoreBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat]
    fin_le

theorem insertRestore_depth (a : (TArg TX').den) : (Control.insertRestoreF x).depth a ≤ 1 := by
  suffices h : (Control.insertRestoreBody (TX := TX')).depth (Env.one a) ≤ 0 by
    simp only [Control.insertRestoreF, bodySig_depth]; omega
  obtain ⟨c, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rcases il with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.insertRestoreBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

theorem insertRestore_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.insertRestoreBody (TX := TX')) (Env.one a) ≤ 0 := by
  obtain ⟨c, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rcases il with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.insertRestoreBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

/-! ## medianLookup -/

theorem medianLookup_cost (a : (TArg TX').den) :
    (Control.medianLookupF x).cost a ≤ 100 * (Ty.enc (TArg TX') a).size + 2000 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := Ty.list .nat)] at hS
  simp only [Ty.enc_nat] at hS
  have l19 := lit_sz 19 (by omega); have l0 := lit_sz 0 (by omega)
  have b1 := bl lr
  rcases ir with _ | ⟨h, tl⟩ <;>
  · dsimp only [Control.medianLookupF, bodySig_cost, Control.medianLookupBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat, predF_cost]
    fin_le

theorem medianLookup_depth (a : (TArg TX').den) :
    (Control.medianLookupF x).depth a ≤ (Ty.enc (TArg TX') a).size + 10 := by
  suffices h : (Control.medianLookupBody x).depth (Env.one a) ≤
      (Ty.enc (TArg TX') a).size + 9 by
    simp only [Control.medianLookupF, bodySig_depth]; omega
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := Ty.list .nat)] at hS
  simp only [Ty.enc_nat] at hS
  have b1 := bl lr
  rcases ir with _ | ⟨h, tl⟩ <;>
  · dsimp only [Control.medianLookupBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ, predF_depth]
    fin_le

theorem medianLookup_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.medianLookupBody x) (Env.one a) ≤
      10 * (Ty.enc (TArg TX') a).size + 40 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, ⟨st, so, iv, il, ir, ires, lr⟩, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := Ty.list .nat)] at hS
  simp only [Ty.enc_nat] at hS
  have b1 := bl lr
  rcases ir with _ | ⟨h, tl⟩ <;>
  · dsimp only [Control.medianLookupBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ, predF_msize]
    fin_le

/-! ## reverseGood, reverseBad, reverseOutput (call-free) -/

theorem reverseGood_cost (a : (TArg TX').den) : (Control.reverseGoodF x).cost a ≤ 2000 := by
  obtain ⟨c, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  have l13 := lit_sz 13 (by omega)
  rcases ps with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseGoodF, bodySig_cost, Control.reverseGoodBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat]
    fin_le

theorem reverseGood_depth (a : (TArg TX').den) : (Control.reverseGoodF x).depth a ≤ 1 := by
  suffices h : (Control.reverseGoodBody (TX := TX')).depth (Env.one a) ≤ 0 by
    simp only [Control.reverseGoodF, bodySig_depth]; omega
  obtain ⟨c, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rcases ps with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseGoodBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

theorem reverseGood_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.reverseGoodBody (TX := TX')) (Env.one a) ≤ 0 := by
  obtain ⟨c, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rcases ps with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseGoodBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

theorem reverseBad_cost (a : (TArg TX').den) : (Control.reverseBadF x).cost a ≤ 2000 := by
  obtain ⟨c, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  have l14 := lit_sz 14 (by omega)
  rcases ps with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseBadF, bodySig_cost, Control.reverseBadBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat]
    fin_le

theorem reverseBad_depth (a : (TArg TX').den) : (Control.reverseBadF x).depth a ≤ 1 := by
  suffices h : (Control.reverseBadBody (TX := TX')).depth (Env.one a) ≤ 0 by
    simp only [Control.reverseBadF, bodySig_depth]; omega
  obtain ⟨c, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rcases ps with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseBadBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

theorem reverseBad_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.reverseBadBody (TX := TX')) (Env.one a) ≤ 0 := by
  obtain ⟨c, g0, g1, ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rcases ps with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseBadBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

theorem reverseOutput_cost (a : (TArg TX').den) : (Control.reverseOutputF x).cost a ≤ 2000 := by
  obtain ⟨c, g0, g1, g2, g3, g4, ⟨e0, e1, pv, ri, orv, out⟩, g6⟩ := a
  have l18 := lit_sz 18 (by omega)
  rcases orv with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseOutputF, bodySig_cost, Control.reverseOutputBody, Tm.cost, Tm.den,
      Env.one, phaseA_get_zero, phaseA_get_succ, Ty.enc_nat]
    fin_le

theorem reverseOutput_depth (a : (TArg TX').den) : (Control.reverseOutputF x).depth a ≤ 1 := by
  suffices h : (Control.reverseOutputBody (TX := TX')).depth (Env.one a) ≤ 0 by
    simp only [Control.reverseOutputF, bodySig_depth]; omega
  obtain ⟨c, g0, g1, g2, g3, g4, ⟨e0, e1, pv, ri, orv, out⟩, g6⟩ := a
  rcases orv with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseOutputBody, Tm.depth, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

theorem reverseOutput_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.reverseOutputBody (TX := TX')) (Env.one a) ≤ 0 := by
  obtain ⟨c, g0, g1, g2, g3, g4, ⟨e0, e1, pv, ri, orv, out⟩, g6⟩ := a
  rcases orv with _ | ⟨e, tl⟩ <;>
  · dsimp only [Control.reverseOutputBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseA_get_zero, phaseA_get_succ]
    fin_le

end QecReliability.Trans.BoundsStep
