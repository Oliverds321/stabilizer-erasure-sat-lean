import Trans.BoundsStep.PhaseA

/-!
# Trans.BoundsStep.PhasePrefix: the prefix traversal (`pstepF`, `prefixPF`, `resumeF`)

`pstep_cost/_depth/_msize` at every `y = (reply, pre)` are linear in `size y` (the result
duplicates the control's prefix list once, so `size (pstep y) ≤ 10·size y + c`, the factor coming from re-encoding `d - 1`); `prefixP` and
`resume` call `pstep` once, so their cost/depth/side budget are linear in `S = size a`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (TR TEnt TKey TPre TCtl TFrame TOp TG0 TG1 TG2 TG3 TG4 TG5 TG6
  TCfg TCtx TArg bodySig bodySig_cost bodySig_depth bodySig_msize bodySig_den)
open QecReliability.Trans.Bounds (shape2 shape3 shape4 shape5 shape6 shape7 shape8)

private theorem phasePrefix_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem phasePrefix_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable {TX' : Ty} (x : Control.Ix TX')

abbrev TY : Ty := .prod .bool TPre

theorem app_sz (t : Ty) (i : ℕ) (xs ys : List t.den) :
    (Ty.enc (.list t) ((appendF t i).den (xs, ys))).size =
      (Ty.enc (.list t) xs).size + (Ty.enc (.list t) ys).size - 1 := by
  have := Ty.sz_list_append t xs ys
  simp only [appendF_den]
  omega

/-! ## One prefix step -/

theorem pstep_cost (y : TY.den) : (Control.pstepF x).cost y ≤ 200 * (Ty.enc TY y).size + 2000 := by
  obtain ⟨rp, ⟨tag, d, pl, cap⟩, st⟩ := y
  have l2 := lit_sz 2 (by omega)
  have b1 := bl d; have b2 := bl cap
  have h1 := Ty.length_le_sz .bool pl
  rcases st with _ | ⟨⟨fb, lc, fpl, fcap⟩, rest⟩
  · dsimp only [Control.pstepF, bodySig_cost, Control.pstepBody, Tm.cost, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ,
      Ty.enc_nat, predF_cost, appendF_cost]
    sz_norm
    fin_le
  · have b3 := bl lc; have b4 := bl fcap
    have h2 := Ty.length_le_sz .bool fpl
    dsimp only [Control.pstepF, bodySig_cost, Control.pstepBody, Tm.cost, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ,
      Ty.enc_nat, predF_cost, appendF_cost, addF_cost, subF_cost]
    sz_norm
    (try rw [Ty.sz_list_cons])
    (try sz_norm)
    fin_le

theorem pstep_depth (y : TY.den) : (Control.pstepF x).depth y ≤ 2 * (Ty.enc TY y).size + 20 := by
  obtain ⟨rp, ⟨tag, d, pl, cap⟩, st⟩ := y
  have b1 := bl d; have b2 := bl cap
  have h1 := Ty.length_le_sz .bool pl
  rcases st with _ | ⟨⟨fb, lc, fpl, fcap⟩, rest⟩
  · dsimp only [Control.pstepF, bodySig_depth, Control.pstepBody, Tm.depth, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ,
      predF_depth, appendF_depth]
    sz_norm
    fin_le
  · have b3 := bl lc; have b4 := bl fcap
    have h2 := Ty.length_le_sz .bool fpl
    dsimp only [Control.pstepF, bodySig_depth, Control.pstepBody, Tm.depth, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ,
      predF_depth, appendF_depth, addF_depth, subF_depth]
    sz_norm
    (try rw [Ty.sz_list_cons])
    (try sz_norm)
    fin_le

theorem pstep_ex (y : TY.den) :
    Control.Tm'.ex (Control.pstepBody x) (Env.one y) ≤ 10 * (Ty.enc TY y).size + 100 := by
  obtain ⟨rp, ⟨tag, d, pl, cap⟩, st⟩ := y
  have b1 := bl d; have b2 := bl cap
  have z1 : (Enc.nat 1).size = 5 := Enc.nat_one_size
  rcases st with _ | ⟨⟨fb, lc, fpl, fcap⟩, rest⟩
  · dsimp only [Control.pstepBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ, predF_msize,
      appendF_msize, predF_den]
    sz_norm
    fin_le
  · have b3 := bl lc; have b4 := bl fcap
    dsimp only [Control.pstepBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ, predF_msize,
      appendF_msize, addF_msize, subF_msize, predF_den, addF_den, subF_den]
    sz_norm
    (try rw [Ty.sz_list_cons])
    (try sz_norm)
    have s1 := NatSize.size_add_le' lc d
    have s2 := NatSize.size_sub_le fcap d
    fin_le

theorem pstep_den_sz (y : TY.den) :
    (Ty.enc TY ((Control.pstepF x).den y)).size ≤ 10 * (Ty.enc TY y).size + 100 := by
  obtain ⟨rp, ⟨tag, d, pl, cap⟩, st⟩ := y
  have l2 := lit_sz 2 (by omega)
  have z1 : (Enc.nat 1).size = 5 := Enc.nat_one_size
  have z0 : (Enc.nat 0).size = 1 := Enc.nat_zero_size
  rcases st with _ | ⟨⟨fb, lc, fpl, fcap⟩, rest⟩
  · dsimp only [Control.pstepF, bodySig_den, Control.pstepBody, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ, predF_den]
    split_ifs <;> sz_norm <;> (try rw [app_sz]) <;> (repeat rw [Ty.sz_list_cons]) <;>
      (repeat rw [Ty.sz_list_nil]) <;> (try sz_norm) <;>
      (have q1 := Ty.sz_nat_le (d - 1); have q2 := NatSize.size_sub_le d 1; have q3 := bl d;
       simp only [Ty.enc_nat] at q1; omega)
  · dsimp only [Control.pstepF, bodySig_den, Control.pstepBody, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ, predF_den,
      addF_den, subF_den]
    split_ifs <;> sz_norm <;> (try rw [app_sz]) <;> (repeat rw [Ty.sz_list_cons]) <;>
      (repeat rw [Ty.sz_list_nil]) <;> (try sz_norm) <;>
      (have q1 := Ty.sz_nat_le (d - 1); have q2 := NatSize.size_sub_le d 1; have q3 := bl d
       have q4 := Ty.sz_nat_le (lc + d); have q5 := NatSize.size_add_le' lc d; have q6 := bl lc
       have q7 := Ty.sz_nat_le (fcap - d); have q8 := NatSize.size_sub_le fcap d
       have q9 := bl fcap
       simp only [Ty.enc_nat] at q1 q4 q7; omega)

theorem pstep_msize (y : TY.den) :
    (Control.pstepF x).msize y ≤ 20 * (Ty.enc TY y).size + 200 := by
  have h := Control.bodySig_msize_le x.pstep (Control.pstepBody x) y
  have h1 := pstep_ex x y
  have h2 := pstep_den_sz x y
  show (bodySig x.pstep (Control.pstepBody x)).msize y ≤ _
  have h2' : (Ty.enc (.prod .bool TPre) ((bodySig x.pstep (Control.pstepBody x)).den y)).size ≤
      10 * (Ty.enc TY y).size + 100 := h2
  omega

/-! ## prefix and resume -/

theorem sz_bp (b : Bool) (p : TPre.den) :
    (Ty.enc TY (b, p)).size = (Enc.bool b).size + (Ty.enc TPre p).size + 1 := by
  rw [shape2]; simp only [Ty.enc_bool]

theorem pre_le (p : TPre.den) :
    (Enc.nat p.1.1).size + (Enc.nat p.1.2.1).size + (Ty.enc (.list .bool) p.1.2.2.1).size + 3 ≤
      (Ty.enc TPre p).size := by
  sz_norm; omega

theorem prefixP_cost (a : (TArg TX').den) :
    (Control.prefixPF x).cost a ≤ 1000 * (Ty.enc (TArg TX') a).size + 10000 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, ⟨req, qu, rp, pre, cc, tc, kc⟩,
    ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := TKey), shape7 (a := Ty.list TEnt)] at hS
  simp only [Ty.enc_nat] at hS
  have l1 := lit_sz 1 (by omega); have l2 := lit_sz 2 (by omega)
  have hp := pre_le pre
  have b1 := bl pre.1.1; have b2 := bl tc; have b3 := bl cc
  dsimp only [Control.prefixPF, bodySig_cost, Control.prefixPBody, Tm.cost, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ,
    Ty.enc_nat, eqF_cost, eqF_den, addF_cost]
  rw [(min_eq_left (pstep_cost x _)).symm, sz_bp]
  have z : (Enc.bool false).size = 1 := rfl
  fin_le

theorem prefixP_depth (a : (TArg TX').den) :
    (Control.prefixPF x).depth a ≤ 2 * (Ty.enc (TArg TX') a).size + 40 := by
  suffices h : (Control.prefixPBody x).depth (Env.one a) ≤ 2 * (Ty.enc (TArg TX') a).size + 39 by
    simp only [Control.prefixPF, bodySig_depth]; omega
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, ⟨req, qu, rp, pre, cc, tc, kc⟩,
    ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := TKey), shape7 (a := Ty.list TEnt)] at hS
  simp only [Ty.enc_nat] at hS
  have l1 := lit_sz 1 (by omega)
  have hp := pre_le pre
  have b1 := bl pre.1.1; have b2 := bl tc; have b3 := bl cc
  dsimp only [Control.prefixPBody, Tm.depth, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ, eqF_depth, eqF_den, addF_depth]
  rw [(min_eq_left (pstep_depth x _)).symm, sz_bp]
  have z : (Enc.bool false).size = 1 := rfl
  fin_le

theorem prefixP_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.prefixPBody x) (Env.one a) ≤ 30 * (Ty.enc (TArg TX') a).size + 400 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, ⟨req, qu, rp, pre, cc, tc, kc⟩,
    ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape7 (a := TKey), shape7 (a := Ty.list TEnt)] at hS
  simp only [Ty.enc_nat] at hS
  have l1 := lit_sz 1 (by omega)
  have hp := pre_le pre
  have b1 := bl pre.1.1; have b2 := bl tc; have b3 := bl cc
  dsimp only [Control.prefixPBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ, eqF_msize, eqF_den,
    addF_msize]
  rw [(min_eq_left (pstep_msize x _)).symm, sz_bp, sz_nn, sz_nn]
  have z : (Enc.bool false).size = 1 := rfl
  have z1 : (Enc.nat 1).size = 5 := Enc.nat_one_size
  simp only [Ty.enc_nat]
  fin_le

theorem resume_cost (a : (TArg TX').den) :
    (Control.resumeF x).cost a ≤ 1000 * (Ty.enc (TArg TX') a).size + 10000 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, ⟨pc, code, good, coef, rep, scale, ne, tg⟩,
    ⟨req, qu, rp, pre, cc, tc, kc⟩, g2, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape8 (a := .nat), shape7 (a := TKey)] at hS
  simp only [Ty.enc_nat, Ty.enc_bool] at hS
  have l1 := lit_sz 1 (by omega); have l19 := lit_sz 19 (by omega)
  have b3 := bl cc
  dsimp only [Control.resumeF, bodySig_cost, Control.resumeBody, Tm.cost, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ,
    Ty.enc_nat, succF_cost]
  split_ifs <;> (try rw [(min_eq_left (pstep_cost x _)).symm, sz_bp]) <;> fin_le

theorem resume_depth (a : (TArg TX').den) :
    (Control.resumeF x).depth a ≤ 2 * (Ty.enc (TArg TX') a).size + 40 := by
  suffices h : (Control.resumeBody x).depth (Env.one a) ≤ 2 * (Ty.enc (TArg TX') a).size + 39 by
    simp only [Control.resumeF, bodySig_depth]; omega
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, ⟨pc, code, good, coef, rep, scale, ne, tg⟩,
    ⟨req, qu, rp, pre, cc, tc, kc⟩, g2, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape8 (a := .nat), shape7 (a := TKey)] at hS
  simp only [Ty.enc_nat, Ty.enc_bool] at hS
  have b3 := bl cc
  dsimp only [Control.resumeBody, Tm.depth, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ, succF_depth]
  split_ifs <;> (try rw [(min_eq_left (pstep_depth x _)).symm, sz_bp]) <;> fin_le

theorem resume_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.resumeBody x) (Env.one a) ≤ 30 * (Ty.enc (TArg TX') a).size + 400 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, ⟨pc, code, good, coef, rep, scale, ne, tg⟩,
    ⟨req, qu, rp, pre, cc, tc, kc⟩, g2, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape8 (a := .nat), shape7 (a := TKey)] at hS
  simp only [Ty.enc_nat, Ty.enc_bool] at hS
  have b3 := bl cc
  dsimp only [Control.resumeBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phasePrefix_get_zero, phasePrefix_get_succ, succF_msize]
  split_ifs <;> (try rw [(min_eq_left (pstep_msize x _)).symm, sz_bp]) <;>
    (try simp only [Ty.enc_bool]) <;> fin_le

end QecReliability.Trans.BoundsStep
