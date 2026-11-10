import LatentEndpointRepairFL
import Trans.BoundsStep.PhaseRepair

/-! Actual endpoint-only repair resource bounds, adapting the pinned generic
bit-size proof. Entry and counter
bounds are uniform in the shape flag; every execution here uses false. No
comparison with the differently encoded true-mode result is assumed. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.LatentMachine.EndpointControllerBounds
open QecReliability.Trans QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.FL.Lib.LinearRepairFL (entryF entryF_cost entryF_den entryF_depth
  entryF_msize entryCost entryDepth entryMsize entryR ctrF ctrF_cost ctrF_den ctrF_depth
  ctrF_msize ctrR mdF mdF_cost mdF_den mdF_depth mdF_msize RB entryR_RB entryCost_le
  entryDepth_le countsF_msize lesserF_msize greaterF_msize max4_size_le)
open QecReliability.Trans.Control (TR TEnt TKey TPre TCtl TFrame TOp TG0 TG1 TG2 TG3 TG4 TG5 TG6
  TCfg TCtx TArg TRA bodySig bodySig_cost bodySig_depth bodySig_msize bodySig_den)
open QecReliability.Trans.Bounds (shape2 shape3 shape4 shape5 shape6 shape7 shape8)

private theorem endpoint_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem endpoint_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable {TX' : Ty} (x : Control.Ix TX')





theorem repairAcc_cost (w : TRA.den) :
    (EndpointControllerFL.repairAccF x).cost w ≤ 20000 * ((Ty.enc TRA w).size + 1) ^ 2 := by
  generalize hS : (Ty.enc TRA w).size = S
  obtain ⟨r, ⟨g0, g1, g2, g3, g4, ⟨⟨a1, a2⟩, ⟨l1, l2⟩, ⟨p1, p2⟩, j, orv, out⟩,
    ⟨pv, rb, oc, et, md⟩⟩, ⟨ge1, ge2⟩, gs, ⟨be1, be2⟩, bs⟩ := w
  rw [shape6 (a := .nat) (b := TCfg), shape7 (a := TG0) (b := TG1),
    shape6 (a := TR) (b := TR) (c := TR), shape5 (a := .nat) (b := .nat) (c := .nat) (d := .nat)
      (e := .nat) pv rb oc et md, sz_nn a1 a2, sz_nn l1 l2, sz_nn p1 p2, sz_nn ge1 ge2,
    sz_nn be1 be2] at hS
  simp only [Ty.enc_nat] at hS
  have hsq : S + 1 ≤ (S + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq2 : (S + 1) * (S + 1) = (S + 1) ^ 2 := (sq _).symm
  have c1 := bl r; have c2 := bl a1; have c3 := bl a2; have c4 := bl l1; have c5 := bl l2
  have c6 := bl p1; have c7 := bl p2; have c8 := bl ge1; have c9 := bl be1; have c10 := bl j
  have c11 := bl pv; have c12 := bl rb; have c13 := bl oc; have c14 := bl et; have c15 := bl md
  have hgb' := NatSize.size_add_le' ge1 be1
  have hB : 1 ≤ S := by omega
  have ha : RB S (a1, a2) := ⟨by show a1.size ≤ S; omega, by show a2.size ≤ S; omega⟩
  have hl : RB S (l1, l2) := ⟨by show l1.size ≤ S; omega, by show l2.size ≤ S; omega⟩
  have hp : RB S (p1, p2) := ⟨by show p1.size ≤ S; omega, by show p2.size ≤ S; omega⟩
  have hgb : ((ge1, ge2).1 + (be1, be2).1).size ≤ S := by show (ge1 + be1).size ≤ S; omega
  have hc := entryCost_le hB (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb (by omega) (by show r.size ≤ S; omega)
  have hRB := entryR_RB hB (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb
  have s5 := size_sum5 pv rb oc et
  dsimp only [EndpointControllerFL.repairAccF, bodySig_cost, EndpointControllerFL.repairAccBody, Tm.cost, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ,
    entryF_cost, entryF_den, ctrF_cost, ctrF_den, mdF_cost, succF_cost, Ty.enc_nat]
  strip_mdata
  generalize entryCost ((false, r, (a1, a2), (l1, l2)), j, (p1, p2), (ge1, ge2), (be1, be2)) = C
    at hc ⊢
  generalize entryR (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) = E at hRB ⊢
  obtain ⟨⟨en, ed⟩, ⟨cn, cd⟩, ⟨on, od⟩⟩ := E
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hRB
  dsimp only at h1a h1b h2a h2b h3a h3b ⊢
  rw [Nat.mul_assoc] at hc
  omega

theorem repairAcc_depth (w : TRA.den) :
    (EndpointControllerFL.repairAccF x).depth w ≤ 40 * (Ty.enc TRA w).size + 100 := by
  suffices h : (EndpointControllerFL.repairAccBody x).depth (Env.one w) ≤ 40 * (Ty.enc TRA w).size + 99 by
    simp only [EndpointControllerFL.repairAccF, bodySig_depth]; omega
  generalize hS : (Ty.enc TRA w).size = S
  obtain ⟨r, ⟨g0, g1, g2, g3, g4, ⟨⟨a1, a2⟩, ⟨l1, l2⟩, ⟨p1, p2⟩, j, orv, out⟩,
    ⟨pv, rb, oc, et, md⟩⟩, ⟨ge1, ge2⟩, gs, ⟨be1, be2⟩, bs⟩ := w
  rw [shape6 (a := .nat) (b := TCfg), shape7 (a := TG0) (b := TG1),
    shape6 (a := TR) (b := TR) (c := TR), shape5 (a := .nat) (b := .nat) (c := .nat) (d := .nat)
      (e := .nat) pv rb oc et md, sz_nn a1 a2, sz_nn l1 l2, sz_nn p1 p2, sz_nn ge1 ge2,
    sz_nn be1 be2] at hS
  simp only [Ty.enc_nat] at hS
  have hsq : S + 1 ≤ (S + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq2 : (S + 1) * (S + 1) = (S + 1) ^ 2 := (sq _).symm
  have c1 := bl r; have c2 := bl a1; have c3 := bl a2; have c4 := bl l1; have c5 := bl l2
  have c6 := bl p1; have c7 := bl p2; have c8 := bl ge1; have c9 := bl be1; have c10 := bl j
  have c11 := bl pv; have c12 := bl rb; have c13 := bl oc; have c14 := bl et; have c15 := bl md
  have hgb' := NatSize.size_add_le' ge1 be1
  have hB : 1 ≤ S := by omega
  have ha : RB S (a1, a2) := ⟨by show a1.size ≤ S; omega, by show a2.size ≤ S; omega⟩
  have hl : RB S (l1, l2) := ⟨by show l1.size ≤ S; omega, by show l2.size ≤ S; omega⟩
  have hp : RB S (p1, p2) := ⟨by show p1.size ≤ S; omega, by show p2.size ≤ S; omega⟩
  have hgb : ((ge1, ge2).1 + (be1, be2).1).size ≤ S := by show (ge1 + be1).size ≤ S; omega
  have hRB := entryR_RB hB (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb
  have hd := entryDepth_le hB (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb (by omega) (by show r.size ≤ S; omega)
  have s5 := size_sum5 pv rb oc et
  dsimp only [EndpointControllerFL.repairAccBody, Tm.depth, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ, entryF_depth, entryF_den,
    ctrF_depth, ctrF_den, mdF_depth, succF_depth]
  strip_mdata
  generalize entryDepth ((false, r, (a1, a2), (l1, l2)), j, (p1, p2), (ge1, ge2), (be1, be2)) = Dp
    at hd ⊢
  generalize entryR (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) = E at hRB ⊢
  obtain ⟨⟨en, ed⟩, ⟨cn, cd⟩, ⟨on, od⟩⟩ := E
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hRB
  dsimp only at h1a h1b h2a h2b h3a h3b ⊢
  simp only [max_le_iff]
  (repeat' apply And.intro) <;> omega

theorem repairAcc_ex (w : TRA.den) :
    Control.Tm'.ex (EndpointControllerFL.repairAccBody x) (Env.one w) ≤ 300 * (Ty.enc TRA w).size + 1000 := by
  generalize hS : (Ty.enc TRA w).size = S
  obtain ⟨r, ⟨g0, g1, g2, g3, g4, ⟨⟨a1, a2⟩, ⟨l1, l2⟩, ⟨p1, p2⟩, j, orv, out⟩,
    ⟨pv, rb, oc, et, md⟩⟩, ⟨ge1, ge2⟩, gs, ⟨be1, be2⟩, bs⟩ := w
  rw [shape6 (a := .nat) (b := TCfg), shape7 (a := TG0) (b := TG1),
    shape6 (a := TR) (b := TR) (c := TR), shape5 (a := .nat) (b := .nat) (c := .nat) (d := .nat)
      (e := .nat) pv rb oc et md, sz_nn a1 a2, sz_nn l1 l2, sz_nn p1 p2, sz_nn ge1 ge2,
    sz_nn be1 be2] at hS
  simp only [Ty.enc_nat] at hS
  have hsq : S + 1 ≤ (S + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq2 : (S + 1) * (S + 1) = (S + 1) ^ 2 := (sq _).symm
  have c1 := bl r; have c2 := bl a1; have c3 := bl a2; have c4 := bl l1; have c5 := bl l2
  have c6 := bl p1; have c7 := bl p2; have c8 := bl ge1; have c9 := bl be1; have c10 := bl j
  have c11 := bl pv; have c12 := bl rb; have c13 := bl oc; have c14 := bl et; have c15 := bl md
  have hgb' := NatSize.size_add_le' ge1 be1
  have hB : 1 ≤ S := by omega
  have ha : RB S (a1, a2) := ⟨by show a1.size ≤ S; omega, by show a2.size ≤ S; omega⟩
  have hl : RB S (l1, l2) := ⟨by show l1.size ≤ S; omega, by show l2.size ≤ S; omega⟩
  have hp : RB S (p1, p2) := ⟨by show p1.size ≤ S; omega, by show p2.size ≤ S; omega⟩
  have hgb : ((ge1, ge2).1 + (be1, be2).1).size ≤ S := by show (ge1 + be1).size ≤ S; omega
  have hRB := entryR_RB hB (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb
  have s5 := size_sum5 pv rb oc et
  have e1 := rb_enc ha; have e2 := rb_enc hl; have e3 := rb_enc hp
  dsimp only [EndpointControllerFL.repairAccBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ, entryF_msize,
    entryF_den, ctrF_msize, ctrF_den, mdF_msize, succF_msize, entryMsize,
    QecReliability.FL.Lib.eqF_msize, countsF_msize, lesserF_msize, greaterF_msize]
  strip_mdata
  generalize entryR (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) = E at hRB ⊢
  obtain ⟨⟨en, ed⟩, ⟨cn, cd⟩, ⟨on, od⟩⟩ := E
  have f1 := rb_enc hRB.1; have f2 := rb_enc hRB.2.1; have f3 := rb_enc hRB.2.2
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hRB
  dsimp only at h1a h1b h2a h2b h3a h3b f1 f2 f3 ⊢
  sz_norm
  simp only [max_le_iff]
  (repeat' apply And.intro) <;> omega

theorem repairAcc_den_sz (w : TRA.den) :
    (Ty.enc TCfg ((EndpointControllerFL.repairAccF x).den w)).size ≤ 40 * (Ty.enc TRA w).size + 400 := by
  generalize hS : (Ty.enc TRA w).size = S
  obtain ⟨r, ⟨g0, g1, g2, g3, g4, ⟨⟨a1, a2⟩, ⟨l1, l2⟩, ⟨p1, p2⟩, j, orv, out⟩,
    ⟨pv, rb, oc, et, md⟩⟩, ⟨ge1, ge2⟩, gs, ⟨be1, be2⟩, bs⟩ := w
  rw [shape6 (a := .nat) (b := TCfg), shape7 (a := TG0) (b := TG1),
    shape6 (a := TR) (b := TR) (c := TR), shape5 (a := .nat) (b := .nat) (c := .nat) (d := .nat)
      (e := .nat) pv rb oc et md, sz_nn a1 a2, sz_nn l1 l2, sz_nn p1 p2, sz_nn ge1 ge2,
    sz_nn be1 be2] at hS
  simp only [Ty.enc_nat] at hS
  have hsq : S + 1 ≤ (S + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq2 : (S + 1) * (S + 1) = (S + 1) ^ 2 := (sq _).symm
  have c1 := bl r; have c2 := bl a1; have c3 := bl a2; have c4 := bl l1; have c5 := bl l2
  have c6 := bl p1; have c7 := bl p2; have c8 := bl ge1; have c9 := bl be1; have c10 := bl j
  have c11 := bl pv; have c12 := bl rb; have c13 := bl oc; have c14 := bl et; have c15 := bl md
  have hgb' := NatSize.size_add_le' ge1 be1
  have hB : 1 ≤ S := by omega
  have ha : RB S (a1, a2) := ⟨by show a1.size ≤ S; omega, by show a2.size ≤ S; omega⟩
  have hl : RB S (l1, l2) := ⟨by show l1.size ≤ S; omega, by show l2.size ≤ S; omega⟩
  have hp : RB S (p1, p2) := ⟨by show p1.size ≤ S; omega, by show p2.size ≤ S; omega⟩
  have hgb : ((ge1, ge2).1 + (be1, be2).1).size ≤ S := by show (ge1 + be1).size ≤ S; omega
  have hRB := entryR_RB hB (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb
  have e1 := rb_enc ha; have e2 := rb_enc hl
  dsimp only at e1 e2
  have cz := ctrR_sz j r false pv rb oc et
  have q1 := Ty.sz_nat_le (j + 1); have q2 := NatSize.size_succ_le j
  simp only [Ty.enc_nat] at q1
  have g4l : (Ty.enc (Ty.list TEnt) g4.1).size + (Ty.enc (Ty.list TEnt) g4.2.1).size +
      (Ty.enc (Ty.list TEnt) g4.2.2.1).size + (Ty.enc (Ty.list TEnt) g4.2.2.2.1).size ≤
      (Ty.enc TG4 g4).size := by
    sz_norm; omega
  dsimp only [EndpointControllerFL.repairAccF, bodySig_den, EndpointControllerFL.repairAccBody, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ, entryF_den,
    ctrF_den, mdF_den, succF_den]
  strip_mdata
  generalize entryR (false, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) = E at hRB ⊢
  obtain ⟨⟨en, ed⟩, ⟨cn, cd⟩, ⟨on, od⟩⟩ := E
  have f2 := rb_enc hRB.2.1; have f3 := rb_enc hRB.2.2
  have mz := md_sz md p2 ed cd od
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hRB
  dsimp only at h1a h1b h2a h2b h3a h3b f2 f3 ⊢
  rw [shape7 (a := TG0) (b := TG1), shape6 (a := Ty.list TEnt) (b := Ty.list TEnt) (c := Ty.list TEnt)
      (d := Ty.list TEnt) (e := Ty.list TEnt) (f := Ty.list TEnt),
    shape6 (a := TR) (b := TR) (c := TR), shape5 (a := .nat) (b := .nat) (c := .nat) (d := .nat)
      (e := .nat), sz_nn a1 a2, sz_nn l1 l2, sz_nn cn cd, Ty.sz_list_cons, sz_nn on od]
  simp only [Ty.enc_nat]
  omega

theorem repairAcc_msize (w : TRA.den) :
    (EndpointControllerFL.repairAccF x).msize w ≤ 340 * (Ty.enc TRA w).size + 1400 := by
  have h := Control.bodySig_msize_le x.repairAcc (EndpointControllerFL.repairAccBody x) w
  have h1 := repairAcc_ex x w
  have h2 := repairAcc_den_sz x w
  show (bodySig x.repairAcc (EndpointControllerFL.repairAccBody x)).msize w ≤ _
  change (Ty.enc TCfg ((bodySig x.repairAcc (EndpointControllerFL.repairAccBody x)).den w)).size ≤ _ at h2
  omega

/-! ## The `.repair` phase -/



theorem repair_cost (a : (TArg TX').den) :
    (EndpointControllerFL.repairF x).cost a ≤ 3000000 * ((Ty.enc (TArg TX') a).size + 1) ^ 2 := by
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, g3, ⟨gr, br, gt, bt, rg, rbd⟩, g5, g6⟩ := a
  have l17 := lit_sz 17 (by omega); have l19 := lit_sz 19 (by omega)
  rcases rg with _ | ⟨ge, gs⟩ <;> rcases rbd with _ | ⟨be, bs⟩
  · dsimp only [EndpointControllerFL.repairF, bodySig_cost, EndpointControllerFL.repairBody, Tm.cost, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ,
      Ty.enc_nat]
    fin_le
  · dsimp only [EndpointControllerFL.repairF, bodySig_cost, EndpointControllerFL.repairBody, Tm.cost, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ,
      Ty.enc_nat]
    fin_le
  · dsimp only [EndpointControllerFL.repairF, bodySig_cost, EndpointControllerFL.repairBody, Tm.cost, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ,
      Ty.enc_nat]
    fin_le
  · have hW := sz_W q r B m X g0 g1 g2 g3 gr br gt bt ge gs be bs g5 g6
    generalize (Ty.enc (TArg TX') (((q, r, B, m), X), (g0, g1, g2, g3,
        (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6))).size = S at hW hsq ⊢
    dsimp only [EndpointControllerFL.repairF, bodySig_cost, EndpointControllerFL.repairBody, Tm.cost, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
    strip_mdata
    rw [(min_eq_left (repairAcc_cost x _)).symm]
    generalize (Ty.enc TRA (r, (g0, g1, g2, g3, (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6), ge,
      gs, be, bs)).size = SW at hW ⊢
    have hq := sq_bound SW S (by omega)
    omega

theorem repair_depth (a : (TArg TX').den) :
    (EndpointControllerFL.repairF x).depth a ≤ 100 * (Ty.enc (TArg TX') a).size + 600 := by
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, g3, ⟨gr, br, gt, bt, rg, rbd⟩, g5, g6⟩ := a
  rcases rg with _ | ⟨ge, gs⟩ <;> rcases rbd with _ | ⟨be, bs⟩
  · dsimp only [EndpointControllerFL.repairF, bodySig_depth, EndpointControllerFL.repairBody, Tm.depth, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
    fin_le
  · dsimp only [EndpointControllerFL.repairF, bodySig_depth, EndpointControllerFL.repairBody, Tm.depth, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
    fin_le
  · dsimp only [EndpointControllerFL.repairF, bodySig_depth, EndpointControllerFL.repairBody, Tm.depth, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
    fin_le
  · have hW := sz_W q r B m X g0 g1 g2 g3 gr br gt bt ge gs be bs g5 g6
    generalize (Ty.enc (TArg TX') (((q, r, B, m), X), (g0, g1, g2, g3,
        (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6))).size = S at hW ⊢
    dsimp only [EndpointControllerFL.repairF, bodySig_depth, EndpointControllerFL.repairBody, Tm.depth, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
    strip_mdata
    rw [(min_eq_left (repairAcc_depth x _)).symm]
    generalize (Ty.enc TRA (r, (g0, g1, g2, g3, (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6), ge,
      gs, be, bs)).size = SW at hW ⊢
    simp only [max_self, Nat.zero_max, Nat.max_zero]
    omega

theorem repair_ex (a : (TArg TX').den) :
    Control.Tm'.ex (EndpointControllerFL.repairBody x) (Env.one a) ≤ 1000 * (Ty.enc (TArg TX') a).size + 10000 := by
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, g3, ⟨gr, br, gt, bt, rg, rbd⟩, g5, g6⟩ := a
  rcases rg with _ | ⟨ge, gs⟩ <;> rcases rbd with _ | ⟨be, bs⟩
  · dsimp only [EndpointControllerFL.repairBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
    fin_le
  · dsimp only [EndpointControllerFL.repairBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
    fin_le
  · dsimp only [EndpointControllerFL.repairBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
    fin_le
  · have hW := sz_W q r B m X g0 g1 g2 g3 gr br gt bt ge gs be bs g5 g6
    generalize (Ty.enc (TArg TX') (((q, r, B, m), X), (g0, g1, g2, g3,
        (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6))).size = S at hW ⊢
    dsimp only [EndpointControllerFL.repairBody, Control.Tm'.ex, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
    strip_mdata
    simp only [max_le_iff]
    (repeat' apply And.intro) <;>
    first
      | (dsimp only [Tm.msize]; omega)
      | (rw [(min_eq_left (repairAcc_msize x _)).symm]
         generalize (Ty.enc TRA (r, (g0, g1, g2, g3, (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6),
           ge, gs, be, bs)).size = SW at hW ⊢
         omega)
      | (refine le_trans (Control.Tm'.msize_le_ex _ _) ?_
         dsimp only [Control.Tm'.ex, Tm.msize, Tm.den, Env.one, endpoint_get_zero, endpoint_get_succ]
         generalize (Ty.enc TRA (r, (g0, g1, g2, g3, (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6),
           ge, gs, be, bs)).size = SW at hW ⊢
         fin_le)

end QecReliability.LatentMachine.EndpointControllerBounds

