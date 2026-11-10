import Trans.BoundsStep.PhaseA

/-!
# Trans.BoundsStep.PhaseFetch: the `.fetch` phase (`fop0F … fop6F`, `fetchF`)

* `mapFst_bounds`: the library `map fst` used by `fop4` (cost `14·size`, depth `size + 1`,
  msize `size`, sizes of the list of entries).
* `fopK_cost/_depth/_msize` at every argument `w = (op, (ctx, t))`: constant cost/depth except
  `fop4` (linear in the size of `t.trialsRev`); `msize ≤ 3·size(w) + 100` (the result is a
  rearrangement of the fields of `w`).
* `fetch_cost/_depth/_ex` at every argument `a` (`S = size a`): linear in `S`.

In `fetch`, the opcode case is selected by an `ite` chain; each case is closed by rewriting
`fopK.(cost|depth|msize) W` to `min _ bound` (`rw [(min_eq_left (fopK_… x _)).symm]`), which
avoids naming the argument `W` built by the body.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (TR TEnt TKey TPre TOp TG0 TG1 TG2 TG3 TG4 TG5 TG6 TCfg TCtx
  TArg TFA bodySig bodySig_cost bodySig_depth bodySig_msize bodySig_den)
open QecReliability.Trans.Bounds (shape2 shape3 shape4 shape5 shape6 shape7 shape8)

private theorem phaseFetch_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem phaseFetch_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable {TX' : Ty} (x : Control.Ix TX')

/-! ## `map fst` -/

theorem mapFst_cost (i j : ℕ) (xs : List (Ty.den TEnt)) :
    (mapF (Control.fstEF i) j).cost xs = 14 * xs.length + 10 := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    have e4 : (Control.fstEF i).cost e = 4 := rfl
    simp only [mapF_cost, List.map_cons, List.sum_cons, List.length_cons, e4] at ih ⊢
    omega

theorem mapFst_msize_aux (i : ℕ) (xs : List (Ty.den TEnt)) :
    (Ty.enc (.list .nat) (xs.map (Control.fstEF i).den)).size ≤ (Ty.enc (.list TEnt) xs).size := by
  induction xs with
  | nil => exact le_refl _
  | cons e es ih =>
    obtain ⟨u, v⟩ := e
    rw [List.map_cons, Ty.sz_list_cons, Ty.sz_list_cons, sz_nn u v]
    have : (Control.fstEF i).den (u, v) = u := rfl
    rw [this]
    simp only [Ty.enc_nat]
    have := enc_pos v
    omega

theorem mapFst_bounds (i j : ℕ) (xs : List (Ty.den TEnt)) :
    (mapF (Control.fstEF i) j).cost xs ≤ 14 * (Ty.enc (.list TEnt) xs).size ∧
      (mapF (Control.fstEF i) j).depth xs ≤ (Ty.enc (.list TEnt) xs).size + 1 ∧
      (mapF (Control.fstEF i) j).msize xs ≤ (Ty.enc (.list TEnt) xs).size := by
  have hl := Ty.length_le_sz TEnt xs
  refine ⟨?_, ?_, ?_⟩
  · rw [mapFst_cost]; omega
  · have hm := maxOf_le (Control.fstEF i).depth xs 1 (fun _ _ => le_refl 1)
    simp only [mapF_depth]
    omega
  · have hm := maxOf_le (Control.fstEF i).msize xs 0 (fun _ _ => le_refl 0)
    have h2 := mapFst_msize_aux i xs
    simp only [mapF_msize]
    omega

/-! ## Opcode cases -/

section Fops

theorem fop0_cost (w : (TFA TX').den) : (Control.fop0F x).cost w ≤ 2000 := by
  dsimp only [Control.fop0F, bodySig_cost, Control.fop0Body, Tm.cost, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
  fin_le

theorem fop1_cost (w : (TFA TX').den) : (Control.fop1F x).cost w ≤ 2000 := by
  have l2 := lit_sz 2 (by omega)
  dsimp only [Control.fop1F, bodySig_cost, Control.fop1Body, Tm.cost, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ, Ty.enc_nat]
  fin_le

theorem fop2_cost (w : (TFA TX').den) : (Control.fop2F x).cost w ≤ 2000 := by
  dsimp only [Control.fop2F, bodySig_cost, Control.fop2Body, Tm.cost, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ, Ty.enc_nat]
  fin_le

theorem fop3_cost (w : (TFA TX').den) : (Control.fop3F x).cost w ≤ 2000 := by
  have l5 := lit_sz 5 (by omega); have l7 := lit_sz 7 (by omega)
  dsimp only [Control.fop3F, bodySig_cost, Control.fop3Body, Tm.cost, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ, Ty.enc_nat]
  fin_le

theorem fop4_cost (w : (TFA TX').den) :
    (Control.fop4F x).cost w ≤ 14 * (Ty.enc (.list TEnt) w.2.2.2.2.1.2.2.2.1).size + 2000 := by
  have l8 := lit_sz 8 (by omega)
  have hm := (mapFst_bounds x.fstE x.mapFst w.2.2.2.2.1.2.2.2.1).1
  dsimp only [Control.fop4F, bodySig_cost, Control.fop4Body, Tm.cost, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ, Ty.enc_nat]
  fin_le

theorem fop5_cost (w : (TFA TX').den) : (Control.fop5F x).cost w ≤ 2000 := by
  dsimp only [Control.fop5F, bodySig_cost, Control.fop5Body, Tm.cost, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
  fin_le

theorem fop6_cost (w : (TFA TX').den) : (Control.fop6F x).cost w ≤ 2000 := by
  have l12 := lit_sz 12 (by omega)
  dsimp only [Control.fop6F, bodySig_cost, Control.fop6Body, Tm.cost, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ, Ty.enc_nat]
  fin_le

theorem fop0_depth (w : (TFA TX').den) : (Control.fop0F x).depth w ≤ 1 := by
  dsimp only [Control.fop0F, bodySig_depth, Control.fop0Body, Tm.depth, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
  fin_le

theorem fop1_depth (w : (TFA TX').den) : (Control.fop1F x).depth w ≤ 1 := by
  dsimp only [Control.fop1F, bodySig_depth, Control.fop1Body, Tm.depth, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
  fin_le

theorem fop2_depth (w : (TFA TX').den) : (Control.fop2F x).depth w ≤ 1 := by
  dsimp only [Control.fop2F, bodySig_depth, Control.fop2Body, Tm.depth, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
  fin_le

theorem fop3_depth (w : (TFA TX').den) : (Control.fop3F x).depth w ≤ 1 := by
  dsimp only [Control.fop3F, bodySig_depth, Control.fop3Body, Tm.depth, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
  fin_le

theorem fop4_depth (w : (TFA TX').den) :
    (Control.fop4F x).depth w ≤ (Ty.enc (.list TEnt) w.2.2.2.2.1.2.2.2.1).size + 2 := by
  have hm := (mapFst_bounds x.fstE x.mapFst w.2.2.2.2.1.2.2.2.1).2.1
  dsimp only [Control.fop4F, bodySig_depth, Control.fop4Body, Tm.depth, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
  fin_le

theorem fop5_depth (w : (TFA TX').den) : (Control.fop5F x).depth w ≤ 1 := by
  dsimp only [Control.fop5F, bodySig_depth, Control.fop5Body, Tm.depth, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
  fin_le

theorem fop6_depth (w : (TFA TX').den) : (Control.fop6F x).depth w ≤ 1 := by
  dsimp only [Control.fop6F, bodySig_depth, Control.fop6Body, Tm.depth, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
  fin_le

theorem fop0_msize (w : (TFA TX').den) :
    (Control.fop0F x).msize w ≤ 3 * (Ty.enc (TFA TX') w).size + 100 := by
  have h := Control.bodySig_msize_le x.fop0 Control.fop0Body w
  have hx : Control.Tm'.ex (Control.fop0Body (TX := TX')) (Env.one w) ≤ 0 := by
    dsimp only [Control.fop0Body, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]; fin_le
  have hd : (Ty.enc TCfg ((bodySig x.fop0 Control.fop0Body).den w)).size ≤
      2 * (Ty.enc (TFA TX') w).size + 100 := by
    have z0 : (Enc.nat 0).size = 1 := Enc.nat_zero_size
    dsimp only [bodySig_den, Control.fop0Body, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
    sz_norm
    omega
  show (bodySig x.fop0 Control.fop0Body).msize w ≤ _
  omega

theorem fop1_msize (w : (TFA TX').den) :
    (Control.fop1F x).msize w ≤ 3 * (Ty.enc (TFA TX') w).size + 100 := by
  have h := Control.bodySig_msize_le x.fop1 Control.fop1Body w
  have hx : Control.Tm'.ex (Control.fop1Body (TX := TX')) (Env.one w) ≤ 0 := by
    dsimp only [Control.fop1Body, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]; fin_le
  have hd : (Ty.enc TCfg ((bodySig x.fop1 Control.fop1Body).den w)).size ≤
      2 * (Ty.enc (TFA TX') w).size + 100 := by
    have z0 : (Enc.nat 0).size = 1 := Enc.nat_zero_size
    have l2 := lit_sz 2 (by omega)
    dsimp only [bodySig_den, Control.fop1Body, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
    sz_norm
    omega
  show (bodySig x.fop1 Control.fop1Body).msize w ≤ _
  omega

theorem fop2_msize (w : (TFA TX').den) :
    (Control.fop2F x).msize w ≤ 3 * (Ty.enc (TFA TX') w).size + 100 := by
  have h := Control.bodySig_msize_le x.fop2 Control.fop2Body w
  have z1 := enc_bitNat_le false w.2.1.1.2.2.1
  have z2 := enc_bitNat_le true (bitNat false w.2.1.1.2.2.1)
  have hx : Control.Tm'.ex (Control.fop2Body (TX := TX')) (Env.one w) ≤
      (Enc.nat w.2.1.1.2.2.1).size + 10 := by
    dsimp only [Control.fop2Body, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ, Ty.enc_nat]; fin_le
  have hd : (Ty.enc TCfg ((bodySig x.fop2 Control.fop2Body).den w)).size ≤
      2 * (Ty.enc (TFA TX') w).size + 90 := by
    have z0 : (Enc.nat 0).size = 1 := Enc.nat_zero_size
    have l1 : (Enc.nat 1).size = 5 := Enc.nat_one_size
    dsimp only [bodySig_den, Control.fop2Body, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
    split_ifs <;> sz_norm <;> (try rw [Ty.sz_list_nil]) <;> omega
  have hB : (Enc.nat w.2.1.1.2.2.1).size ≤ (Ty.enc (TFA TX') w).size := by
    sz_norm; omega
  show (bodySig x.fop2 Control.fop2Body).msize w ≤ _
  omega

theorem fop3_msize (w : (TFA TX').den) :
    (Control.fop3F x).msize w ≤ 3 * (Ty.enc (TFA TX') w).size + 100 := by
  have h := Control.bodySig_msize_le x.fop3 Control.fop3Body w
  have hx : Control.Tm'.ex (Control.fop3Body (TX := TX')) (Env.one w) ≤ 0 := by
    dsimp only [Control.fop3Body, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]; fin_le
  have hd : (Ty.enc TCfg ((bodySig x.fop3 Control.fop3Body).den w)).size ≤
      2 * (Ty.enc (TFA TX') w).size + 100 := by
    have z0 : (Enc.nat 0).size = 1 := Enc.nat_zero_size
    have l5 := lit_sz 5 (by omega); have l7 := lit_sz 7 (by omega)
    dsimp only [bodySig_den, Control.fop3Body, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
    split_ifs <;> sz_norm <;> omega
  show (bodySig x.fop3 Control.fop3Body).msize w ≤ _
  omega

theorem fop4_msize (w : (TFA TX').den) :
    (Control.fop4F x).msize w ≤ 3 * (Ty.enc (TFA TX') w).size + 100 := by
  have h := Control.bodySig_msize_le x.fop4 (Control.fop4Body x) w
  have hm := (mapFst_bounds x.fstE x.mapFst w.2.2.2.2.1.2.2.2.1).2.2
  have hm2 := mapFst_msize_aux x.fstE w.2.2.2.2.1.2.2.2.1
  have hx : Control.Tm'.ex (Control.fop4Body x) (Env.one w) ≤
      (Ty.enc (.list TEnt) w.2.2.2.2.1.2.2.2.1).size := by
    dsimp only [Control.fop4Body, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]; fin_le
  have hd : (Ty.enc TCfg ((bodySig x.fop4 (Control.fop4Body x)).den w)).size ≤
      2 * (Ty.enc (TFA TX') w).size + 50 := by
    have l8 := lit_sz 8 (by omega)
    dsimp only [bodySig_den, Control.fop4Body, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ, mapF_den]
    sz_norm
    sz_norm at hm2
    omega
  have hT : (Ty.enc (.list TEnt) w.2.2.2.2.1.2.2.2.1).size ≤ (Ty.enc (TFA TX') w).size := by
    sz_norm; omega
  show (bodySig x.fop4 (Control.fop4Body x)).msize w ≤ _
  omega

theorem fop5_msize (w : (TFA TX').den) :
    (Control.fop5F x).msize w ≤ 3 * (Ty.enc (TFA TX') w).size + 100 := by
  have h := Control.bodySig_msize_le x.fop5 Control.fop5Body w
  have hx : Control.Tm'.ex (Control.fop5Body (TX := TX')) (Env.one w) ≤ 0 := by
    dsimp only [Control.fop5Body, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]; fin_le
  have hd : (Ty.enc TCfg ((bodySig x.fop5 Control.fop5Body).den w)).size ≤
      2 * (Ty.enc (TFA TX') w).size + 100 := by
    dsimp only [bodySig_den, Control.fop5Body, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
    split_ifs <;> sz_norm <;> (try rw [Ty.sz_list_cons]) <;> (try sz_norm) <;> omega
  show (bodySig x.fop5 Control.fop5Body).msize w ≤ _
  omega

theorem fop6_msize (w : (TFA TX').den) :
    (Control.fop6F x).msize w ≤ 3 * (Ty.enc (TFA TX') w).size + 100 := by
  have h := Control.bodySig_msize_le x.fop6 Control.fop6Body w
  have hx : Control.Tm'.ex (Control.fop6Body (TX := TX')) (Env.one w) ≤ 0 := by
    dsimp only [Control.fop6Body, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]; fin_le
  have hd : (Ty.enc TCfg ((bodySig x.fop6 Control.fop6Body).den w)).size ≤
      2 * (Ty.enc (TFA TX') w).size + 100 := by
    have l12 := lit_sz 12 (by omega)
    dsimp only [bodySig_den, Control.fop6Body, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
    sz_norm
    omega
  show (bodySig x.fop6 Control.fop6Body).msize w ≤ _
  omega

end Fops

/-! ## fetch -/

set_option maxHeartbeats 2000000 in
theorem fetch_cost (a : (TArg TX').den) :
    (Control.fetchF x).cost a ≤ 1000 * (Ty.enc (TArg TX') a).size + 20000 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, ⟨pc, code, good, coef, rep, scale, ne, tg⟩, g1,
    ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape8 (a := .nat), shape7 (a := Ty.list TEnt)] at hS
  have l1 := lit_sz 1 (by omega); have l2 := lit_sz 2 (by omega); have l3 := lit_sz 3 (by omega)
  have l4 := lit_sz 4 (by omega); have l5 := lit_sz 5 (by omega); have l19 := lit_sz 19 (by omega)
  rcases code with _ | ⟨⟨tag, flag, arg⟩, rest⟩
  · dsimp only [Control.fetchF, bodySig_cost, Control.fetchBody, Tm.cost, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ,
      Ty.enc_nat]
    fin_le
  · rw [Ty.sz_list_cons, shape3 (a := .nat) (b := .bool) (c := .nat)] at hS
    simp only [Ty.enc_nat] at hS
    have bt := bl tag
    dsimp only [Control.fetchF, bodySig_cost, Control.fetchBody, Tm.cost, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ,
      Ty.enc_nat, eqF_cost, eqF_den]
    split_ifs <;>
    (first
      | rw [(min_eq_left (fop0_cost x _)).symm]
      | rw [(min_eq_left (fop1_cost x _)).symm]
      | rw [(min_eq_left (fop2_cost x _)).symm]
      | rw [(min_eq_left (fop3_cost x _)).symm]
      | rw [(min_eq_left (fop4_cost x _)).symm]
      | rw [(min_eq_left (fop5_cost x _)).symm]
      | rw [(min_eq_left (fop6_cost x _)).symm]) <;>
    (try dsimp only) <;> strip_mdata <;> omega

set_option maxHeartbeats 2000000 in
theorem fetch_depth (a : (TArg TX').den) :
    (Control.fetchF x).depth a ≤ (Ty.enc (TArg TX') a).size + 20 := by
  suffices h : (Control.fetchBody x).depth (Env.one a) ≤ (Ty.enc (TArg TX') a).size + 19 by
    simp only [Control.fetchF, bodySig_depth]; omega
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, ⟨pc, code, good, coef, rep, scale, ne, tg⟩, g1,
    ⟨cr, ps, pd, tr, sel, si, sf⟩, g3, g4, g5, g6⟩ := a
  rw [sz_arg7, shape8 (a := .nat), shape7 (a := Ty.list TEnt)] at hS
  have l1 := lit_sz 1 (by omega); have l2 := lit_sz 2 (by omega); have l3 := lit_sz 3 (by omega)
  have l4 := lit_sz 4 (by omega); have l5 := lit_sz 5 (by omega)
  rcases code with _ | ⟨⟨tag, flag, arg⟩, rest⟩
  · dsimp only [Control.fetchBody, Tm.depth, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
    fin_le
  · rw [Ty.sz_list_cons, shape3 (a := .nat) (b := .bool) (c := .nat)] at hS
    simp only [Ty.enc_nat] at hS
    have bt := bl tag
    dsimp only [Control.fetchBody, Tm.depth, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ, eqF_depth, eqF_den]
    split_ifs <;>
    (first
      | rw [(min_eq_left (fop0_depth x _)).symm]
      | rw [(min_eq_left (fop1_depth x _)).symm]
      | rw [(min_eq_left (fop2_depth x _)).symm]
      | rw [(min_eq_left (fop3_depth x _)).symm]
      | rw [(min_eq_left (fop4_depth x _)).symm]
      | rw [(min_eq_left (fop5_depth x _)).symm]
      | rw [(min_eq_left (fop6_depth x _)).symm]) <;>
    (try dsimp only) <;> fin_le

set_option maxHeartbeats 4000000 in
theorem fetch_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.fetchBody x) (Env.one a) ≤ 10 * (Ty.enc (TArg TX') a).size + 500 := by
  generalize hS : (Ty.enc (TArg TX') a).size = S
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, ⟨pc, code, good, coef, rep, scale, ne, tg⟩, g1, g2, g3, g4, g5,
    g6⟩ := a
  have l1 := lit_sz 1 (by omega); have l2 := lit_sz 2 (by omega); have l3 := lit_sz 3 (by omega)
  have l4 := lit_sz 4 (by omega); have l5 := lit_sz 5 (by omega)
  rcases code with _ | ⟨⟨tag, flag, arg⟩, rest⟩
  · dsimp only [Control.fetchBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
    fin_le
  · have htag : (Enc.nat tag).size ≤ S := by
      rw [← hS, sz_arg7, shape8 (a := .nat), Ty.sz_list_cons,
        shape3 (a := .nat) (b := .bool) (c := .nat)]
      simp only [Ty.enc_nat]
      omega
    have bt := bl tag
    dsimp only [Control.fetchBody, Control.Tm'.ex, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
    split_ifs <;> simp only [max_le_iff] <;> (repeat' apply And.intro) <;>
    first
      | (dsimp only [Tm.msize]; omega)
      | (refine le_trans (Control.Tm'.msize_le_ex _ _) ?_
         dsimp only [Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]
         rw [← hS]
         sz_norm
         (try rw [Ty.sz_list_cons])
         (try sz_norm)
         omega)
      | (rw [(min_eq_left (fop0_msize x _)).symm]
         (try dsimp only [Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]); rw [← hS]; sz_norm; (try rw [Ty.sz_list_cons]); (try sz_norm)
         omega)
      | (rw [(min_eq_left (fop1_msize x _)).symm]
         (try dsimp only [Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]); rw [← hS]; sz_norm; (try rw [Ty.sz_list_cons]); (try sz_norm)
         omega)
      | (rw [(min_eq_left (fop2_msize x _)).symm]
         (try dsimp only [Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]); rw [← hS]; sz_norm; (try rw [Ty.sz_list_cons]); (try sz_norm)
         omega)
      | (rw [(min_eq_left (fop3_msize x _)).symm]
         (try dsimp only [Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]); rw [← hS]; sz_norm; (try rw [Ty.sz_list_cons]); (try sz_norm)
         omega)
      | (rw [(min_eq_left (fop4_msize x _)).symm]
         (try dsimp only [Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]); rw [← hS]; sz_norm; (try rw [Ty.sz_list_cons]); (try sz_norm)
         omega)
      | (rw [(min_eq_left (fop5_msize x _)).symm]
         (try dsimp only [Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]); rw [← hS]; sz_norm; (try rw [Ty.sz_list_cons]); (try sz_norm)
         omega)
      | (rw [(min_eq_left (fop6_msize x _)).symm]
         (try dsimp only [Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ]); rw [← hS]; sz_norm; (try rw [Ty.sz_list_cons]); (try sz_norm)
         omega)
      | (clear hS
         dsimp only [Tm.msize, Tm.den, Env.one, phaseFetch_get_zero, phaseFetch_get_succ, eqF_msize, eqF_den]
         (try sz_norm)
         generalize Nat.size 1 = n1 at l1 ⊢; generalize (Enc.nat 1).size = e1 at l1 ⊢
         generalize Nat.size 2 = n2 at l2 ⊢; generalize (Enc.nat 2).size = e2 at l2 ⊢
         generalize Nat.size 3 = n3 at l3 ⊢; generalize (Enc.nat 3).size = e3 at l3 ⊢
         generalize Nat.size 4 = n4 at l4 ⊢; generalize (Enc.nat 4).size = e4 at l4 ⊢
         generalize Nat.size 5 = n5 at l5 ⊢; generalize (Enc.nat 5).size = e5 at l5 ⊢
         (try split_ifs) <;> (try simp only [max_le_iff]) <;> (repeat' apply And.intro) <;> omega)

end QecReliability.Trans.BoundsStep
