import Trans.BoundsStep.PhaseA

/-!
# Trans.BoundsStep.PhaseRepair: the `.repair` phase (`repairAccF`, `repairF`)

One repair step `repairAccF` at `w = (r, cfg, g, gs, b, bs)` (`Sw = size w`): with every bit
length `≤ Sw` (`RB Sw`, `FL/Lib/LinearRepair.lean`), `entryCost_le` gives the quadratic cost
`O((Sw+1)²)` (two multiplications), `entryDepth_le` the linear depth; the counters (`ctrF`), the
running maximum (`mdF`) and the successor are linear. The result is linear in `Sw` (its new
ratios have bit length `≤ Sw`), so `msize ≤ K·Sw + K'`. `repairF` calls `repairAccF` once at an
argument of size `≤ 2·S` (the two lists' heads/tails are counted twice).

Entry results are handled with `generalize` (matching up to definitional unfolding), which
avoids syntactic mismatches of the tuples built by `Tm.den`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.FL.Lib.LinearRepairFL (entryF entryF_cost entryF_den entryF_depth
  entryF_msize entryCost entryDepth entryMsize entryR ctrF ctrF_cost ctrF_den ctrF_depth
  ctrF_msize ctrR mdF mdF_cost mdF_den mdF_depth mdF_msize RB entryR_RB entryCost_le
  entryDepth_le countsF_msize lesserF_msize greaterF_msize max4_size_le)
open QecReliability.Trans.Control (TR TEnt TKey TPre TCtl TFrame TOp TG0 TG1 TG2 TG3 TG4 TG5 TG6
  TCfg TCtx TArg TRA bodySig bodySig_cost bodySig_depth bodySig_msize bodySig_den)
open QecReliability.Trans.Bounds (shape2 shape3 shape4 shape5 shape6 shape7 shape8)

private theorem phaseRepair_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem phaseRepair_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

variable {TX' : Ty} (x : Control.Ix TX')

theorem size_sum5 (a b c d : ℕ) : (a + b + c + d + 2).size ≤ a.size + b.size + c.size + d.size + 6 := by
  have h1 := NatSize.size_add_le' a b
  have h2 := NatSize.size_add_le' (a + b) c
  have h3 := NatSize.size_add_le' (a + b + c) d
  have h4 := NatSize.size_add_le' (a + b + c + d) 2
  have h5 : (2 : ℕ).size ≤ 2 := NatSize.size_le_self 2
  omega

/-- Sizes of the counters after one step. -/
theorem ctrR_sz (j r : ℕ) (s : Bool) (pv rb oc et : ℕ) :
    (Enc.nat (ctrR j r s pv rb oc et).1).size + (Enc.nat (ctrR j r s pv rb oc et).2.1).size +
      (Enc.nat (ctrR j r s pv rb oc et).2.2.1).size + (Enc.nat (ctrR j r s pv rb oc et).2.2.2).size ≤
      4 * (pv.size + rb.size + oc.size + et.size) + 60 := by
  have f : ∀ u k : ℕ, k ≤ 2 → (Enc.nat (u + k)).size ≤ 4 * u.size + 13 := fun u k hk => by
    have h1 := Ty.sz_nat_le (u + k)
    have h2 := NatSize.size_add_le' u k
    have h3 : k.size ≤ k := NatSize.size_le_self k
    simp only [Ty.enc_nat] at h1
    omega
  unfold ctrR
  dsimp only
  have e1 := f pv 1 (by omega)
  have e2 := f rb (if j = 0 ∨ j = r then 0 else 1) (by split_ifs <;> omega)
  have e3 := f oc ((if j = 0 then 0 else 1) + (if s then 1 else 0)) (by split_ifs <;> omega)
  have e4 := f et (if j = 0 then 1 else 2) (by split_ifs <;> omega)
  rw [Nat.add_assoc oc] at *
  omega

theorem md_sz (a b c d e : ℕ) :
    (Enc.nat (max a (max b (max c (max d e))))).size ≤
      4 * (a.size + b.size + c.size + d.size + e.size) + 1 := by
  have h1 := Ty.sz_nat_le (max a (max b (max c (max d e))))
  have h2 := max4_size_le a b c d e
  simp only [Ty.enc_nat] at h1
  omega

/-- `RB B p` in terms of the encoded size of the ratio. -/
theorem rb_enc {B : ℕ} {p : ℕ × ℕ} (h : RB B p) :
    (Enc.nat p.1).size + (Enc.nat p.2).size ≤ 8 * B + 2 := by
  have h1 := Ty.sz_nat_le p.1
  have h2 := Ty.sz_nat_le p.2
  simp only [Ty.enc_nat] at h1 h2
  have := h.1; have := h.2
  omega

/-! ## One repair step -/

theorem repairAcc_cost (w : TRA.den) :
    (Control.repairAccF x).cost w ≤ 20000 * ((Ty.enc TRA w).size + 1) ^ 2 := by
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
  have hc := entryCost_le hB (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb (by omega) (by show r.size ≤ S; omega)
  have hRB := entryR_RB hB (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb
  have s5 := size_sum5 pv rb oc et
  dsimp only [Control.repairAccF, bodySig_cost, Control.repairAccBody, Tm.cost, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ,
    entryF_cost, entryF_den, ctrF_cost, ctrF_den, mdF_cost, succF_cost, Ty.enc_nat]
  strip_mdata
  generalize entryCost ((true, r, (a1, a2), (l1, l2)), j, (p1, p2), (ge1, ge2), (be1, be2)) = C
    at hc ⊢
  generalize entryR (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) = E at hRB ⊢
  obtain ⟨⟨en, ed⟩, ⟨cn, cd⟩, ⟨on, od⟩⟩ := E
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hRB
  dsimp only at h1a h1b h2a h2b h3a h3b ⊢
  rw [Nat.mul_assoc] at hc
  omega

theorem repairAcc_depth (w : TRA.den) :
    (Control.repairAccF x).depth w ≤ 40 * (Ty.enc TRA w).size + 100 := by
  suffices h : (Control.repairAccBody x).depth (Env.one w) ≤ 40 * (Ty.enc TRA w).size + 99 by
    simp only [Control.repairAccF, bodySig_depth]; omega
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
  have hRB := entryR_RB hB (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb
  have hd := entryDepth_le hB (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb (by omega) (by show r.size ≤ S; omega)
  have s5 := size_sum5 pv rb oc et
  dsimp only [Control.repairAccBody, Tm.depth, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ, entryF_depth, entryF_den,
    ctrF_depth, ctrF_den, mdF_depth, succF_depth]
  strip_mdata
  generalize entryDepth ((true, r, (a1, a2), (l1, l2)), j, (p1, p2), (ge1, ge2), (be1, be2)) = Dp
    at hd ⊢
  generalize entryR (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) = E at hRB ⊢
  obtain ⟨⟨en, ed⟩, ⟨cn, cd⟩, ⟨on, od⟩⟩ := E
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hRB
  dsimp only at h1a h1b h2a h2b h3a h3b ⊢
  simp only [max_le_iff]
  (repeat' apply And.intro) <;> omega

theorem repairAcc_ex (w : TRA.den) :
    Control.Tm'.ex (Control.repairAccBody x) (Env.one w) ≤ 300 * (Ty.enc TRA w).size + 1000 := by
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
  have hRB := entryR_RB hB (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb
  have s5 := size_sum5 pv rb oc et
  have e1 := rb_enc ha; have e2 := rb_enc hl; have e3 := rb_enc hp
  dsimp only [Control.repairAccBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ, entryF_msize,
    entryF_den, ctrF_msize, ctrF_den, mdF_msize, succF_msize, entryMsize,
    QecReliability.FL.Lib.eqF_msize, countsF_msize, lesserF_msize, greaterF_msize]
  strip_mdata
  generalize entryR (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) = E at hRB ⊢
  obtain ⟨⟨en, ed⟩, ⟨cn, cd⟩, ⟨on, od⟩⟩ := E
  have f1 := rb_enc hRB.1; have f2 := rb_enc hRB.2.1; have f3 := rb_enc hRB.2.2
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hRB
  dsimp only at h1a h1b h2a h2b h3a h3b f1 f2 f3 ⊢
  sz_norm
  simp only [max_le_iff]
  (repeat' apply And.intro) <;> omega

theorem repairAcc_den_sz (w : TRA.den) :
    (Ty.enc TCfg ((Control.repairAccF x).den w)).size ≤ 40 * (Ty.enc TRA w).size + 400 := by
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
  have hRB := entryR_RB hB (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) ha hl
    hp hgb
  have e1 := rb_enc ha; have e2 := rb_enc hl
  dsimp only at e1 e2
  have cz := ctrR_sz j r true pv rb oc et
  have q1 := Ty.sz_nat_le (j + 1); have q2 := NatSize.size_succ_le j
  simp only [Ty.enc_nat] at q1
  have g4l : (Ty.enc (Ty.list TEnt) g4.1).size + (Ty.enc (Ty.list TEnt) g4.2.1).size +
      (Ty.enc (Ty.list TEnt) g4.2.2.1).size + (Ty.enc (Ty.list TEnt) g4.2.2.2.1).size ≤
      (Ty.enc TG4 g4).size := by
    sz_norm; omega
  dsimp only [Control.repairAccF, bodySig_den, Control.repairAccBody, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ, entryF_den,
    ctrF_den, mdF_den, succF_den]
  strip_mdata
  generalize entryR (true, r, (a1, a2), (l1, l2)) j (p1, p2) (ge1, ge2) (be1, be2) = E at hRB ⊢
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
    (Control.repairAccF x).msize w ≤ 340 * (Ty.enc TRA w).size + 1400 := by
  have h := Control.bodySig_msize_le x.repairAcc (Control.repairAccBody x) w
  have h1 := repairAcc_ex x w
  have h2 := repairAcc_den_sz x w
  show (bodySig x.repairAcc (Control.repairAccBody x)).msize w ≤ _
  change (Ty.enc TCfg ((bodySig x.repairAcc (Control.repairAccBody x)).den w)).size ≤ _ at h2
  omega

/-! ## The `.repair` phase -/

theorem sq_bound (SW S : ℕ) (h : SW ≤ 2 * S + 10) :
    20000 * (SW + 1) ^ 2 + 100000 ≤ 3000000 * (S + 1) ^ 2 := by
  have h1 : SW + 1 ≤ 11 * (S + 1) := by omega
  have h2 : (SW + 1) ^ 2 ≤ (11 * (S + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : (11 * (S + 1)) ^ 2 = 121 * (S + 1) ^ 2 := by ring
  have h4 : 1 ≤ (S + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The argument of the repair step built by `repairBody` is at most twice the phase argument. -/
theorem sz_W (q r B m : ℕ) (X : TX'.den) (g0 : TG0.den) (g1 : TG1.den) (g2 : TG2.den)
    (g3 : TG3.den) (gr br gt bt : List TEnt.den) (ge : TEnt.den) (gs : List TEnt.den)
    (be : TEnt.den) (bs : List TEnt.den) (g5 : TG5.den) (g6 : TG6.den) :
    (Ty.enc TRA (r, (g0, g1, g2, g3, (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6), ge, gs, be,
      bs)).size ≤
      2 * (Ty.enc (TArg TX') (((q, r, B, m), X), (g0, g1, g2, g3,
        (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6))).size := by
  rw [sz_arg7, shape6 (a := .nat) (b := TCfg), shape7 (a := TG0) (b := TG1),
    shape6 (a := Ty.list TEnt) (b := Ty.list TEnt) (c := Ty.list TEnt) (d := Ty.list TEnt)
      (e := Ty.list TEnt) (f := Ty.list TEnt), Ty.sz_list_cons, Ty.sz_list_cons]
  simp only [Ty.enc_nat]
  omega

theorem repair_cost (a : (TArg TX').den) :
    (Control.repairF x).cost a ≤ 3000000 * ((Ty.enc (TArg TX') a).size + 1) ^ 2 := by
  have hsq : (Ty.enc (TArg TX') a).size + 1 ≤ ((Ty.enc (TArg TX') a).size + 1) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, g3, ⟨gr, br, gt, bt, rg, rbd⟩, g5, g6⟩ := a
  have l17 := lit_sz 17 (by omega); have l19 := lit_sz 19 (by omega)
  rcases rg with _ | ⟨ge, gs⟩ <;> rcases rbd with _ | ⟨be, bs⟩
  · dsimp only [Control.repairF, bodySig_cost, Control.repairBody, Tm.cost, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ,
      Ty.enc_nat]
    fin_le
  · dsimp only [Control.repairF, bodySig_cost, Control.repairBody, Tm.cost, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ,
      Ty.enc_nat]
    fin_le
  · dsimp only [Control.repairF, bodySig_cost, Control.repairBody, Tm.cost, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ,
      Ty.enc_nat]
    fin_le
  · have hW := sz_W q r B m X g0 g1 g2 g3 gr br gt bt ge gs be bs g5 g6
    generalize (Ty.enc (TArg TX') (((q, r, B, m), X), (g0, g1, g2, g3,
        (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6))).size = S at hW hsq ⊢
    dsimp only [Control.repairF, bodySig_cost, Control.repairBody, Tm.cost, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
    strip_mdata
    rw [(min_eq_left (repairAcc_cost x _)).symm]
    generalize (Ty.enc TRA (r, (g0, g1, g2, g3, (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6), ge,
      gs, be, bs)).size = SW at hW ⊢
    have hq := sq_bound SW S (by omega)
    omega

theorem repair_depth (a : (TArg TX').den) :
    (Control.repairF x).depth a ≤ 100 * (Ty.enc (TArg TX') a).size + 600 := by
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, g3, ⟨gr, br, gt, bt, rg, rbd⟩, g5, g6⟩ := a
  rcases rg with _ | ⟨ge, gs⟩ <;> rcases rbd with _ | ⟨be, bs⟩
  · dsimp only [Control.repairF, bodySig_depth, Control.repairBody, Tm.depth, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
    fin_le
  · dsimp only [Control.repairF, bodySig_depth, Control.repairBody, Tm.depth, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
    fin_le
  · dsimp only [Control.repairF, bodySig_depth, Control.repairBody, Tm.depth, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
    fin_le
  · have hW := sz_W q r B m X g0 g1 g2 g3 gr br gt bt ge gs be bs g5 g6
    generalize (Ty.enc (TArg TX') (((q, r, B, m), X), (g0, g1, g2, g3,
        (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6))).size = S at hW ⊢
    dsimp only [Control.repairF, bodySig_depth, Control.repairBody, Tm.depth, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
    strip_mdata
    rw [(min_eq_left (repairAcc_depth x _)).symm]
    generalize (Ty.enc TRA (r, (g0, g1, g2, g3, (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6), ge,
      gs, be, bs)).size = SW at hW ⊢
    simp only [max_self, Nat.zero_max, Nat.max_zero]
    omega

theorem repair_ex (a : (TArg TX').den) :
    Control.Tm'.ex (Control.repairBody x) (Env.one a) ≤ 1000 * (Ty.enc (TArg TX') a).size + 10000 := by
  obtain ⟨⟨⟨q, r, B, m⟩, X⟩, g0, g1, g2, g3, ⟨gr, br, gt, bt, rg, rbd⟩, g5, g6⟩ := a
  rcases rg with _ | ⟨ge, gs⟩ <;> rcases rbd with _ | ⟨be, bs⟩
  · dsimp only [Control.repairBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
    fin_le
  · dsimp only [Control.repairBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
    fin_le
  · dsimp only [Control.repairBody, Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
    fin_le
  · have hW := sz_W q r B m X g0 g1 g2 g3 gr br gt bt ge gs be bs g5 g6
    generalize (Ty.enc (TArg TX') (((q, r, B, m), X), (g0, g1, g2, g3,
        (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6))).size = S at hW ⊢
    dsimp only [Control.repairBody, Control.Tm'.ex, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
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
         dsimp only [Control.Tm'.ex, Tm.msize, Tm.den, Env.one, phaseRepair_get_zero, phaseRepair_get_succ]
         generalize (Ty.enc TRA (r, (g0, g1, g2, g3, (gr, br, gt, bt, ge :: gs, be :: bs), g5, g6),
           ge, gs, be, bs)).size = SW at hW ⊢
         fin_le)

end QecReliability.Trans.BoundsStep
