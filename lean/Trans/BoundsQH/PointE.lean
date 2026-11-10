import Trans.BoundsQH.Point

/-!
# Trans.BoundsQH.PointE: the generic term bound with environment-aware callee conditions

`Tm.CallsBE B tm ρ`: like `Tm.CallsBP`, but a callee's quantities at its actual argument `y`
need only be bounded by `B (max (mag y) (envMag ρ'))`, `ρ'` the environment of the call. This
allows callees whose bounds are not polynomial in their own argument but in data available in
the caller's environment (the encoder `prog ell` has size `≈ 2^ell`, and the hash program
has `base · 2^ell` in its environment). `Tm.boundE`, `fnBOn_of_bodyE`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.Trans.Query.Bound QecReliability.Trans.Query.Bound.Tm

/-- `F`'s quantities at `y` are bounded by `B (max (mag y) M)`. -/
def FnBAtE (B : ℕ → ℕ) {a b : Ty} (F : FnSig a b) (y : a.den) (M : ℕ) : Prop :=
  F.cost y ≤ B (max (mag a y) M) ∧ F.depth y ≤ B (max (mag a y) M) ∧
    F.msize y ≤ B (max (mag a y) M) ∧ mag b (F.den y) ≤ B (max (mag a y) M)

/-- Callee bounds at the arguments actually used. -/
def Tm.CallsBE (B : ℕ → ℕ) {Γ : List Ty} {t : Ty} : Tm Γ t → Env Γ → Prop
  | .pair a b, ρ => Tm.CallsBE B a ρ ∧ Tm.CallsBE B b ρ
  | .fst p, ρ => Tm.CallsBE B p ρ
  | .snd p, ρ => Tm.CallsBE B p ρ
  | .ite c x y, ρ => Tm.CallsBE B c ρ ∧ (if c.den ρ then Tm.CallsBE B x ρ else Tm.CallsBE B y ρ)
  | .lcons h tl, ρ => Tm.CallsBE B h ρ ∧ Tm.CallsBE B tl ρ
  | .lcase s e₁ e₂, ρ =>
      Tm.CallsBE B s ρ ∧ (match s.den ρ with
        | [] => Tm.CallsBE B e₁ ρ
        | h :: tl => Tm.CallsBE B e₂ (.cons h (.cons tl ρ)))
  | .ncase s e₁ e₂, ρ =>
      Tm.CallsBE B s ρ ∧ (if s.den ρ = 0 then Tm.CallsBE B e₁ ρ
        else Tm.CallsBE B e₂ (.cons (decide (s.den ρ % 2 = 1)) (.cons (s.den ρ / 2) ρ)))
  | .bit b n, ρ => Tm.CallsBE B b ρ ∧ Tm.CallsBE B n ρ
  | .letE a b, ρ => Tm.CallsBE B a ρ ∧ Tm.CallsBE B b (.cons (a.den ρ) ρ)
  | .app F a, ρ => FnBAtE B F (a.den ρ) (envMag ρ) ∧ Tm.CallsBE B a ρ
  | _, _ => True

namespace Tm

/-- **Generic bound, environment-aware version.** -/
theorem boundE {B : ℕ → ℕ} (hB : Adm B) {Γ : List Ty} {t : Ty} (tm : Tm Γ t) (c : ℕ)
    (hlit : litc tm ≤ c) (ρ : Env Γ) (hc : CallsBE B tm ρ) :
    AllLe tm ρ (B^[nodes tm] (envMag ρ + c)) := by
  induction tm with
  | var i =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    have h2 := mag_get ρ i
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes] <;> omega
  | val v =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [litc] at hlit
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_val] <;>
      omega
  | lit x =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    have h2 := size_le_mag _ x
    simp only [litc] at hlit
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes] <;> omega
  | unit =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_unit] <;>
      omega
  | ff =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_bool] <;>
      omega
  | tt =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_bool] <;>
      omega
  | zero =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_nat] <;>
      omega
  | lnil =>
    have h1 := hB.step (k := 0) (j := 1) le_rfl (envMag ρ + c)
    simp only [Function.iterate_zero, id] at h1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, nodes, mag_nil] <;>
      omega
  | pair a b iha ihb =>
    simp only [CallsBE, litc, max_le_iff] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := iha hlit.1 ρ hc.1
    obtain ⟨c2, d2, m2, g2⟩ := ihb hlit.2 ρ hc.2
    have l1 := hB.lift (show nodes a ≤ nodes a + nodes b by omega) (envMag ρ + c)
    have l2 := hB.lift (show nodes b ≤ nodes a + nodes b by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes a + nodes b) (j := nodes (Tm.pair a b)) (by simp [nodes])
      (envMag ρ + c)
    have sz := size_le_mag _ ((Tm.pair a b).den ρ)
    simp only [Tm.den, mag_prod] at sz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, mag_prod] <;> omega
  | fst p ih =>
    simp only [CallsBE, litc] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ih hlit ρ hc
    have st := hB.step (k := nodes p) (j := nodes (Tm.fst p)) (by simp [nodes]) (envMag ρ + c)
    simp only [mag_prod] at g1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega
  | snd p ih =>
    simp only [CallsBE, litc] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ih hlit ρ hc
    have st := hB.step (k := nodes p) (j := nodes (Tm.snd p)) (by simp [nodes]) (envMag ρ + c)
    simp only [mag_prod] at g1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega
  | ite cnd x y ihc ihx ihy =>
    simp only [CallsBE, litc, max_le_iff] at hc hlit
    obtain ⟨c0, d0, m0, g0⟩ := ihc hlit.1 ρ hc.1
    have l0 := hB.lift (show nodes cnd ≤ nodes cnd + nodes x + nodes y by omega) (envMag ρ + c)
    have l1 := hB.lift (show nodes x ≤ nodes cnd + nodes x + nodes y by omega) (envMag ρ + c)
    have l2 := hB.lift (show nodes y ≤ nodes cnd + nodes x + nodes y by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes cnd + nodes x + nodes y) (j := nodes (Tm.ite cnd x y))
      (by simp [nodes]) (envMag ρ + c)
    have hc2 := hc.2
    cases hcd : cnd.den ρ
    · simp only [hcd] at hc2
      obtain ⟨c2, d2, m2, g2⟩ := ihy hlit.2.2 ρ (by simpa using hc2)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hcd] <;> simp <;>
        omega
    · simp only [hcd] at hc2
      obtain ⟨c1, d1, m1, g1⟩ := ihx hlit.2.1 ρ (by simpa using hc2)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hcd] <;> simp <;>
        omega
  | lcons h tl ihh iht =>
    simp only [CallsBE, litc, max_le_iff] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ihh hlit.1 ρ hc.1
    obtain ⟨c2, d2, m2, g2⟩ := iht hlit.2 ρ hc.2
    have l1 := hB.lift (show nodes h ≤ nodes h + nodes tl by omega) (envMag ρ + c)
    have l2 := hB.lift (show nodes tl ≤ nodes h + nodes tl by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes h + nodes tl) (j := nodes (Tm.lcons h tl)) (by simp [nodes])
      (envMag ρ + c)
    have sz := size_le_mag _ ((Tm.lcons h tl).den ρ)
    simp only [Tm.den, mag_cons] at sz
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, mag_cons] <;> omega
  | @lcase _ te _ sc e₁ e₂ ihs ih₁ ih₂ =>
    simp only [CallsBE, litc, max_le_iff] at hc hlit
    obtain ⟨cs, ds, ms, gs⟩ := ihs hlit.1 ρ hc.1
    have l0 := hB.lift (show nodes sc ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes sc + nodes e₁ + nodes e₂ + 1) (j := nodes (Tm.lcase sc e₁ e₂))
      (by simp [nodes]) (envMag ρ + c)
    have hc2 := hc.2
    cases hd : sc.den ρ with
    | nil =>
      simp only [hd] at hc2
      obtain ⟨c1, d1, m1, g1⟩ := ih₁ hlit.2.1 ρ hc2
      have l1 := hB.lift (show nodes e₁ ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega) (envMag ρ + c)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hd] <;> omega
    | cons hh tt =>
      simp only [hd] at hc2
      rw [hd] at gs
      simp only [mag_cons] at gs
      have hX : envMag (Env.cons (t := te) hh (Env.cons (t := .list te) tt ρ)) + c ≤
          B^[nodes sc + 1] (envMag ρ + c) := by
        have := hB.step (k := nodes sc) (j := nodes sc + 1) le_rfl (envMag ρ + c)
        have := hB.le_iter (nodes sc) (envMag ρ + c)
        simp only [envMag_cons]; omega
      obtain ⟨c2, d2, m2, g2⟩ := ih₂ hlit.2.2 (Env.cons (t := te) hh (Env.cons (t := .list te) tt ρ))
        hc2
      have cmp := hB.comp (a := nodes e₂) hX
      have l2 := hB.lift (show nodes e₂ + (nodes sc + 1) ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by
        omega) (envMag ρ + c)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hd] <;> omega
  | ncase sc e₁ e₂ ihs ih₁ ih₂ =>
    simp only [CallsBE, litc, max_le_iff] at hc hlit
    obtain ⟨cs, ds, ms, gs⟩ := ihs hlit.1 ρ hc.1
    have l0 := hB.lift (show nodes sc ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes sc + nodes e₁ + nodes e₂ + 1) (j := nodes (Tm.ncase sc e₁ e₂))
      (by simp [nodes]) (envMag ρ + c)
    have hc2 := hc.2
    by_cases hn : sc.den ρ = 0
    · simp only [hn, if_true] at hc2
      obtain ⟨c1, d1, m1, g1⟩ := ih₁ hlit.2.1 ρ hc2
      have l1 := hB.lift (show nodes e₁ ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by omega) (envMag ρ + c)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hn, if_true] <;>
        omega
    · simp only [hn, if_false] at hc2
      simp only [mag_nat] at gs
      have hX : envMag (Env.cons (t := .bool) (decide (sc.den ρ % 2 = 1))
          (Env.cons (t := .nat) (sc.den ρ / 2) ρ)) + c ≤ B^[nodes sc + 1] (envMag ρ + c) := by
        have := hB.step (k := nodes sc) (j := nodes sc + 1) le_rfl (envMag ρ + c)
        have := hB.le_iter (nodes sc) (envMag ρ + c)
        simp only [envMag_cons, mag_bool, mag_nat]; omega
      obtain ⟨c2, d2, m2, g2⟩ := ih₂ hlit.2.2
        (Env.cons (t := .bool) (decide (sc.den ρ % 2 = 1)) (Env.cons (t := .nat) (sc.den ρ / 2) ρ))
        hc2
      have cmp := hB.comp (a := nodes e₂) hX
      have l2 := hB.lift (show nodes e₂ + (nodes sc + 1) ≤ nodes sc + nodes e₁ + nodes e₂ + 1 by
        omega) (envMag ρ + c)
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, hn, if_false] <;>
        omega
  | bit b n ihb ihn =>
    simp only [CallsBE, litc, max_le_iff] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ihb hlit.1 ρ hc.1
    obtain ⟨c2, d2, m2, g2⟩ := ihn hlit.2 ρ hc.2
    have l1 := hB.lift (show nodes b ≤ nodes b + nodes n by omega) (envMag ρ + c)
    have l2 := hB.lift (show nodes n ≤ nodes b + nodes n by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes b + nodes n) (j := nodes (Tm.bit b n)) (by simp [nodes])
      (envMag ρ + c)
    have hb := bitNat_le (b.den ρ) (n.den ρ)
    have sz := size_le_mag .nat (bitNat (b.den ρ) (n.den ρ))
    simp only [Ty.enc_nat, mag_nat] at sz g2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den, mag_nat] <;> omega
  | letE a b iha ihb =>
    simp only [CallsBE, litc, max_le_iff] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := iha hlit.1 ρ hc.1
    have hX : envMag (Env.cons (a.den ρ) ρ) + c ≤ B^[nodes a + 1] (envMag ρ + c) := by
      have := hB.step (k := nodes a) (j := nodes a + 1) le_rfl (envMag ρ + c)
      have := hB.le_iter (nodes a) (envMag ρ + c)
      simp only [envMag_cons]; omega
    obtain ⟨c2, d2, m2, g2⟩ := ihb hlit.2 (Env.cons (a.den ρ) ρ) hc.2
    have cmp := hB.comp (a := nodes b) hX
    have l1 := hB.lift (show nodes a ≤ nodes b + (nodes a + 1) by omega) (envMag ρ + c)
    have st := hB.step2 (k := nodes b + (nodes a + 1)) (j := nodes (Tm.letE a b))
      (by simp [nodes]; omega) (envMag ρ + c)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega
  | app F a iha =>
    simp only [CallsBE, litc] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := iha hlit ρ hc.2
    obtain ⟨f1, f2, f3, f4⟩ := hc.1
    have hm : B (max (mag _ (a.den ρ)) (envMag ρ)) ≤ B^[nodes a + 1] (envMag ρ + c) := by
      rw [Function.iterate_succ_apply']
      exact hB.mono (max_le g1 ((Nat.le_add_right _ _).trans (hB.le_iter _ _)))
    have st := hB.step (k := nodes a + 1) (j := nodes (Tm.app F a)) (by simp [nodes]) (envMag ρ + c)
    have st0 := hB.step (k := nodes a) (j := nodes a + 1) le_rfl (envMag ρ + c)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega

end Tm

/-- **Body-bounded signatures, environment-aware callee bounds, on a set of arguments.** -/
theorem fnBOn_of_bodyE {a b : Ty} (F : FnSig a b) (body : Tm [a] b)
    (hcost : ∀ x, F.cost x ≤ body.cost (Env.one x) + 2)
    (hdepth : ∀ x, F.depth x ≤ body.depth (Env.one x) + 1)
    (hmsize : ∀ x, F.msize x ≤ body.msize (Env.one x))
    (hden : ∀ x, F.den x = body.den (Env.one x)) (Q : a.den → Prop) {K C : ℕ}
    (hc : ∀ x, Q x → Tm.CallsBE (G (K + 1) C) body (Env.one x)) :
    ∃ K' C', ∀ x, Q x → FnBAt (G K' C') F x := by
  refine ⟨(Tm.nodes body + 1) * (K + 1 + 1), C + Tm.litc body, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := Tm.boundE (adm_G (k := K + 1) (by omega) C) body (Tm.litc body)
    le_rfl (Env.one x) (hc x hx)
  have he : envMag (Env.one x) = mag a x := by simp [envMag]
  rw [he] at h1 h2 h3 h4
  have hst := (adm_G (k := K + 1) (by omega) C).step (k := Tm.nodes body)
    (j := Tm.nodes body + 1) le_rfl (mag a x + Tm.litc body)
  have hi := G_iter (K + 1) C (Tm.nodes body + 1) (mag a x + Tm.litc body)
  rw [G_shift] at hi
  have := hcost x; have := hdepth x; have := hmsize x
  unfold FnBAt
  rw [hden x]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- A global bound gives the environment-aware one. -/
theorem fnBAtE_of {a b : Ty} {F : FnSig a b} {k c K C : ℕ} (h : FnB (G k c) F) (hk : k ≤ K)
    (hc : c ≤ C) (y : a.den) (M : ℕ) : FnBAtE (G K C) F y M := by
  obtain ⟨h1, h2, h3, h4⟩ := h y
  have e := G_mono (m := mag a y) (m' := max (mag a y) M) hk hc (le_max_left _ _)
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e⟩

theorem FnBAtE.lift {a b : Ty} {F : FnSig a b} {y : a.den} {M k c K C : ℕ}
    (h : FnBAtE (G k c) F y M) (hk : k ≤ K) (hc : c ≤ C) : FnBAtE (G K C) F y M := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e := G_mono (m := max (mag a y) M) hk hc le_rfl
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e⟩

end QecReliability.Trans.BoundsQH
