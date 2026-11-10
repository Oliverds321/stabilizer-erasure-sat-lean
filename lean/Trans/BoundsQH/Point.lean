import Trans.BoundsQH.Poly

/-!
# Trans.BoundsQH.Point: the generic term bound with pointwise callee conditions

`Tm.CallsBP B tm ρ` asks the callee bounds only at the arguments actually used when evaluating
`tm` in `ρ` (it mirrors `Tm.CallsOK`). `Tm.boundP` is `Tm.bound` under this weaker hypothesis;
`polyB_of_bodyP`: a body-bounded signature is `PolyB` if, for one `G K C`, every evaluation of
its body satisfies `CallsBP (G K C)`. Used for callees that are only polynomially bounded on
the arguments they are called with (the adder tree inside `population`, the encoder inside the
hash program).
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.Trans.Query.Bound QecReliability.Trans.Query.Bound.Tm

/-- `F`'s quantities at `y` are bounded by `B (mag y)`. -/
def FnBAt (B : ℕ → ℕ) {a b : Ty} (F : FnSig a b) (y : a.den) : Prop :=
  F.cost y ≤ B (mag a y) ∧ F.depth y ≤ B (mag a y) ∧ F.msize y ≤ B (mag a y) ∧
    mag b (F.den y) ≤ B (mag a y)

/-- Callee bounds at the arguments actually used. -/
def Tm.CallsBP (B : ℕ → ℕ) {Γ : List Ty} {t : Ty} : Tm Γ t → Env Γ → Prop
  | .pair a b, ρ => Tm.CallsBP B a ρ ∧ Tm.CallsBP B b ρ
  | .fst p, ρ => Tm.CallsBP B p ρ
  | .snd p, ρ => Tm.CallsBP B p ρ
  | .ite c x y, ρ => Tm.CallsBP B c ρ ∧ (if c.den ρ then Tm.CallsBP B x ρ else Tm.CallsBP B y ρ)
  | .lcons h tl, ρ => Tm.CallsBP B h ρ ∧ Tm.CallsBP B tl ρ
  | .lcase s e₁ e₂, ρ =>
      Tm.CallsBP B s ρ ∧ (match s.den ρ with
        | [] => Tm.CallsBP B e₁ ρ
        | h :: tl => Tm.CallsBP B e₂ (.cons h (.cons tl ρ)))
  | .ncase s e₁ e₂, ρ =>
      Tm.CallsBP B s ρ ∧ (if s.den ρ = 0 then Tm.CallsBP B e₁ ρ
        else Tm.CallsBP B e₂ (.cons (decide (s.den ρ % 2 = 1)) (.cons (s.den ρ / 2) ρ)))
  | .bit b n, ρ => Tm.CallsBP B b ρ ∧ Tm.CallsBP B n ρ
  | .letE a b, ρ => Tm.CallsBP B a ρ ∧ Tm.CallsBP B b (.cons (a.den ρ) ρ)
  | .app F a, ρ => FnBAt B F (a.den ρ) ∧ Tm.CallsBP B a ρ
  | _, _ => True

theorem Tm.callsBP_of_callsB {B : ℕ → ℕ} {Γ : List Ty} {t : Ty} (tm : Tm Γ t)
    (h : Tm.CallsB B tm) (ρ : Env Γ) : Tm.CallsBP B tm ρ := by
  induction tm with
  | pair a b iha ihb => exact ⟨iha h.1 ρ, ihb h.2 ρ⟩
  | fst p ih => exact ih h ρ
  | snd p ih => exact ih h ρ
  | ite c x y ihc ihx ihy =>
    refine ⟨ihc h.1 ρ, ?_⟩
    cases c.den ρ
    · exact ihy h.2.2 ρ
    · exact ihx h.2.1 ρ
  | lcons a b iha ihb => exact ⟨iha h.1 ρ, ihb h.2 ρ⟩
  | lcase s e₁ e₂ ihs ih₁ ih₂ =>
    refine ⟨ihs h.1 ρ, ?_⟩
    cases s.den ρ with
    | nil => exact ih₁ h.2.1 ρ
    | cons hh tt => exact ih₂ h.2.2 _
  | ncase s e₁ e₂ ihs ih₁ ih₂ =>
    refine ⟨ihs h.1 ρ, ?_⟩
    split
    · exact ih₁ h.2.1 ρ
    · exact ih₂ h.2.2 _
  | bit a b iha ihb => exact ⟨iha h.1 ρ, ihb h.2 ρ⟩
  | letE a b iha ihb => exact ⟨iha h.1 ρ, ihb h.2 _⟩
  | app F a iha => exact ⟨h.1 (a.den ρ), iha h.2 ρ⟩
  | _ => trivial

namespace Tm

/-- **Generic bound, pointwise version.** -/
theorem boundP {B : ℕ → ℕ} (hB : Adm B) {Γ : List Ty} {t : Ty} (tm : Tm Γ t) (c : ℕ)
    (hlit : litc tm ≤ c) (ρ : Env Γ) (hc : CallsBP B tm ρ) :
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
    simp only [CallsBP, litc, max_le_iff] at hc hlit
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
    simp only [CallsBP, litc] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ih hlit ρ hc
    have st := hB.step (k := nodes p) (j := nodes (Tm.fst p)) (by simp [nodes]) (envMag ρ + c)
    simp only [mag_prod] at g1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega
  | snd p ih =>
    simp only [CallsBP, litc] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := ih hlit ρ hc
    have st := hB.step (k := nodes p) (j := nodes (Tm.snd p)) (by simp [nodes]) (envMag ρ + c)
    simp only [mag_prod] at g1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega
  | ite cnd x y ihc ihx ihy =>
    simp only [CallsBP, litc, max_le_iff] at hc hlit
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
    simp only [CallsBP, litc, max_le_iff] at hc hlit
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
    simp only [CallsBP, litc, max_le_iff] at hc hlit
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
    simp only [CallsBP, litc, max_le_iff] at hc hlit
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
    simp only [CallsBP, litc, max_le_iff] at hc hlit
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
    simp only [CallsBP, litc, max_le_iff] at hc hlit
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
    simp only [CallsBP, litc] at hc hlit
    obtain ⟨c1, d1, m1, g1⟩ := iha hlit ρ hc.2
    obtain ⟨f1, f2, f3, f4⟩ := hc.1
    have hm : B (mag _ (a.den ρ)) ≤ B^[nodes a + 1] (envMag ρ + c) := by
      rw [Function.iterate_succ_apply']; exact hB.mono g1
    have st := hB.step (k := nodes a + 1) (j := nodes (Tm.app F a)) (by simp [nodes]) (envMag ρ + c)
    have st0 := hB.step (k := nodes a) (j := nodes a + 1) le_rfl (envMag ρ + c)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Tm.cost, Tm.depth, Tm.msize, Tm.den] <;> omega

end Tm

/-- **Body-bounded signatures with pointwise callee bounds.** -/
theorem polyB_of_bodyP {a b : Ty} (F : FnSig a b) (body : Tm [a] b)
    (hcost : ∀ x, F.cost x ≤ body.cost (Env.one x) + 2)
    (hdepth : ∀ x, F.depth x ≤ body.depth (Env.one x) + 1)
    (hmsize : ∀ x, F.msize x ≤ body.msize (Env.one x))
    (hden : ∀ x, F.den x = body.den (Env.one x)) {K C : ℕ}
    (hc : ∀ x, Tm.CallsBP (G (K + 1) C) body (Env.one x)) : PolyB F := by
  refine ⟨(Tm.nodes body + 1) * (K + 1 + 1), C + Tm.litc body, fun x => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := Tm.boundP (adm_G (k := K + 1) (by omega) C) body (Tm.litc body)
    le_rfl (Env.one x) (hc x)
  have he : envMag (Env.one x) = mag a x := by simp [envMag]
  rw [he] at h1 h2 h3 h4
  have hst := (adm_G (k := K + 1) (by omega) C).step (k := Tm.nodes body)
    (j := Tm.nodes body + 1) le_rfl (mag a x + Tm.litc body)
  have hi := G_iter (K + 1) C (Tm.nodes body + 1) (mag a x + Tm.litc body)
  rw [G_shift] at hi
  have := hcost x; have := hdepth x; have := hmsize x
  rw [hden x]
  exact ⟨by omega, by omega, by omega, by omega⟩

end QecReliability.Trans.BoundsQH
