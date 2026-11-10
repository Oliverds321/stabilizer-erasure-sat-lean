import Trans.BoundsQH.Comb
import Trans.Query.FLCirc

/-!
# Trans.BoundsQH.QCirc: polynomial bounds for `Trans/Query/FLCirc.lean`

* `polyB_exact`: an `FnSig.exact` function is `PolyB` when its callees are.
* `chain_G`: the closed form of a linear recursion with a `G k c` step bound.
* `PolyB` for the wire maps (`shiftWireF … formTF`, `gateSF gatesSF wiresSF`), `gateClausesF`,
  `compileAtF` (recursion), `blockAndF`, `outputUnitsF` (recursion), `matchBlockF`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Query

attribute [polyB] mapEnvQ_P mapEnvH_P flatMapEnvQ_P mapF_P filterF_P flatMapF_P

/-- `FnSig.exact` functions are polynomially bounded when their callees are. -/
theorem polyB_exact {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den)
    (hden : ∀ x, body.den (Env.one x) = den x) (hc : Tm.CallsP body) :
    PolyB (FnSig.exact i body den) :=
  polyB_of_body _ body (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun x => (hden x).symm) hc

/-- Closed form of a linear recursion with step bound `G k c`. -/
theorem chain_G {α : Type} (ℓ μ f : α → ℕ) (hℓ : ∀ x, ℓ x ≤ μ x) {k c : ℕ}
    (h : ∀ x, f x ≤ G k c (μ x) ∨ ∃ y, ℓ y < ℓ x ∧ μ y ≤ μ x ∧ f x ≤ G k c (μ x) + f y) :
    ∀ x, f x ≤ G (k + 1) c (μ x) := fun x => by
  have h1 := chain_bound ℓ μ f (G k c) (G_monotone k c) h x
  have h2 := le_G k c (μ x)
  have h3 : (ℓ x + 1) * G k c (μ x) ≤ (G k c (μ x) + 1) * (G k c (μ x) + 1) :=
    Nat.mul_le_mul (by have := hℓ x; omega) (by omega)
  have h4 := G_sq k c (μ x)
  omega

theorem G_lin20 (k c m : ℕ) (hc : 300 ≤ c) : 20 * G k c m + 100 ≤ G (k + 1) c m := by
  have h1 := G_sq k c m
  have h2 := le_G k c m
  nlinarith

/-- Lifting a callee bound to a common `G K C` at a larger magnitude. -/
theorem fnB_at {a b : Ty} {F : FnSig a b} {k c K C : ℕ} (hF : FnB (G k c) F) (hk : k ≤ K)
    (hc : c ≤ C) {y : a.den} {m : ℕ} (hy : mag a y ≤ m) :
    F.cost y ≤ G K C m ∧ F.depth y ≤ G K C m ∧ F.msize y ≤ G K C m ∧ mag b (F.den y) ≤ G K C m := by
  obtain ⟨h1, h2, h3, h4⟩ := hF y
  have e := G_mono hk hc hy
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e⟩

/-- **Linear recursions are `PolyB`.** At every argument, either all four quantities are
bounded by `G K C` (msize up to `15·mag` of the result), or there is a smaller argument `y`
(no larger magnitude) such that each quantity is bounded by `G K C` plus its value at `y`. -/
theorem polyB_chain {a b : Ty} (F : FnSig a b) (ℓ : a.den → ℕ) (hℓ : ∀ x, ℓ x ≤ mag a x)
    {K C : ℕ} (hC : 300 ≤ C)
    (h : ∀ x, (F.cost x ≤ G K C (mag a x) ∧ F.depth x ≤ G K C (mag a x) ∧
        mag b (F.den x) ≤ G K C (mag a x) ∧ F.msize x ≤ G K C (mag a x) + 15 * mag b (F.den x)) ∨
      ∃ y, ℓ y < ℓ x ∧ mag a y ≤ mag a x ∧ F.cost x ≤ G K C (mag a x) + F.cost y ∧
        F.depth x ≤ G K C (mag a x) + F.depth y ∧
        mag b (F.den x) ≤ G K C (mag a x) + mag b (F.den y) ∧
        F.msize x ≤ G K C (mag a x) + 15 * mag b (F.den x) + F.msize y) :
    FnB (G (K + 3) C) F := by
  have hres := chain_G ℓ (mag a) (fun x => mag b (F.den x)) hℓ (k := K) (c := C) (fun x =>
    (h x).imp (fun h => h.2.2.1) (fun ⟨y, h1, h2, _, _, h5, _⟩ => ⟨y, h1, h2, h5⟩))
  have hcost := chain_G ℓ (mag a) F.cost hℓ (k := K) (c := C) (fun x =>
    (h x).imp (fun h => h.1) (fun ⟨y, h1, h2, h3, _, _, _⟩ => ⟨y, h1, h2, h3⟩))
  have hdepth := chain_G ℓ (mag a) F.depth hℓ (k := K) (c := C) (fun x =>
    (h x).imp (fun h => h.2.1) (fun ⟨y, h1, h2, _, h4, _, _⟩ => ⟨y, h1, h2, h4⟩))
  have hm : ∀ x, G K C (mag a x) + 15 * mag b (F.den x) ≤ G (K + 2) C (mag a x) := fun x => by
    have h1 := hres x
    have h2 := lin16 (K + 1) C (mag a x) (by omega)
    have h3 := G_mono (k := K) (k' := K + 1) (c := C) (c' := C) (by omega) le_rfl
      (le_refl (mag a x))
    have h4 : G (K + 1 + 1) C (mag a x) = G (K + 2) C (mag a x) := rfl
    omega
  have hmsize := chain_G ℓ (mag a) F.msize hℓ (k := K + 2) (c := C) (fun x =>
    (h x).imp (fun h => h.2.2.2.trans (hm x)) (fun ⟨y, h1, h2, _, _, _, h6⟩ =>
      ⟨y, h1, h2, h6.trans (by have := hm x; omega)⟩))
  intro x
  have e1 := G_mono (k := K + 1) (k' := K + 3) (c := C) (c' := C) (by omega) le_rfl
    (le_refl (mag a x))
  have e2 : G (K + 2 + 1) C (mag a x) = G (K + 3) C (mag a x) := rfl
  have := hres x; have := hcost x; have := hdepth x; have := hmsize x
  exact ⟨by omega, by omega, by omega, by omega⟩

/-! ## Wire maps -/

section Maps
variable (x : Ix)

theorem shiftWire_den' (p : (Ty.prod TEnvS .nat).den) :
    (shiftWireBody x).den (Env.one p) = Plain.shiftWire p.1 p.2 := by
  simp [tm_simp, shiftWireBody, Plain.shiftWire]

@[polyB] theorem shiftWireF_P : PolyB (shiftWireF x) :=
  polyB_exact _ _ _ (shiftWire_den' x) (by simp [Tm.CallsP, shiftWireBody, polyB])

@[polyB] theorem litSF_P : PolyB (litSF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, litSBody, Plain.litS])
    (by simp [Tm.CallsP, litSBody, polyB])

@[polyB] theorem clauseSF_P : PolyB (clauseSF x) := mapEnvQ_P (litSF_P x) _
@[polyB] theorem formSF_P : PolyB (formSF x) := mapEnvQ_P (clauseSF_P x) _

@[polyB] theorem tableWireF_P : PolyB (tableWireF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, tableWireBody, Plain.tableWire])
    (by simp [Tm.CallsP, tableWireBody, polyB])

@[polyB] theorem litTF_P : PolyB (litTF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, litTBody, Plain.litT])
    (by simp [Tm.CallsP, litTBody, polyB])

@[polyB] theorem clauseTF_P : PolyB (clauseTF x) := mapEnvQ_P (litTF_P x) _
@[polyB] theorem formTF_P : PolyB (formTF x) := mapEnvQ_P (clauseTF_P x) _

@[polyB] theorem gateSF_P : PolyB (gateSF x) :=
  polyB_exact _ _ _ (fun p => by
      obtain ⟨e, u, s, a, b⟩ := p
      cases u <;> cases s <;> simp [tm_simp, gateSBody, Plain.gateS])
    (by simp [Tm.CallsP, gateSBody, polyB])

@[polyB] theorem gatesSF_P : PolyB (gatesSF x) := mapEnvQ_P (gateSF_P x) _
@[polyB] theorem wiresSF_P : PolyB (wiresSF x) := mapEnvQ_P (shiftWireF_P x) _

@[polyB] theorem gateClausesF_P : PolyB (gateClausesF x) :=
  polyB_exact _ _ _ (fun p => by
      obtain ⟨o, u, s, a, b⟩ := p
      cases u <;> cases s <;> simp [tm_simp, gateClausesBody, Plain.gateClauses])
    (by simp [Tm.CallsP, gateClausesBody])

@[polyB] theorem blockAndF_P : PolyB (blockAndF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, blockAndBody, Plain.blockAnd])
    (by simp [Tm.CallsP, blockAndBody, polyB])

end Maps

/-! ## `compileAt` -/

section CompileAt
variable (x : Ix)

theorem mag_compileAt_step (k : ℕ) (g : Ty.den TGate) (gs : List (Ty.den TGate)) :
    mag (.prod .nat TGates) (k + 1, gs) ≤ mag (.prod .nat TGates) (k, g :: gs) := by
  simp only [mag_prod, mag_nat]; rw [mag_cons]; omega

theorem mag_compileAt_gate (k : ℕ) (g : Ty.den TGate) (gs : List (Ty.den TGate)) :
    mag (.prod .nat TGate) (k, g) ≤ mag (.prod .nat TGates) (k, g :: gs) := by
  have := mag_cons TGate g gs
  simp only [mag_prod, mag_nat] at this ⊢; omega

theorem compileAtF_P : PolyB (compileAtF x) := by
  obtain ⟨kg, cg, hg⟩ := gateClausesF_P x
  -- common step bound `G K C`
  have hs := succF_B x.succ
  have st : ∀ (k : ℕ) (g : Ty.den TGate) (gs : List (Ty.den TGate)),
      (gateClausesF x).cost (k, g) + 15 * (Plain.gateClauses k g).length + (succF x.succ).cost k +
          60 ≤ G (kg + 3) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) ∧
      (gateClausesF x).depth (k, g) + (Plain.gateClauses k g).length + (succF x.succ).depth k +
          5 ≤ G (kg + 3) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) ∧
      mag TForm (Plain.gateClauses k g) ≤ G (kg + 3) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) ∧
      (gateClausesF x).msize (k, g) + (succF x.succ).msize k +
          (Ty.enc (.prod .nat TGate) (k, g)).size + (Ty.enc (.prod .nat TGates) (k + 1, gs)).size +
          10 ≤ G (kg + 3) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) := by
    intro k g gs
    have hμ := mag_compileAt_gate k g gs
    have hμ2 := mag_compileAt_step k g gs
    obtain ⟨g1, g2, g3, g4⟩ := fnB_at hg (K := kg + 2) (C := cg + 300) (by omega) (by omega) hμ
    obtain ⟨s1, s2, s3, -⟩ := fnB_at hs (K := kg + 2) (C := cg + 300) (by omega) (by omega)
      (show mag .nat k ≤ mag (.prod .nat TGates) (k, g :: gs) by
        simp only [mag_prod, mag_nat] at hμ ⊢; omega)
    have hl := mag_list_len TClause (Plain.gateClauses k g)
    simp only [gateClausesF_den] at g4
    have z1 := sz_le (.prod .nat TGate) (k, g)
    have z2 := sz_le (.prod .nat TGates) (k + 1, gs)
    have L : 20 * G (kg + 2) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) + 100 ≤
        G (kg + 3) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) :=
      G_lin20 (kg + 2) (cg + 300) _ (by omega)
    have L0 := le_G (kg + 2) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs))
    exact ⟨by omega, by omega, by omega, by omega⟩
  -- result magnitude
  have hres := chain_G (fun p : (Ty.prod .nat TGates).den => p.2.length)
    (fun p => mag (.prod .nat TGates) p) (fun p => mag TForm (Plain.compileAt p.1 p.2))
    (fun p => by have := mag_list_len TGate p.2; simp only [mag_prod]; omega)
    (k := kg + 3) (c := cg + 300) (fun p => by
      obtain ⟨k, (_ | ⟨g, gs⟩)⟩ := p
      · left; simp only [Plain.compileAt]; exact (le_of_eq (show mag TForm [] = 1 from rfl)).trans (G_const (by omega))
      · right
        refine ⟨(k + 1, gs), by simp, mag_compileAt_step k g gs, ?_⟩
        have := (st k g gs).2.2.1
        have := mag_append_le TClause (Plain.gateClauses k g) (Plain.compileAt (k + 1) gs)
        simp only [Plain.compileAt]
        omega)
  refine ⟨kg + 6, cg + 300, fun p => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := chain_G (fun p : (Ty.prod .nat TGates).den => p.2.length)
      (fun p => mag (.prod .nat TGates) p) (fun p => compileAtCost x p.1 p.2)
      (fun p => by have := mag_list_len TGate p.2; simp only [mag_prod]; omega)
      (k := kg + 3) (c := cg + 300) (fun p => by
        obtain ⟨k, (_ | ⟨g, gs⟩)⟩ := p
        · left; simp only [compileAtCost]; exact G_const (by omega)
        · right
          refine ⟨(k + 1, gs), by simp, mag_compileAt_step k g gs, ?_⟩
          have := (st k g gs).1
          simp only [compileAtCost]
          omega) p
    simp only [compileAtF_cost]
    exact this.trans (G_mono (by omega) le_rfl le_rfl)
  · have := chain_G (fun p : (Ty.prod .nat TGates).den => p.2.length)
      (fun p => mag (.prod .nat TGates) p) (fun p => compileAtDepth x p.1 p.2)
      (fun p => by have := mag_list_len TGate p.2; simp only [mag_prod]; omega)
      (k := kg + 3) (c := cg + 300) (fun p => by
        obtain ⟨k, (_ | ⟨g, gs⟩)⟩ := p
        · left; simp only [compileAtDepth]; exact G_const (by omega)
        · right
          refine ⟨(k + 1, gs), by simp, mag_compileAt_step k g gs, ?_⟩
          have := (st k g gs).2.1
          simp only [compileAtDepth]
          omega) p
    simp only [compileAtF_depth]
    exact this.trans (G_mono (by omega) le_rfl le_rfl)
  · have := chain_G (fun p : (Ty.prod .nat TGates).den => p.2.length)
      (fun p => mag (.prod .nat TGates) p) (fun p => compileAtMsize x p.1 p.2)
      (fun p => by have := mag_list_len TGate p.2; simp only [mag_prod]; omega)
      (k := kg + 4 + 1) (c := cg + 300) (fun p => by
        obtain ⟨k, (_ | ⟨g, gs⟩)⟩ := p
        · left; simp only [compileAtMsize]; exact G_const (by omega)
        · right
          refine ⟨(k + 1, gs), by simp, mag_compileAt_step k g gs, ?_⟩
          have h1 := (st k g gs).2.2.2
          have h2 := hres (k, g :: gs)
          have h3 := sz_le TForm (Plain.compileAt k (g :: gs))
          have h4 : 20 * G (kg + 4) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) + 100 ≤
              G (kg + 4 + 1) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) :=
            G_lin20 _ _ _ (by omega)
          have h5 := G_succ (kg + 3) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs))
          have h6 : G (kg + 3 + 1) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) =
              G (kg + 4) (cg + 300) (mag (.prod .nat TGates) (k, g :: gs)) := rfl
          dsimp only at h2
          simp only [compileAtMsize]
          omega) p
    simp only [compileAtF_msize]
    exact this.trans (G_mono (by omega) le_rfl le_rfl)
  · have := hres p
    simp only [compileAtF_den]
    exact this.trans (G_mono (by omega) le_rfl le_rfl)

attribute [polyB] compileAtF_P

end CompileAt

end QecReliability.Trans.BoundsQH
