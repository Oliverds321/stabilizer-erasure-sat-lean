import Trans.BoundsQH.QGood
import Trans.BoundsQH.Point
import Trans.BoundsQH.QCodec
import Trans.Query.FLPop

/-!
# Trans.BoundsQH.QPop: polynomial bounds for `Trans/Query/FLPop.lean`

* `polyB_chainμ`: linear recursions measured by any `μ ≤ A (mag + 1)` (for `rippleF`, whose
  recursive argument `(v+5, as, bs, v+4)` may have larger magnitude than the argument).
* Wire invariant `PInv` of programs; `ripple_inv`, `countTree_inv` (all wires `≤ X + #gates`,
  `#gates ≤ 5 k 2^k`, `#outputs ≤ |xs| + k + 1`).
* `countTreeF` is polynomially bounded **on arguments with `2^k ≤ |xs| + 1`** (`countTree_on`,
  binary recursion of height `k`); `populationF_P` via the pointwise bound `polyB_of_bodyP`
  (population calls the tree at `|xs| = 2^k`).
* `weightBlockF_P`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Query

/-- `polyB_chain` with an arbitrary measure `μ ≤ A (mag + 1)`. -/
theorem polyB_chainμ {a b : Ty} (F : FnSig a b) (ℓ μ : a.den → ℕ) (hℓ : ∀ x, ℓ x ≤ μ x)
    (A : ℕ) (hμ : ∀ x, μ x ≤ A * (mag a x + 1)) {K C : ℕ} (hC : 300 ≤ C)
    (h : ∀ x, (F.cost x ≤ G K C (μ x) ∧ F.depth x ≤ G K C (μ x) ∧
        mag b (F.den x) ≤ G K C (μ x) ∧ F.msize x ≤ G K C (μ x) + 15 * mag b (F.den x)) ∨
      ∃ y, ℓ y < ℓ x ∧ μ y ≤ μ x ∧ F.cost x ≤ G K C (μ x) + F.cost y ∧
        F.depth x ≤ G K C (μ x) + F.depth y ∧
        mag b (F.den x) ≤ G K C (μ x) + mag b (F.den y) ∧
        F.msize x ≤ G K C (μ x) + 15 * mag b (F.den x) + F.msize y) :
    FnB (G (K + 6) (C + A)) F := by
  have hres := chain_G ℓ μ (fun x => mag b (F.den x)) hℓ (k := K) (c := C) (fun x =>
    (h x).imp (fun h => h.2.2.1) (fun ⟨y, h1, h2, _, _, h5, _⟩ => ⟨y, h1, h2, h5⟩))
  have hcost := chain_G ℓ μ F.cost hℓ (k := K) (c := C) (fun x =>
    (h x).imp (fun h => h.1) (fun ⟨y, h1, h2, h3, _, _, _⟩ => ⟨y, h1, h2, h3⟩))
  have hdepth := chain_G ℓ μ F.depth hℓ (k := K) (c := C) (fun x =>
    (h x).imp (fun h => h.2.1) (fun ⟨y, h1, h2, _, h4, _, _⟩ => ⟨y, h1, h2, h4⟩))
  have hm : ∀ x, G K C (μ x) + 15 * mag b (F.den x) ≤ G (K + 2) C (μ x) := fun x => by
    have h1 := hres x
    have h2 := lin16 (K + 1) C (μ x) (by omega)
    have h3 := G_mono (k := K) (k' := K + 1) (c := C) (c' := C) (by omega) le_rfl (le_refl (μ x))
    have h4 : G (K + 1 + 1) C (μ x) = G (K + 2) C (μ x) := rfl
    omega
  have hmsize := chain_G ℓ μ F.msize hℓ (k := K + 2) (c := C) (fun x =>
    (h x).imp (fun h => h.2.2.2.trans (hm x)) (fun ⟨y, h1, h2, _, _, _, h6⟩ =>
      ⟨y, h1, h2, h6.trans (by have := hm x; omega)⟩))
  intro x
  have l1 := lin_le A (mag a x)
  have hx : μ x ≤ G 2 A (mag a x) := by have := hμ x; omega
  have c1 : G (K + 3) C (μ x) ≤ G (K + 6) (C + A) (mag a x) :=
    (G_mono le_rfl le_rfl hx).trans ((G_comp (K + 3) C 2 A (mag a x)).trans
      (G_mono (by omega) le_rfl le_rfl))
  have e1 := G_mono (k := K + 1) (k' := K + 3) (c := C) (c' := C) (by omega) le_rfl (le_refl (μ x))
  have e2 : G (K + 2 + 1) C (μ x) = G (K + 3) C (μ x) := rfl
  have := hres x; have := hcost x; have := hdepth x; have := hmsize x
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem fnBAt_of {a b : Ty} {F : FnSig a b} {k c K C : ℕ} (h : FnB (G k c) F) (hk : k ≤ K)
    (hc : c ≤ C) (y : a.den) : FnBAt (G K C) F y := fnB_at h hk hc le_rfl

/-! ## Wire invariant of programs -/

/-- All wires of a program are `≤ W`. -/
def PInv (W : ℕ) (p : Plain.ProgP) : Prop :=
  (∀ g ∈ p.1, g.2.2.1 ≤ W ∧ g.2.2.2 ≤ W) ∧ ∀ o ∈ p.2, o ≤ W

theorem mag_prog_le {W : ℕ} (p : Plain.ProgP) (h : PInv W p) :
    mag TProg p ≤ (p.1.length + p.2.length + 2) * (2 * W + 10) := by
  have h1 := mag_gates_le p.1 h.1
  have h2 := mag_wires_le p.2 h.2
  have e : mag TProg p = mag TGates p.1 + mag (.list .nat) p.2 + 1 := rfl
  have e2 : (p.1.length + p.2.length + 2) * (2 * W + 10) =
      p.1.length * (2 * W + 10) + p.2.length * (2 * W + 10) + 2 * (2 * W + 10) := by ring
  have m1 : p.1.length * (2 * W + 6) ≤ p.1.length * (2 * W + 10) := Nat.mul_le_mul_left _ (by omega)
  have m2 : p.2.length * (W + 1) ≤ p.2.length * (2 * W + 10) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem ripple_inv : ∀ (xs ys : List ℕ) (v c W : ℕ), v ≤ W → c ≤ W → (∀ a ∈ xs, a ≤ W) →
    (∀ b ∈ ys, b ≤ W) →
    PInv (W + 5 * min xs.length ys.length) (Plain.ripple v xs ys c) ∧
    (Plain.ripple v xs ys c).1.length = 5 * min xs.length ys.length ∧
    (Plain.ripple v xs ys c).2.length = min xs.length ys.length + 1
  | [], ys, v, c, W, _, hc, _, _ => by
    simp only [ripple_nil, List.length_nil, Nat.zero_min, PInv]
    refine ⟨⟨by simp, by simp; omega⟩, by simp, by simp⟩
  | a :: as, [], v, c, W, _, hc, _, _ => by
    simp only [ripple_cons_nil, List.length_nil, Nat.min_zero, PInv]
    refine ⟨⟨by simp, by simp; omega⟩, by simp, by simp⟩
  | a :: as, b :: bs, v, c, W, hv, hc, ha, hb => by
    have ha' : a ≤ W := ha a (by simp)
    have hb' : b ≤ W := hb b (by simp)
    obtain ⟨⟨r1, r2⟩, r3, r4⟩ := ripple_inv as bs (v + 5) (v + 4) (W + 5) (by omega) (by omega)
      (fun x hx => (ha x (by simp [hx])).trans (by omega))
      (fun x hx => (hb x (by simp [hx])).trans (by omega))
    rw [ripple_cons]
    simp only [List.length_cons, Nat.succ_min_succ, List.length_append, adderGates_length]
    refine ⟨⟨fun g hg => ?_, fun o ho => ?_⟩, by omega, by omega⟩
    · rcases List.mem_append.mp hg with hg | hg
      · simp only [Plain.adderGates, List.mem_cons, List.mem_nil_iff, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
      · have := r1 g hg; omega
    · rcases List.mem_cons.mp ho with rfl | ho
      · omega
      · have := r2 o ho; omega

theorem gateS_le {W : ℕ} (e : ℕ × ℕ) (g : Plain.GateP) (h : g.2.2.1 ≤ W ∧ g.2.2.2 ≤ W) :
    (Plain.gateS e g).2.2.1 ≤ W + e.2 ∧ (Plain.gateS e g).2.2.2 ≤ W + e.2 := by
  have s1 : Plain.shiftWire e g.2.2.1 ≤ g.2.2.1 + e.2 := by
    unfold Plain.shiftWire; split <;> omega
  have s2 : Plain.shiftWire e g.2.2.2 ≤ g.2.2.2 + e.2 := by
    unfold Plain.shiftWire; split <;> omega
  unfold Plain.gateS
  split
  · split
    · omega
    · dsimp only; omega
  · dsimp only; omega

theorem countTree_inv (v z X : ℕ) (hv : v ≤ X) (hz : z ≤ X) : ∀ (k : ℕ) (xs : List ℕ),
    (∀ a ∈ xs, a ≤ X) →
    PInv (X + (Plain.countTree v k xs z).1.length) (Plain.countTree v k xs z) ∧
    (Plain.countTree v k xs z).1.length ≤ 5 * k * 2 ^ k ∧
    (Plain.countTree v k xs z).2.length ≤ xs.length + k + 1
  | 0, xs, hx => by
    simp only [Plain.countTree, List.length_nil]
    exact ⟨⟨by simp, fun o ho => (hx o ho).trans (by omega)⟩, by simp, by omega⟩
  | k + 1, xs, hx => by
    obtain ⟨⟨l1, l2⟩, l3, l4⟩ := countTree_inv v z X hv hz k (xs.take (xs.length / 2))
      (fun a ha => hx a (List.mem_of_mem_take ha))
    obtain ⟨⟨q1, q2⟩, q3, q4⟩ := countTree_inv v z X hv hz k (xs.drop (xs.length / 2))
      (fun a ha => hx a (List.mem_of_mem_drop ha))
    rw [countTree_succ]
    generalize Plain.countTree v k (xs.take (xs.length / 2)) z = L at *
    generalize Plain.countTree v k (xs.drop (xs.length / 2)) z = R at *
    set W := X + L.1.length + R.1.length with hW
    -- the combined program before the ripple
    have hG : ∀ g ∈ L.1 ++ Plain.gatesS (v, L.1.length) R.1, g.2.2.1 ≤ W ∧ g.2.2.2 ≤ W := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · have := l1 g hg; omega
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        have := gateS_le (v, L.1.length) g' (q1 g' hg')
        dsimp only at this; omega
    have ho : ∀ o ∈ L.2 ++ Plain.wiresS (v, L.1.length) R.2, o ≤ W := by
      intro o ho
      rcases List.mem_append.mp ho with ho | ho
      · have := l2 o ho; omega
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have := q2 o' ho'
        have s : Plain.shiftWire (v, L.1.length) o' ≤ o' + L.1.length := by
          unfold Plain.shiftWire; split <;> omega
        omega
    have hgl : (L.1 ++ Plain.gatesS (v, L.1.length) R.1).length = L.1.length + R.1.length := by
      simp [Plain.gatesS]
    obtain ⟨⟨r1, r2⟩, r3, r4⟩ := ripple_inv
      ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).take (k + 1))
      ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).drop (k + 1))
      (v + (L.1 ++ Plain.gatesS (v, L.1.length) R.1).length) z W (by rw [hgl]; omega) (by omega)
      (fun a ha => ho a (List.mem_of_mem_take ha)) (fun a ha => ho a (List.mem_of_mem_drop ha))
    generalize hA : Plain.ripple (v + (L.1 ++ Plain.gatesS (v, L.1.length) R.1).length)
      ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).take (k + 1))
      ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).drop (k + 1)) z = A at r1 r2 r3 r4
    have hm : min ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).take (k + 1)).length
        ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).drop (k + 1)).length ≤ k + 1 := by
      have := List.length_take_le (k + 1) (L.2 ++ Plain.wiresS (v, L.1.length) R.2)
      omega
    generalize min ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).take (k + 1)).length
        ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).drop (k + 1)).length = mn at *
    have hlen : ((L.1 ++ Plain.gatesS (v, L.1.length) R.1) ++ A.1).length =
        L.1.length + R.1.length + 5 * mn := by rw [List.length_append, hgl, r3]
    simp only [treeCombine, hA]
    rw [hlen]
    have p1 : 5 * k * 2 ^ k * 2 + 5 * (k + 1) ≤ 5 * (k + 1) * 2 ^ (k + 1) := by
      have h2 : k + 1 ≤ 2 ^ (k + 1) := Nat.lt_two_pow_self.le
      rw [pow_succ] at h2 ⊢
      generalize 2 ^ k = P at *
      have e1 : 5 * (k + 1) * (P * 2) = 10 * (k * P) + 10 * P := by ring
      have e2 : 5 * k * P * 2 = 10 * (k * P) := by ring
      omega
    refine ⟨⟨fun g hg => ?_, fun o ho => ?_⟩, by omega, by omega⟩
    · rcases List.mem_append.mp hg with hg | hg
      · have := hG g hg; omega
      · have := r1 g hg; omega
    · have := r2 o ho; omega


/-! ## Signatures -/

section Pop
variable (x : Ix)

@[polyB] theorem adderGatesF_P : PolyB (adderGatesF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, adderGatesBody, Plain.adderGates])
    (by simp [Tm.CallsP, adderGatesBody, polyB])

set_option maxRecDepth 4096 in
theorem rippleF_P : PolyB (rippleF x) := by
  obtain ⟨ka, ca, ha⟩ := adderGatesF_P x
  refine ⟨_, _, polyB_chainμ (rippleF x) (fun p => p.2.1.length)
    (fun p => max p.1 p.2.2.2 + 5 * p.2.1.length + mag (.list .nat) p.2.1 +
      mag (.list .nat) p.2.2.1)
    (fun p => by omega) 6 (fun p => ?_) (K := ka + 3) (C := ca + 400) (by omega) (fun p => ?_)⟩
  · obtain ⟨(v : ℕ), xs, ys, (c : ℕ)⟩ := p
    have := mag_list_len .nat xs
    simp only [mag_prod, mag_nat]
    omega
  obtain ⟨(v : ℕ), xs, ys, (c : ℕ)⟩ := p
  dsimp only
  set μ := max v c + 5 * xs.length + mag (.list .nat) xs + mag (.list .nat) ys with hμ
  have L0 := le_G (ka + 2) (ca + 400) μ
  have L1 : 100 * G (ka + 2) (ca + 400) μ + 100 ≤ G (ka + 3) (ca + 400) μ :=
    G_lin100 _ _ μ (by omega)
  have hc : c ≤ μ := by rw [hμ]; omega
  rcases xs with _ | ⟨(a : ℕ), as⟩
  · left
    have e1 : rippleCost x v [] ys c = 30 := rfl
    have e2 : rippleDepth x v [] ys c = 2 := rfl
    have e3 : rippleMsize x v [] ys c = 4 * c.size + 20 := rfl
    have e4 : mag TProg (Plain.ripple v [] ys c) = 1 + (c + 1 + 1) + 1 := rfl
    have := natSize_le c
    simp only [rippleF_cost, rippleF_depth, rippleF_msize, rippleF_den, e1, e2, e3, e4]
    refine ⟨by omega, by omega, by omega, by omega⟩
  rcases ys with _ | ⟨(b : ℕ), bs⟩
  · left
    have e1 : rippleCost x v (a :: as) [] c = 30 := rfl
    have e2 : rippleDepth x v (a :: as) [] c = 2 := rfl
    have e3 : rippleMsize x v (a :: as) [] c = 4 * c.size + 20 := rfl
    have e4 : mag TProg (Plain.ripple v (a :: as) [] c) = 1 + (c + 1 + 1) + 1 := rfl
    have := natSize_le c
    simp only [rippleF_cost, rippleF_depth, rippleF_msize, rippleF_den, e1, e2, e3, e4]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · right
    have ea : mag (.list .nat) (a :: as) = a + 1 + mag (.list .nat) as := rfl
    have eb : mag (.list .nat) (b :: bs) = b + 1 + mag (.list .nat) bs := rfl
    have hla := mag_list_len .nat as
    refine ⟨(v + 5, as, bs, v + 4), by simp, ?_, ?_⟩
    · dsimp only; simp only [List.length_cons] at hμ; omega
    -- callee bounds
    have hv : v ≤ μ := by rw [hμ]; omega
    have hab : a + b ≤ μ := by rw [hμ]; omega
    obtain ⟨a1, a2, a3, -⟩ := addF_B x.add (v, 5)
    obtain ⟨b1, b2, b3, -⟩ := addF_B x.add (v, 4)
    obtain ⟨s1, s2, s3, -⟩ := fnB_at (succF_B x.succ) (K := ka + 2) (C := ca + 400) (by omega)
      (by omega) (show mag .nat v ≤ μ from hv)
    simp only [mag_prod, mag_nat] at a1 a2 a3 b1 b2 b3
    have g1 : G 2 300 (v + 5 + 1) ≤ G (ka + 2) (ca + 400) μ :=
      (G_mono le_rfl le_rfl (show v + 5 + 1 ≤ μ + 6 by omega)).trans
        ((le_of_eq (G_shift 2 300 6 μ)).trans (G_mono (by omega) (by omega) le_rfl))
    have g2 : G 2 300 (v + 4 + 1) ≤ G (ka + 2) (ca + 400) μ := (G_mono le_rfl le_rfl
      (show v + 4 + 1 ≤ v + 5 + 1 by omega)).trans g1
    have D1 : 5 * (μ + 0) + 16 ≤ G 1 0 μ := G_succ 0 0 μ
    have hz : mag (.prod .nat (.prod .nat (.prod .nat .nat))) (v, a, b, c) ≤ G 1 0 μ := by
      simp only [mag_prod, mag_nat]; omega
    obtain ⟨d1, d2, d3, d4⟩ := ha (v, a, b, c)
    have c1 : G ka ca (G 1 0 μ) ≤ G (ka + 2) (ca + 400) μ :=
      (G_comp ka ca 1 0 μ).trans (G_mono (by omega) (by omega) le_rfl)
    have b0 := G_mono (k := ka) (c := ca) le_rfl le_rfl hz
    have Q1 : G 1 0 μ ≤ G (ka + 2) (ca + 400) μ := G_mono (by omega) (by omega) le_rfl
    have z1 := sz_le (.prod .nat (.prod .nat (.prod .nat .nat))) (v, a, b, c)
    have z2 := sz_le (.prod .nat (.prod (.list .nat) (.prod (.list .nat) .nat))) (v + 5, as, bs, v + 4)
    have z3 := sz_le TProg (Plain.ripple v (a :: as) (b :: bs) c)
    have hy2 : mag (.prod .nat (.prod (.list .nat) (.prod (.list .nat) .nat))) (v + 5, as, bs, v + 4)
        ≤ 2 * μ + 12 := by simp only [mag_prod, mag_nat]; omega
    -- the result
    have hr : mag TProg (Plain.ripple v (a :: as) (b :: bs) c) ≤
        mag TGates (Plain.adderGates v a b c) + v + 3 +
          mag TProg (Plain.ripple (v + 5) as bs (v + 4)) := by
      rw [ripple_cons]
      have := mag_append_le TGate (Plain.adderGates v a b c) (Plain.ripple (v + 5) as bs (v + 4)).1
      have e : mag TProg (Plain.ripple (v + 5) as bs (v + 4)) =
          mag TGates (Plain.ripple (v + 5) as bs (v + 4)).1 +
            mag (.list .nat) (Plain.ripple (v + 5) as bs (v + 4)).2 + 1 := rfl
      have e2 : mag TProg (Plain.adderGates v a b c ++ (Plain.ripple (v + 5) as bs (v + 4)).1,
          (v + 1) :: (Plain.ripple (v + 5) as bs (v + 4)).2) =
          mag TGates (Plain.adderGates v a b c ++ (Plain.ripple (v + 5) as bs (v + 4)).1) +
            (v + 1 + 1 + mag (.list .nat) (Plain.ripple (v + 5) as bs (v + 4)).2) + 1 := rfl
      omega
    simp only [adderGatesF_den] at d4
    have e1 : rippleCost x v (a :: as) (b :: bs) c = (addF x.add).cost (v, 5) +
        (addF x.add).cost (v, 4) + (adderGatesF x).cost (v, a, b, c) + (succF x.succ).cost v +
        rippleCost x (v + 5) as bs (v + 4) + 200 := rfl
    have e2 : rippleDepth x v (a :: as) (b :: bs) c = (addF x.add).depth (v, 5) +
        (addF x.add).depth (v, 4) + (adderGatesF x).depth (v, a, b, c) + (succF x.succ).depth v +
        rippleDepth x (v + 5) as bs (v + 4) + 20 := rfl
    have e3 : rippleMsize x v (a :: as) (b :: bs) c = (addF x.add).msize (v, 5) +
        (addF x.add).msize (v, 4) + (adderGatesF x).msize (v, a, b, c) + (succF x.succ).msize v +
        (Ty.enc (.prod .nat (.prod .nat (.prod .nat .nat))) (v, a, b, c)).size +
        (Ty.enc (.prod .nat (.prod (.list .nat) (.prod (.list .nat) .nat))) (v + 5, as, bs, v + 4)).size +
        3 * (Ty.enc TProg (Plain.ripple v (a :: as) (b :: bs) c)).size +
        rippleMsize x (v + 5) as bs (v + 4) + 20 := rfl
    simp only [rippleF_cost, rippleF_depth, rippleF_msize, rippleF_den, e1, e2, e3]
    refine ⟨by omega, by omega, by omega, by omega⟩

attribute [polyB] rippleF_P

@[polyB] theorem treeSplitF_P : PolyB (treeSplitF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, treeSplitBody, treeSplit])
    (by simp [Tm.CallsP, treeSplitBody, polyB])

@[polyB] theorem treeCombineF_P : PolyB (treeCombineF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, treeCombineBody, combFinish, treeCombine])
    (by simp [Tm.CallsP, treeCombineBody, combFinish, polyB])

/-! ## The adder tree on admissible arguments -/

/-- Admissible arguments of the adder tree: `2^k ≤ |xs| + 1`. -/
abbrev CTQ (p : (TTreeArg).den) : Prop := 2 ^ p.2.1 ≤ p.2.2.1.length + 1

theorem ctq_split {k : ℕ} {xs : List ℕ} (h : 2 ^ (k + 1) ≤ xs.length + 1) :
    2 ^ k ≤ (xs.take (xs.length / 2)).length + 1 ∧
      2 ^ k ≤ (xs.drop (xs.length / 2)).length + 1 := by
  rw [pow_succ] at h
  simp only [List.length_take, List.length_drop]
  generalize 2 ^ k = P at *
  constructor <;> omega

theorem countTree_mag (p : (TTreeArg).den) (hq : CTQ p) :
    mag TProg (Plain.countTree p.1 p.2.1 p.2.2.1 p.2.2.2) ≤ G 4 300 (mag TTreeArg p) := by
  obtain ⟨(v : ℕ), (k : ℕ), xs, (z : ℕ)⟩ := p
  change 2 ^ k ≤ xs.length + 1 at hq
  dsimp only
  set μ := mag TTreeArg (v, k, xs, z) with hμ
  have hxs := mag_list_len .nat xs
  have em : μ = v + (k + (mag (.list .nat) xs + z + 1) + 1) + 1 := rfl
  obtain ⟨hI, hg, ho⟩ := countTree_inv v z μ (by omega) (by omega) k xs (fun a ha => by
    have := mag_mem .nat ha; simp only [mag_nat] at this; omega)
  have hm := mag_prog_le _ hI
  have hk2 : 2 ^ k ≤ μ := by omega
  have hkP : k * 2 ^ k ≤ (μ + 1) * (μ + 1) := Nat.mul_le_mul (by omega) (by omega)
  have e5 : 5 * k * 2 ^ k = 5 * (k * 2 ^ k) := by ring
  generalize (Plain.countTree v k xs z).1.length = ng at *
  generalize (Plain.countTree v k xs z).2.length = no at *
  have hP := sq_ge μ
  generalize hPdef : (μ + 1) * (μ + 1) = P at *
  have q1 : (ng + no + 2) * (2 * (μ + ng) + 10) ≤ (8 * P) * (22 * P) :=
    Nat.mul_le_mul (by omega) (by omega)
  have q2 : (8 * P) * (22 * P) = 176 * (P * P) := by ring
  have g1 : (μ + 300 + 1) * (μ + 300 + 1) + 16 ≤ G 1 300 μ := G_sq 0 300 μ
  have g1' : P ≤ G 1 300 μ := by
    have : (μ + 1) * (μ + 1) ≤ (μ + 300 + 1) * (μ + 300 + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have g2 : P * P ≤ G 2 300 μ := by
    have : (G 1 300 μ + 1) * (G 1 300 μ + 1) + 16 ≤ G 2 300 μ := G_sq 1 300 μ
    have : P * P ≤ (G 1 300 μ + 1) * (G 1 300 μ + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have g3 : 100 * G 2 300 μ + 100 ≤ G 3 300 μ := G_lin100 2 300 μ le_rfl
  have g4 : 5 * G 3 300 μ + 16 ≤ G 4 300 μ := G_succ 3 300 μ
  omega

theorem countTree_on (x : Ix) : ∃ K C, ∀ p, CTQ p → FnBAt (G K C) (countTreeF x) p := by
  obtain ⟨ks, cs, hs⟩ := treeSplitF_P x
  obtain ⟨kc, cc, hc⟩ := treeCombineF_P x
  -- the step bound
  have step : ∀ (v k z : ℕ) (xs : List ℕ), CTQ (v, k + 1, xs, z) →
      (treeSplitF x).cost (v, k + 1, xs, z) +
        (treeCombineF x).cost ((v, k + 1, xs, z), Plain.countTree v k (xs.take (xs.length / 2)) z,
          Plain.countTree v k (xs.drop (xs.length / 2)) z) + 100 ≤
        G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k + 1, xs, z)) ∧
      (treeSplitF x).depth (v, k + 1, xs, z) +
        (treeCombineF x).depth ((v, k + 1, xs, z), Plain.countTree v k (xs.take (xs.length / 2)) z,
          Plain.countTree v k (xs.drop (xs.length / 2)) z) + 10 ≤
        G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k + 1, xs, z)) ∧
      (treeSplitF x).msize (v, k + 1, xs, z) +
        (treeCombineF x).msize ((v, k + 1, xs, z), Plain.countTree v k (xs.take (xs.length / 2)) z,
          Plain.countTree v k (xs.drop (xs.length / 2)) z) +
        (Ty.enc (.prod TTreeArg (.prod TProg TProg)) ((v, k + 1, xs, z),
          Plain.countTree v k (xs.take (xs.length / 2)) z,
          Plain.countTree v k (xs.drop (xs.length / 2)) z)).size + 10 ≤
        G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k + 1, xs, z)) := by
    intro v k z xs hq
    set μ := mag TTreeArg (v, k + 1, xs, z) with hμ
    obtain ⟨q1, q2⟩ := ctq_split hq
    have m1 : mag TTreeArg (v, k, xs.take (xs.length / 2), z) ≤ μ := by
      have := mag_take .nat xs (xs.length / 2); simp only [hμ, mag_prod, mag_nat]; omega
    have m2 : mag TTreeArg (v, k, xs.drop (xs.length / 2), z) ≤ μ := by
      have := mag_drop .nat xs (xs.length / 2); simp only [hμ, mag_prod, mag_nat]; omega
    have hL := (countTree_mag (v, k, xs.take (xs.length / 2), z) q1).trans (G_mono le_rfl le_rfl m1)
    have hR := (countTree_mag (v, k, xs.drop (xs.length / 2), z) q2).trans (G_mono le_rfl le_rfl m2)
    dsimp only at hL hR
    have g5 : 5 * G 4 300 μ + 16 ≤ G 5 300 μ := G_succ 4 300 μ
    have g0 := le_G 4 300 μ
    have ha : mag (.prod TTreeArg (.prod TProg TProg)) ((v, k + 1, xs, z),
        Plain.countTree v k (xs.take (xs.length / 2)) z,
        Plain.countTree v k (xs.drop (xs.length / 2)) z) ≤ G 5 300 μ := by
      have e : mag (.prod TTreeArg (.prod TProg TProg)) ((v, k + 1, xs, z),
          Plain.countTree v k (xs.take (xs.length / 2)) z,
          Plain.countTree v k (xs.drop (xs.length / 2)) z) =
          μ + (mag TProg (Plain.countTree v k (xs.take (xs.length / 2)) z) +
            mag TProg (Plain.countTree v k (xs.drop (xs.length / 2)) z) + 1) + 1 := rfl
      omega
    obtain ⟨c1, c2, c3, -⟩ := hc ((v, k + 1, xs, z),
        Plain.countTree v k (xs.take (xs.length / 2)) z,
        Plain.countTree v k (xs.drop (xs.length / 2)) z)
    have b1 := G_mono (k := kc) (c := cc) le_rfl le_rfl ha
    have b2 : G kc cc (G 5 300 μ) ≤ G (ks + kc + 7) (cs + cc + 400) μ :=
      (G_comp kc cc 5 300 μ).trans (G_mono (by omega) (by omega) le_rfl)
    obtain ⟨s1, s2, s3, -⟩ := fnB_at hs (K := ks + kc + 7) (C := cs + cc + 400) (by omega)
      (by omega) (le_refl μ)
    have z1 := sz_le (.prod TTreeArg (.prod TProg TProg)) ((v, k + 1, xs, z),
        Plain.countTree v k (xs.take (xs.length / 2)) z,
        Plain.countTree v k (xs.drop (xs.length / 2)) z)
    have b3 : G 5 300 μ ≤ G (ks + kc + 7) (cs + cc + 400) μ := G_mono (by omega) (by omega) le_rfl
    have L1 : 100 * G (ks + kc + 7) (cs + cc + 400) μ + 100 ≤ G (ks + kc + 8) (cs + cc + 400) μ :=
      G_lin100 _ _ μ (by omega)
    exact ⟨by omega, by omega, by omega⟩
  -- the three recursions
  have base : ∀ p : (TTreeArg).den, 30 + 2 + (Ty.enc (.list .nat) p.2.2.1).size +
      4 * p.2.2.2.size + 20 ≤ G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg p) := by
    intro p
    obtain ⟨(v : ℕ), (k : ℕ), xs, (z : ℕ)⟩ := p
    have h1 := sz_le (.list .nat) xs
    have h2 := natSize_le z
    have h3 : 5 * G (ks + kc + 7) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) + 16 ≤
        G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) := G_succ _ _ _
    have h4 := le_G (ks + kc + 7) (cs + cc + 400) (mag TTreeArg (v, k, xs, z))
    have e : mag TTreeArg (v, k, xs, z) = v + (k + (mag (.list .nat) xs + z + 1) + 1) + 1 := rfl
    dsimp only
    omega
  have tb : ∀ f : (TTreeArg).den → ℕ,
      (∀ p, CTQ p → p.2.1 = 0 → f p ≤ G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg p)) →
      (∀ v k z xs, CTQ (v, k + 1, xs, z) → f (v, k + 1, xs, z) ≤
        G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k + 1, xs, z)) +
        f (v, k, xs.take (xs.length / 2), z) + f (v, k, xs.drop (xs.length / 2), z)) →
      ∀ p, CTQ p → f p ≤ 2 ^ (p.2.1 + 1) * G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg p) := by
    intro f h0 h1 p hp
    have := tree_bound (fun p : (TTreeArg).den => p.2.1) (fun p => mag TTreeArg p)
      (fun p => if CTQ p then f p else 0) (G (ks + kc + 8) (cs + cc + 400)) (G_monotone _ _)
      (fun p => by
        obtain ⟨(v : ℕ), (k : ℕ), xs, (z : ℕ)⟩ := p
        by_cases hq : CTQ (v, k, xs, z)
        · rcases k with _ | k
          · left; simp only [if_pos hq]; exact h0 _ hq rfl
          · right
            obtain ⟨q1, q2⟩ := ctq_split hq
            refine ⟨(v, k, xs.take (xs.length / 2), z), (v, k, xs.drop (xs.length / 2), z),
              by simp, by simp, ?_, ?_, rfl, rfl, ?_⟩
            · have := mag_take .nat xs (xs.length / 2); simp only [mag_prod, mag_nat]; omega
            · have := mag_drop .nat xs (xs.length / 2); simp only [mag_prod, mag_nat]; omega
            · simp only [if_pos hq, if_pos q1, if_pos q2]; exact h1 v k z xs hq
        · left; simp only [if_neg hq]; exact Nat.zero_le _) p
    simp only [if_pos hp] at this
    exact this
  have fin : ∀ p : (TTreeArg).den, CTQ p → ∀ q,
      q ≤ 2 ^ (p.2.1 + 1) * G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg p) →
      q ≤ G (ks + kc + 9) (cs + cc + 400) (mag TTreeArg p) := by
    intro p hp q hq
    obtain ⟨(v : ℕ), (k : ℕ), xs, (z : ℕ)⟩ := p
    change 2 ^ k ≤ xs.length + 1 at hp
    dsimp only at hq ⊢
    have hx := mag_list_len .nat xs
    have e : mag TTreeArg (v, k, xs, z) = v + (k + (mag (.list .nat) xs + z + 1) + 1) + 1 := rfl
    have h2 : 2 ^ (k + 1) ≤ G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) := by
      have := le_G (ks + kc + 7) (cs + cc + 400) (mag TTreeArg (v, k, xs, z))
      have : 5 * G (ks + kc + 7) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) + 16 ≤
          G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) := G_succ _ _ _
      rw [pow_succ]; omega
    have h3 : 2 ^ (k + 1) * G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) ≤
        (G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) + 1) *
          (G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) + 1) *
        (G (ks + kc + 8) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) + 1) + 16 ≤
        G (ks + kc + 9) (cs + cc + 400) (mag TTreeArg (v, k, xs, z)) := G_sq _ _ _
    omega
  have hcost := tb (fun p => countTreeCost x p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p hp h0 => by
      obtain ⟨v, k, xs, z⟩ := p; dsimp only at h0; subst h0
      have := base (v, 0, xs, z); dsimp only at this; simp only [countTreeCost]; omega)
    (fun v k z xs hq => by
      have := (step v k z xs hq).1; simp only [countTreeCost]; omega)
  have hdepth := tb (fun p => countTreeDepth x p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p hp h0 => by
      obtain ⟨v, k, xs, z⟩ := p; dsimp only at h0; subst h0
      have := base (v, 0, xs, z); dsimp only at this; simp only [countTreeDepth]; omega)
    (fun v k z xs hq => by
      have := (step v k z xs hq).2.1; simp only [countTreeDepth]; omega)
  have hmsize := tb (fun p => countTreeMsize x p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p hp h0 => by
      obtain ⟨v, k, xs, z⟩ := p; dsimp only at h0; subst h0
      have := base (v, 0, xs, z); dsimp only at this; simp only [countTreeMsize]; omega)
    (fun v k z xs hq => by
      have := (step v k z xs hq).2.2; simp only [countTreeMsize]; omega)
  refine ⟨ks + kc + 9, cs + cc + 400, fun p hp => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact fin p hp _ (hcost p hp)
  · exact fin p hp _ (hdepth p hp)
  · exact fin p hp _ (hmsize p hp)
  · exact (countTree_mag p hp).trans (G_mono (by omega) (by omega) le_rfl)

/-! ## Population counter and weight block -/

theorem pow2Size_le (n : ℕ) : Plain.pow2Size n ≤ 2 * n + 1 := by
  unfold Plain.pow2Size
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : n.size - 1 < n.size := by have := NatSize.size_pos_of_ne (n := n) (by omega); omega
    have h2 : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp h1
    have h3 : 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
      rw [← pow_succ']; congr 1; have := NatSize.size_pos_of_ne (n := n) (by omega); omega
    omega

theorem pow2SizeF_B : FnB (G 2 300) (pow2SizeF x) := fnB_quad _ _ fun (n : ℕ) => by
  have h1 := natSize_le n
  have h2 := pow2Size_le n
  have hX := sq_ge n
  simp only [mag_nat, pow2SizeF_cost, pow2SizeF_depth, pow2SizeF_msize, pow2SizeF_den]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

@[polyB] theorem pow2SizeF_P : PolyB (pow2SizeF x) := ⟨_, _, pow2SizeF_B x⟩

@[polyB] theorem paddedWiresF_P : PolyB (paddedWiresF x) :=
  polyB_exact _ _ _ (fun n => by simp [tm_simp, paddedWiresBody, Plain.paddedWires])
    (by simp [Tm.CallsP, paddedWiresBody, polyB])

theorem paddedWires_length (n : ℕ) : 2 ^ (max 1 n).size ≤ (Plain.paddedWires n).length := by
  unfold Plain.paddedWires Plain.pow2Size
  simp only [List.length_append, List.length_range, List.length_replicate]
  have h1 := Nat.lt_size_self (max 1 n)
  generalize 2 ^ (max 1 n).size = P at *
  omega

theorem FnBAt.lift {a b : Ty} {F : FnSig a b} {y : a.den} {k c K C : ℕ} (h : FnBAt (G k c) F y)
    (hk : k ≤ K) (hc : c ≤ C) : FnBAt (G K C) F y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e := G_mono (m := mag a y) hk hc le_rfl
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e⟩

theorem populationF_P : PolyB (populationF x) := by
  obtain ⟨Kt, Ct, ht⟩ := countTree_on x
  obtain ⟨kp, cp, hp⟩ := paddedWiresF_P x
  refine polyB_of_bodyP (K := Kt + kp + 2) (C := Ct + cp + 300) (populationF x) (populationBody x)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun n => (by simp [tm_simp, populationBody, Plain.population] :
      (populationBody x).den (Env.one n) = Plain.population n).symm) (fun n => ?_)
  have hct : FnBAt (G (Kt + kp + 2 + 1) (Ct + cp + 300)) (countTreeF x)
      (n + 1, (max 1 n).size, Plain.paddedWires n, n) :=
    (ht _ (by
      show 2 ^ (max 1 n).size ≤ (Plain.paddedWires n).length + 1
      have := paddedWires_length n; omega)).lift (by omega) (by omega)
  simp only [Tm.CallsBP, populationBody]
  refine ⟨⟨hct, ?_⟩, ⟨⟨trivial, trivial⟩, trivial⟩⟩
  refine ⟨⟨fnBAt_of (succF_B _) (by omega) (by omega) _, trivial⟩, ⟨fnBAt_of (bitLenF_B _)
    (by omega) (by omega) _, fnBAt_of (maxF_B _) (by omega) (by omega) _, trivial, trivial⟩,
    ⟨fnBAt_of hp (by omega) (by omega) _, trivial⟩, trivial⟩

attribute [polyB] populationF_P

@[polyB] theorem weightBlockF_P : PolyB (weightBlockF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, weightBlockBody, Plain.weightBlock])
    (by simp [Tm.CallsP, weightBlockBody, polyB])

end Pop

end QecReliability.Trans.BoundsQH
