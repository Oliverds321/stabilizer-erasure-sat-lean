import Trans.BoundsRest.EndPoly
import Trans.BoundsRest.Compile

/-!
# Trans.BoundsRest.Endpoint: the endpoint callee within one polynomial envelope

`Control.endpointF` = `let a := ambF (n, rows, maskOf (r, side, P)) in (1, foldl dbl 1 (range a))`.
The first part (`ambT`) is `PolyB` (`EndPoly.ambF_P`, `maskOfF_P`); the doubling fold has
exponential *magnitude* (`2^a`) but cost `27 a + 10`, depth `≤ a + 2` and size budget
`O(a²)` (`dblFold_cost/_depth/_msize`, sizes are bit lengths). Hence (`endpointF_cdm`) cost,
depth and msize of `endpointF` are `≤ 200 (G+1)² + 200` with `G = G K C (mag arg)`.

The wrapper `endpointWF` only calls `endpointF`: forgetting the callee's result (`cdmSig`,
same index and bounds, meaning `0`) makes it a `PolyB` body (`endpointWF_cdm`).

**`endpoint_budget`**: one `PolynomialEnvelope` bounds cost/depth/msize of `x.endpoint` at
`(instX …, b)` for every instance and both sides — the `hend` hypothesis of
`BoundsStep.step_budget` (for `x.endpoint = endpointWF cI y`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.BoundsRest
open QecReliability.FL QecReliability.FL.Lib QecReliability.FL.Tm QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH
open QecReliability.Trans.Control
open QecReliability.Trans.Control.RankP
open QecReliability.Trans.Wire (TX instX CIx endpointWF endpointWBody Xn Xrows XC)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

/-- `F` with its result forgotten: same index and resource bounds, meaning `0`. -/
def cdmSig {a b : Ty} (F : FnSig a b) : FnSig a .nat :=
  ⟨F.idx, fun _ => 0, F.cost, F.depth, F.msize⟩

theorem size_two_mul (z : ℕ) : (2 * z).size ≤ z.size + 1 := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp
  · have := NatSize.size_half (n := 2 * z) (by omega)
    rw [show 2 * z / 2 = z by omega] at this
    omega

section End
variable (y : IxR)

/-- The argument type of `endpointF`. -/
abbrev TEArg : Ty := .prod (.prod .nat (.prod .nat (.prod TRowsP TProgP))) .bool

/-- The let-bound ambiguity term of `endpointBody`. -/
def ambT : Tm [TEArg] .nat :=
  .app (ambF y) (.pair (.fst (.fst v0)) (.pair (.fst (.snd (.snd (.fst v0))))
    (.app (maskOfF y) (.pair (.fst (.snd (.fst v0))) (.pair (.snd v0)
      (.snd (.snd (.snd (.fst v0)))))))))

/-- The rest of `endpointBody`: `(1, foldl dbl 1 (range a))`. -/
def restT : Tm [.nat, TEArg] TR :=
  .pair (.lit (1 : ℕ))
    (.app (foldlF (dblF y) y.dblFold) (.pair (.lit (1 : ℕ)) (.app (rangeF y.range) v0)))

theorem endpointBody_eq : endpointBody y = .letE (ambT y) (restT y) := rfl

/-! ## The doubling fold -/

theorem dbl_den (z x : ℕ) : (dblF y).den (z, x) = 2 * z := by
  simp [dblF, bodySig_den, dblBody, tm_simp, bitNat]

theorem dbl_cost (z x : ℕ) : (dblF y).cost (z, x) = 15 := by
  simp [dblF, bodySig_cost, dblBody, tm_simp]

theorem dbl_depth (z x : ℕ) : (dblF y).depth (z, x) = 1 := by
  simp [dblF, bodySig_depth, dblBody, tm_simp]

theorem dbl_msize (z x : ℕ) : (dblF y).msize (z, x) ≤ 4 * z.size + 10 := by
  have h1 := Ty.sz_nat_le (2 * z)
  have h2 := size_two_mul z
  have e : (dblF y).msize (z, x) = max (max 0 0) (max 5 (Enc.nat (bitNat false z)).size) := rfl
  rw [e]
  have e2 : bitNat false z = 2 * z := by simp [bitNat]
  rw [e2]
  have : (Enc.nat (2 * z)).size ≤ 4 * (2 * z).size + 1 := h1
  simp only [max_le_iff]
  omega

theorem dblFold_den : ∀ (l : List ℕ) (z : ℕ), foldlDen (dblF y) z l = 2 ^ l.length * z
  | [], z => by simp only [List.length_nil, pow_zero, one_mul]; rfl
  | x :: xs, z => by
    rw [foldlDen_cons, dbl_den, dblFold_den xs, List.length_cons, pow_succ]
    ring

theorem dblFold_cost : ∀ (l : List ℕ) (z : ℕ), foldlCost (dblF y) z l = 27 * l.length + 10
  | [], _ => rfl
  | x :: xs, z => by
    rw [foldlCost, dbl_cost, dblFold_cost xs, List.length_cons]
    ring

theorem dblFold_depth : ∀ (l : List ℕ) (z : ℕ), foldlDepth (dblF y) z l ≤ l.length + 2
  | [], _ => by simp
  | x :: xs, z => by
    have ih := dblFold_depth xs ((dblF y).den (z, x))
    rw [foldlDepth, dbl_depth, List.length_cons]
    simp only [max_le_iff]
    omega

theorem dblFold_msize : ∀ (l : List ℕ) (z : ℕ),
    foldlMsize (dblF y) z l ≤ 2 * (Ty.enc (.list .nat) l).size + 8 * (z.size + l.length) + 20
  | [], _ => by simp
  | x :: xs, z => by
    have ih := dblFold_msize xs ((dblF y).den (z, x))
    rw [dbl_den] at ih
    have h1 := dbl_msize y z x
    have h2 := size_two_mul z
    have h3 := Ty.sz_nat_le z
    have h4 := Ty.sz_nat_le (2 * z)
    have e1 := Bounds.shape2 (a := .nat) (b := .nat) z x
    have e2 := Bounds.shape2 (a := .nat) (b := .list .nat) (2 * z) xs
    have e3 := Ty.sz_list_cons .nat x xs
    rw [foldlMsize, dbl_den, List.length_cons]
    rw [e1, e2]
    simp only [max_le_iff]
    refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## `restT` -/

theorem restT_cost_arith {s1 fc a u : ℕ} (h1 : s1 ≤ 5) (hc : fc = 27 * a + 10) (hu : u ≤ a) :
    s1 + (s1 + (1 + (60 * (a + 1) * (u + 1) + 10)) + 1 + fc) + 1 ≤
      100 * ((a + 1) * (a + 1)) + 100 := by
  have m1 : (a + 1) * (u + 1) ≤ (a + 1) * (a + 1) := Nat.mul_le_mul le_rfl (by omega)
  have e60 : 60 * (a + 1) * (u + 1) = 60 * ((a + 1) * (u + 1)) := by ring
  have m3 : a + 1 ≤ (a + 1) * (a + 1) := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem restT_depth_arith {fd a u : ℕ} (hd : fd ≤ a + 2) (hu : u ≤ a) :
    max 0 (max (max 0 (max 0 (a + u + 3))) fd) ≤ 3 * a + 10 := by
  simp only [max_le_iff]
  omega

theorem restT_msize_arith {s1 sr fm fs a u : ℕ} (h1 : s1 ≤ 5) (hr : sr ≤ a * (4 * a + 2) + 1)
    (hm : fm ≤ 2 * sr + 8 * (1 + a) + 20) (hfs : fs ≤ 4 * (a + 1) + 1) (hu : u ≤ a) :
    max (max s1 (max (max (max s1 (max 0 (sr + 8 * u + 20))) (s1 + sr + 1)) fm)) (s1 + fs + 1) ≤
      30 * ((a + 1) * (a + 1)) + 100 := by
  have m2 : a * (4 * a + 2) ≤ 6 * ((a + 1) * (a + 1)) := by nlinarith
  have m3 : a + 1 ≤ (a + 1) * (a + 1) := Nat.le_mul_of_pos_left _ (by omega)
  simp only [max_le_iff]
  omega

theorem restT_bounds (a : ℕ) (ρ : Env [TEArg]) :
    (restT y).cost (.cons a ρ) ≤ 100 * ((a + 1) * (a + 1)) + 100 ∧
      (restT y).depth (.cons a ρ) ≤ 3 * a + 10 ∧
      (restT y).msize (.cons a ρ) ≤ 30 * ((a + 1) * (a + 1)) + 100 := by
  have hs := NatSize.size_le_self a
  have hr := Bounds.sz_range_le a
  have hc := dblFold_cost y (List.range a) (1 : ℕ)
  have hd := dblFold_depth y (List.range a) (1 : ℕ)
  have hm := dblFold_msize y (List.range a) (1 : ℕ)
  have hden := dblFold_den y (List.range a) (1 : ℕ)
  rw [List.length_range] at hc hd hm hden
  have hsz2 : (2 ^ a * 1).size ≤ a + 1 := by
    rw [mul_one, Nat.size_le]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hfs : (Ty.enc .nat (foldlDen (dblF y) (1 : ℕ) (List.range a))).size ≤ 4 * (a + 1) + 1 := by
    rw [hden]
    have := Ty.sz_nat_le (2 ^ a * 1)
    omega
  have h1 : (Ty.enc .nat (1 : ℕ)).size ≤ 5 := by
    have := Ty.sz_nat_le (1 : ℕ)
    rw [Nat.size_one] at this
    omega
  rw [Nat.size_one] at hm
  have ecost : (restT y).cost (.cons a ρ) = (Ty.enc .nat (1 : ℕ)).size +
      ((Ty.enc .nat (1 : ℕ)).size + (1 + (60 * (a + 1) * (a.size + 1) + 10)) + 1 +
        foldlCost (dblF y) (1 : ℕ) (List.range a)) + 1 := rfl
  have edepth : (restT y).depth (.cons a ρ) =
      max 0 (max (max 0 (max 0 (a + a.size + 3))) (foldlDepth (dblF y) (1 : ℕ) (List.range a))) :=
    rfl
  have emsize : (restT y).msize (.cons a ρ) =
      max (max (Ty.enc .nat (1 : ℕ)).size
        (max (max (max (Ty.enc .nat (1 : ℕ)).size
          (max 0 ((Ty.enc (.list .nat) (List.range a)).size + 8 * a.size + 20)))
          (Ty.enc (.prod .nat (.list .nat)) ((1 : ℕ), List.range a)).size)
          (foldlMsize (dblF y) (1 : ℕ) (List.range a))))
        (Ty.enc TR ((1 : ℕ), foldlDen (dblF y) (1 : ℕ) (List.range a))).size := rfl
  have es1 : (Ty.enc (.prod .nat (.list .nat)) ((1 : ℕ), List.range a)).size =
      (Ty.enc .nat (1 : ℕ)).size + (Ty.enc (.list .nat) (List.range a)).size + 1 :=
    Bounds.shape2 _ _
  have es2 : (Ty.enc TR ((1 : ℕ), foldlDen (dblF y) (1 : ℕ) (List.range a))).size =
      (Ty.enc .nat (1 : ℕ)).size + (Ty.enc .nat (foldlDen (dblF y) (1 : ℕ) (List.range a))).size
        + 1 := Bounds.shape2 _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [ecost]
    exact restT_cost_arith h1 hc hs
  · rw [edepth]
    exact restT_depth_arith hd hs
  · rw [emsize, es1, es2]
    exact restT_msize_arith h1 hr hm hfs hs

/-! ## `endpointF` -/

theorem endpoint_arith {A Dp M rc rd rm a g : ℕ} (hA : A + 2 ≤ g) (hD : Dp + 1 ≤ g) (hM : M ≤ g)
    (ha : a ≤ g) (r1 : rc ≤ 100 * ((a + 1) * (a + 1)) + 100) (r2 : rd ≤ 3 * a + 10)
    (r3 : rm ≤ 30 * ((a + 1) * (a + 1)) + 100) :
    A + rc + 1 + 2 ≤ 200 * ((g + 1) * (g + 1)) + 200 ∧ max Dp rd + 1 ≤ 5 * g + 20 ∧
      max M rm ≤ 200 * ((g + 1) * (g + 1)) + 200 := by
  have m : (a + 1) * (a + 1) ≤ (g + 1) * (g + 1) := Nat.mul_le_mul (by omega) (by omega)
  have m' : g + 1 ≤ (g + 1) * (g + 1) := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · have : max Dp rd ≤ 5 * g + 19 := max_le (by omega) (by omega)
    omega
  · exact max_le (by omega) (by omega)

/-- **Endpoint bound**: cost, depth and size budget of `endpointF` are polynomial in
`G K C (mag arg)` (its result `2^a` is not, which is why this is not `PolyB`). -/
theorem endpointF_cdm : ∃ K C, ∀ w : TEArg.den,
    (endpointF y).cost w ≤ 200 * ((G K C (mag TEArg w) + 1) * (G K C (mag TEArg w) + 1)) + 200 ∧
    (endpointF y).depth w ≤ 5 * G K C (mag TEArg w) + 20 ∧
    (endpointF y).msize w ≤ 200 * ((G K C (mag TEArg w) + 1) * (G K C (mag TEArg w) + 1)) + 200 := by
  obtain ⟨K, C, hB⟩ := polyB_bodySig 0 (ambT y)
    (by simp [Tm.CallsP, ambT, ambF_P, maskOfF_P])
  refine ⟨K, C, fun w => ?_⟩
  obtain ⟨b1, b2, b3, b4⟩ := hB w
  have ec : (endpointF y).cost w = (ambT y).cost (Env.one w) +
      (restT y).cost (.cons ((ambT y).den (Env.one w)) (Env.one w)) + 1 + 2 := rfl
  have ed : (endpointF y).depth w = max ((ambT y).depth (Env.one w))
      ((restT y).depth (.cons ((ambT y).den (Env.one w)) (Env.one w))) + 1 := rfl
  have em : (endpointF y).msize w = max ((ambT y).msize (Env.one w))
      ((restT y).msize (.cons ((ambT y).den (Env.one w)) (Env.one w))) := rfl
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (ambT y).den (Env.one w) = a := ⟨_, rfl⟩
  rw [ha] at ec ed em
  have b4' : a ≤ G K C (mag TEArg w) := by rw [← ha]; exact b4
  obtain ⟨r1, r2, r3⟩ := restT_bounds y a (Env.one w)
  rw [ec, ed, em]
  exact endpoint_arith b1 b2 b3 b4' r1 r2 r3

/-- The same as `PolyB` of the result-forgetting signature. -/
theorem endpointF_cdm_P : PolyB (cdmSig (endpointF y)) := by
  obtain ⟨K, C, h⟩ := endpointF_cdm y
  refine ⟨K + 5, C, fun w => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h w
  have g1 := G_sq K C (mag TEArg w)
  have g2 := G_succ (K + 1) C (mag TEArg w)
  have g3 := G_succ (K + 1 + 1) C (mag TEArg w)
  have g4 := G_succ (K + 1 + 1 + 1) C (mag TEArg w)
  have g5 := G_succ (K + 1 + 1 + 1 + 1) C (mag TEArg w)
  have g0 := le_G K C (mag TEArg w)
  have g6 : G K C (mag TEArg w) + 1 ≤ (G K C (mag TEArg w) + 1) * (G K C (mag TEArg w) + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have e5 : K + 1 + 1 + 1 + 1 + 1 = K + 5 := by omega
  rw [e5] at g5
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (endpointF y).cost w ≤ G (K + 5) C (mag TEArg w)
    omega
  · show (endpointF y).depth w ≤ G (K + 5) C (mag TEArg w)
    omega
  · show (endpointF y).msize w ≤ G (K + 5) C (mag TEArg w)
    omega
  · show mag .nat 0 ≤ _
    simp

/-! ## The wrapper -/

/-- `endpointWBody` with the callee's result forgotten. -/
def endpointWBody' : Tm [.prod TX .bool] .nat :=
  .app (cdmSig (endpointF y)) (.pair (.pair (Xn (.fst v0)) (.pair (Xn (.fst v0))
    (.pair (Xrows (.fst v0)) (XC (.fst v0))))) (.snd v0))

theorem endpointWF_cdm (c : CIx) : ∃ K C, ∀ w : (Ty.prod TX .bool).den,
    (endpointWF c y).cost w ≤ G K C (mag (.prod TX .bool) w) ∧
    (endpointWF c y).depth w ≤ G K C (mag (.prod TX .bool) w) ∧
    (endpointWF c y).msize w ≤ G K C (mag (.prod TX .bool) w) := by
  obtain ⟨K, C, h⟩ := polyB_bodySig c.endpointW (endpointWBody' y)
    (by simp [Tm.CallsP, endpointWBody', endpointF_cdm_P])
  refine ⟨K, C, fun w => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := h w
  exact ⟨h1, h2, h3⟩

end End

/-! ## The instance -/

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : CertifiedParity (512*t) (64*t) t)

/-- **Endpoint envelope.** One envelope bounds the endpoint callee `x.endpoint = endpointWF cI y` at
`(instX …, b)` for every instance and both sides (the `hend` hypothesis of
`BoundsStep.step_budget`). -/
theorem endpoint_budget (cI : CIx) (y : IxR) :
    ∃ P : PolynomialEnvelope, ∀ (x : Control.Ix TX), x.endpoint = endpointWF cI y →
      ∀ {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
        (coins : Fin (coinBits hD hd A c d (k+1)) → Bool), 0 < a → 0 < c → ∀ bb : Bool,
      x.endpoint.cost (instX hD hd A c d k rows coins, bb) ≤ P.eval (paperL rows a b c d) ∧
        x.endpoint.depth (instX hD hd A c d k rows coins, bb) ≤ P.eval (paperL rows a b c d) ∧
        x.endpoint.msize (instX hD hd A c d k rows coins, bb) ≤ P.eval (paperL rows a b c d) := by
  obtain ⟨K, C, h⟩ := endpointWF_cdm y cI
  obtain ⟨P, hP⟩ := (G_comp_pb K C (magK_pb (seedConstant hD hd A))).envelope
  refine ⟨P, fun x hx a b c d k rows coins ha hc bb => ?_⟩
  rw [hx]
  have hX := instX_mag_le hD hd A rows coins (b := b) ha hc
  have hm : mag (.prod TX .bool) (instX hD hd A c d k rows coins, bb) ≤
      magK (seedConstant hD hd A) (paperL rows a b c d) := by
    show mag TX (instX hD hd A c d k rows coins) + mag .bool bb + 1 ≤ _
    rw [mag_bool]
    unfold magK
    omega
  have hG := G_mono (k := K) (c := C) le_rfl le_rfl hm
  have hPL := hP (paperL rows a b c d)
  obtain ⟨h1, h2, h3⟩ := h (instX hD hd A c d k rows coins, bb)
  exact ⟨(h1.trans hG).trans hPL, (h2.trans hG).trans hPL, (h3.trans hG).trans hPL⟩

end QecReliability.Trans.BoundsRest
