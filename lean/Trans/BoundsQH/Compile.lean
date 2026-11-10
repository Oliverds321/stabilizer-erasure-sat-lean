import Trans.BoundsQH.HComb
import Trans.Wire.Compile

/-!
# Trans.BoundsQH.Compile: polynomial bounds for the controller's compile wrapper

`compileF L c Q H base den D` (`Trans/Wire/Compile.lean`) calls the query function `Q` and,
for cell keys, the hash function `H` at `(base, den, q, scale, slice)` with the literal
constants `base`, `den`.

* `compileF_P`: if `Q` is `PolyB` and `H` is bounded by one `G kH cH` at every argument of the
  form `(base, den, q, r, bits)` (`base`, `den` fixed — the hash program's constants enter its
  bounds), then `compileF` is `PolyB`.
* `compile_poly`: the instance `Q = Query.queryFnF stdIx`; explicit form
  `∀ y, mag y ≤ M → cost/depth/msize/mag(result) ≤ G K C M` (monotone in `M`), which is what the
  controller-side bounds consume with `M = poly(paperL)` (every component of
  `(instX …, encKey key)` has magnitude `≤ poly(L)` at reachable states).
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Wire
open QecReliability.Trans.Control (bodySig TKey)
open QecReliability.Trans.Hash (THashArg)

/-- `bodySig` functions are polynomially bounded when their callees are. -/
theorem polyB_bodySig {a b : Ty} (i : ℕ) (body : Tm [a] b) (hc : Tm.CallsP body) :
    PolyB (bodySig i body) :=
  polyB_of_body _ body (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl) hc

section Compile
variable (L : Lib) (c : CIx) {Q : FnSig WQArg (.list .bool)} {H : FnSig THashArg WProg}
  (base den D : ℕ)

theorem sliceF_P : PolyB (sliceF L c) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, sliceBody, polyB])

theorem hashWF_P {kH cH : ℕ} (hH : ∀ q r bits, FnBAt (G kH cH) H (base, den, q, r, bits)) :
    PolyB (hashWF L c H base den) := by
  obtain ⟨ks, cs, hs⟩ := sliceF_P L c
  refine polyB_of_bodyP (K := kH + ks) (C := cH + cs) _ (hashWBody L c H base den)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => rfl) (fun y => ?_)
  simp only [Tm.CallsBP, hashWBody]
  refine ⟨(hH _ _ _).lift (by omega) (by omega), ⟨trivial, trivial, trivial, trivial,
    fnBAt_of hs (by omega) (by omega) _, trivial⟩⟩

theorem cellQF_P (hQ : PolyB Q) (hW : PolyB (hashWF L c H base den)) :
    PolyB (cellQF L c Q H base den D) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, cellQBody, polyB, hQ, hW])

theorem baseQF_P (hQ : PolyB Q) : PolyB (baseQF c Q D) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP, baseQBody, hQ])

/-- **The compile wrapper is polynomially bounded** (given the query function and the hash
function at the arguments with the fixed constants `base`, `den`). -/
theorem compileF_P (hQ : PolyB Q) {kH cH : ℕ}
    (hH : ∀ q r bits, FnBAt (G kH cH) H (base, den, q, r, bits)) :
    PolyB (compileF L c Q H base den D) :=
  polyB_bodySig _ _ (by
    simp [Tm.CallsP, compileBody, cellQF_P L c base den D hQ (hashWF_P L c base den hH),
      baseQF_P c D hQ])

end Compile

/-- `PolyB` in the "bounded magnitude" form consumed by budget arguments. -/
theorem PolyB.le_of_mag {a b : Ty} {F : FnSig a b} (h : PolyB F) :
    ∃ K C, ∀ (M : ℕ) (y : a.den), mag a y ≤ M →
      F.cost y ≤ G K C M ∧ F.depth y ≤ G K C M ∧ F.msize y ≤ G K C M ∧
        mag b (F.den y) ≤ G K C M ∧ (b.enc (F.den y)).size ≤ 5 * G K C M + 1 := by
  obtain ⟨K, C, hF⟩ := h
  refine ⟨K, C, fun M y hy => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hF y
  have e := G_mono (k := K) (c := C) le_rfl le_rfl hy
  have hs := sz_le b (F.den y)
  exact ⟨h1.trans e, h2.trans e, h3.trans e, h4.trans e, by omega⟩

/-- **Compile bound (modulo the hash bound).** For the query function `queryFnF stdIx` and any
hash function `H` bounded at the constant-`(base, den)` arguments, the compile wrapper has one
polynomial bound `G K C` (degree `2^K`, `G_poly`) in the magnitude of its argument: whenever
`mag (X, key) ≤ M`, the cost, depth, size budget, result magnitude and result size are
`≤ G K C M` (resp. `5 G K C M + 1`). -/
theorem compile_poly (L : Lib) (c : CIx) (H : FnSig THashArg WProg) (base den D : ℕ) {kH cH : ℕ}
    (hH : ∀ q r bits, FnBAt (G kH cH) H (base, den, q, r, bits)) :
    ∃ K C, ∀ (M : ℕ) (y : (Ty.prod TX TKey).den), mag (.prod TX TKey) y ≤ M →
      (compileF L c (Query.queryFnF Query.stdIx) H base den D).cost y ≤ G K C M ∧
      (compileF L c (Query.queryFnF Query.stdIx) H base den D).depth y ≤ G K C M ∧
      (compileF L c (Query.queryFnF Query.stdIx) H base den D).msize y ≤ G K C M ∧
      mag (.list .bool) ((compileF L c (Query.queryFnF Query.stdIx) H base den D).den y) ≤
        G K C M ∧
      (Ty.enc (.list .bool) ((compileF L c (Query.queryFnF Query.stdIx) H base den D).den y)).size
        ≤ 5 * G K C M + 1 :=
  (compileF_P L c base den D (queryFnF_P Query.stdIx) hH).le_of_mag

end QecReliability.Trans.BoundsQH
