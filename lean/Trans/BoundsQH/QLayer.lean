import Trans.BoundsQH.QPop
import Trans.Query.Main

/-!
# Trans.BoundsQH.QLayer: polynomial bounds for `Trans/Query/FLLayer.lean` and `queryFnF`

`unitsF` (recursion), the layer/cell/request/query signatures (`FnSig.exact`), and the main
result of the query side:

* **`queryFnF_P x : PolyB (queryFnF x)`** — for every index table `x`;
* **`queryFn_poly`**: explicit constants `K C` with
  `cost/depth/msize/mag(result) of (queryFnF stdIx) at y ≤ G K C (mag y) = B0^[K] (mag y + C)`,
  and `G K C m + 4 ≤ 26^(2^K - 1) (m + C + 4)^(2^K)` (`G_poly`).
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Query

section Layer
variable (x : Ix)

@[polyB] theorem pullbackF_P : PolyB (pullbackF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, pullbackBody, pullFinish, Plain.pullback])
    (by simp [Tm.CallsP, pullbackBody, pullFinish, polyB])

@[polyB] theorem layerBlockF_P : PolyB (layerBlockF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, layerBlockBody, Plain.layerBlock])
    (by simp [Tm.CallsP, layerBlockBody, polyB])

@[polyB] theorem witnessF_P : PolyB (witnessF x) :=
  polyB_exact _ _ _
    (fun p => by obtain ⟨n, rows, side⟩ := p; cases side <;> simp [tm_simp, witnessBody, Plain.witness])
    (by simp [Tm.CallsP, witnessBody, polyB])

@[polyB] theorem quantumBlockF_P : PolyB (quantumBlockF x) :=
  polyB_exact _ _ _
    (fun p => by
      obtain ⟨n, rows, side⟩ := p; cases side <;> simp [tm_simp, quantumBlockBody, Plain.quantumBlock])
    (by simp [Tm.CallsP, quantumBlockBody, polyB])

@[polyB] theorem quantumLayerF_P : PolyB (quantumLayerF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, quantumLayerBody, Plain.quantumLayer])
    (by simp [Tm.CallsP, quantumLayerBody, polyB])

@[polyB] theorem hashCellF_P : PolyB (hashCellF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, hashCellBody, Plain.hashCell])
    (by simp [Tm.CallsP, hashCellBody, polyB])

@[polyB] theorem quantumCellF_P : PolyB (quantumCellF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, quantumCellBody, Plain.quantumCell])
    (by simp [Tm.CallsP, quantumCellBody, polyB])

theorem unitsF_P : PolyB (unitsF x) := by
  refine ⟨_, _, polyB_chain (unitsF x) (fun p => p.2.2.length)
    (fun p => by have := mag_list_len .bool p.2.2; simp only [mag_prod]; omega)
    (K := 3) (C := 300) le_rfl (fun p => ?_)⟩
  obtain ⟨(k : ℕ), (q : ℕ), pre⟩ := p
  set μ := mag (.prod .nat (.prod .nat (.list .bool))) (k, q, pre) with hμ
  have L0 := le_G 2 300 μ
  have L1 : 100 * G 2 300 μ + 100 ≤ G 3 300 μ := G_lin100 2 300 μ le_rfl
  rcases pre with _ | ⟨b, pre⟩
  · left
    have := natSize_le k
    have e : mag TForm (Plain.units k q []) = 1 := by cases q <;> rfl
    simp only [unitsF_cost, unitsF_depth, unitsF_msize, unitsF_den, unitsCost, unitsDepth,
      unitsMsize, e]
    have : k ≤ μ := by rw [hμ]; simp only [mag_prod, mag_nat]; omega
    refine ⟨by omega, by omega, by omega, by omega⟩
  · right
    have hy : mag (.prod .nat (.prod .nat (.list .bool))) (k + 1, q - 1, pre) ≤ μ := by
      rw [hμ]; simp only [mag, magL]; omega
    refine ⟨(k + 1, q - 1, pre), by simp, hy, ?_⟩
    obtain ⟨p1, p2, p3, -⟩ := fnB_at (predF_B x.pred) (K := 2) (C := 300) le_rfl le_rfl
      (show mag .nat q ≤ μ by rw [hμ]; simp only [mag, magL]; omega)
    obtain ⟨s1, s2, s3, -⟩ := fnB_at (succF_B x.succ) (K := 2) (C := 300) le_rfl le_rfl
      (show mag .nat k ≤ μ by rw [hμ]; simp only [mag, magL]; omega)
    have z1 := sz_le (.prod .nat (.prod .nat (.list .bool))) (k + 1, q - 1, pre)
    have z2 := sz_le TForm (Plain.units k q (b :: pre))
    have hk : k ≤ μ := by rw [hμ]; simp only [mag, magL]; omega
    have hres : mag TForm (Plain.units k q (b :: pre)) ≤ k + 5 + mag TForm (Plain.units (k + 1) (q - 1) pre) := by
      rcases q with _ | q
      · show 1 + 1 + 1 ≤ _; omega
      · show (k + 1 + 1 + 1 + 1) + 1 + mag TForm (Plain.units (k + 1) q pre) ≤ _
        simp only [Nat.add_sub_cancel]; omega
    have hpos := mag_list_len TClause (Plain.units k q (b :: pre))
    simp only [unitsF_cost, unitsF_depth, unitsF_msize, unitsF_den, unitsCost, unitsDepth,
      unitsMsize]
    refine ⟨by omega, by omega, by omega, by omega⟩

attribute [polyB] unitsF_P

@[polyB] theorem requestF_P : PolyB (requestF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, requestBody, Plain.request])
    (by simp [Tm.CallsP, requestBody, polyB])

@[polyB] theorem encodeX_P : PolyB (encodeX x) := encodeF_P _ _ _ _ _

@[polyB] theorem queryF_P : PolyB (queryF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, queryBody, Plain.query])
    (by simp [Tm.CallsP, queryBody, polyB])

@[polyB] theorem baseQueryF_P : PolyB (baseQueryF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, baseQueryBody, Plain.baseQuery])
    (by simp [Tm.CallsP, baseQueryBody, polyB])

@[polyB] theorem cellQueryF_P : PolyB (cellQueryF x) :=
  polyB_exact _ _ _ (fun p => by simp [tm_simp, cellQueryBody, Plain.cellQuery])
    (by simp [Tm.CallsP, cellQueryBody, polyB])

/-- **The query function is polynomially bounded** (every index table). -/
@[polyB] theorem queryFnF_P : PolyB (queryFnF x) :=
  polyB_exact _ _ _
    (fun p => by obtain ⟨c, q⟩ := p; cases c <;> simp [tm_simp, queryFnBody, queryBits])
    (by simp [Tm.CallsP, queryFnBody, polyB])

end Layer

/-- Closed form of the bounding functions: a polynomial of degree `2^K`. -/
theorem G_poly (K C m : ℕ) : G K C m + 4 ≤ 26 ^ (2 ^ K - 1) * (m + C + 4) ^ (2 ^ K) :=
  B0_iter_le K (m + C)

/-- **Main result of the query side.** There are constants `K C` such that at every argument
`y`, the cost, depth, size budget and result magnitude of `queryFnF stdIx` are
`≤ G K C (mag y) ≤ 26^(2^K-1) (mag y + C + 4)^(2^K)`. -/
theorem queryFn_poly : ∃ K C : ℕ, ∀ y : (TQueryArg).den,
    (queryFnF stdIx).cost y ≤ G K C (mag TQueryArg y) ∧
    (queryFnF stdIx).depth y ≤ G K C (mag TQueryArg y) ∧
    (queryFnF stdIx).msize y ≤ G K C (mag TQueryArg y) ∧
    mag (.list .bool) ((queryFnF stdIx).den y) ≤ G K C (mag TQueryArg y) :=
  queryFnF_P stdIx

end QecReliability.Trans.BoundsQH
