import Trans.Query.FLPop

/-!
# Trans.Query.FLLayer: latent layer, hash cell, requests and the query bits

| FL | meaning |
|---|---|
| `pullbackF`, `layerBlockF` | `Plain.pullback/layerBlock` |
| `witnessF`, `quantumBlockF`, `quantumLayerF` | `Plain.witness/quantumBlock/quantumLayer` |
| `hashCellF`, `quantumCellF` | `Plain.hashCell/quantumCell` |
| `unitsF`, `requestF`, `queryF` | `Plain.units/request/query` |
| `baseQueryF`, `cellQueryF` | `Plain.baseQuery/cellQuery` |
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Query
open QecReliability.FL QecReliability.FL.Lib Tm NatSize

variable {P : Program}

/-! ## Latent pullback and layer -/

/-- Context `[lg, q, gs, s, (n, (r, (w, (C, B))))]` with `s = 2n + w`, `q = r + 2n + w`. -/
abbrev PullCtx : List Ty :=
  [Ty.nat, Ty.nat, TGates, Ty.nat, Ty.prod Ty.nat (Ty.prod Ty.nat (Ty.prod Ty.nat (Ty.prod TProg TBlock)))]

def pullFinish (x : Ix) : Tm PullCtx TBlock :=
  .pair (.app (addF x.add) (.pair v0 (.fst (.snd (.snd (.snd (.snd v4)))))))
    (.app (appendF TClause x.append)
      (.pair (.app (compileAtF x) (.pair v1 v2))
        (.app (formTF x) (.pair
          (.pair (.app (appendF .nat x.append) (.pair
              (.app (wiresSF x) (.pair (.pair (.fst (.snd v4)) v3) (.snd (.fst (.snd (.snd (.snd v4)))))))
              (.app (rangeFromF x.rangeFrom) (.pair (.fst (.snd v4)) v3))))
            (.pair (.app (addF x.add) (.pair (.app (mulF x.mul) (.pair (.lit (3 : ℕ)) (.fst v4)))
                (.fst (.snd (.snd v4)))))
              (.app (addF x.add) (.pair v1 v0))))
          (.snd (.snd (.snd (.snd (.snd v4)))))))))

/-- `v0 = (n, (r, (w, (C, B))))`. -/
def pullbackBody (x : Ix) : Tm [.prod .nat (.prod .nat (.prod .nat (.prod TProg TBlock)))] TBlock :=
  .letE (.app (addF x.add) (.pair (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v0))) (.fst (.snd (.snd v0)))))
  (.letE (.app (gatesSF x) (.pair (.pair (.fst (.snd v1)) v0) (.fst (.fst (.snd (.snd (.snd v1)))))))
  (.letE (.app (addF x.add) (.pair (.app (addF x.add) (.pair (.fst (.snd v2))
      (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v2))))) (.fst (.snd (.snd v2)))))
  (.letE (.app (lengthF TGate x.length) v1)
    (pullFinish x))))

def pullbackF (x : Ix) : FnSig (.prod .nat (.prod .nat (.prod .nat (.prod TProg TBlock)))) TBlock :=
  FnSig.exact x.pullback (pullbackBody x)
    (fun p => Plain.pullback p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

@[simp] theorem pullbackF_den (x : Ix)
    (p : (Ty.prod .nat (.prod .nat (.prod .nat (.prod TProg TBlock)))).den) :
    (pullbackF x).den p = Plain.pullback p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := rfl

theorem pullback_valid {x : Ix} (hL : LibOK P x) (hg : ∀ p, (gatesSF x).ValidAt P p)
    (hw : ∀ p, (wiresSF x).ValidAt P p) (hc : ∀ p, (compileAtF x).ValidAt P p)
    (hf : ∀ p, (formTF x).ValidAt P p)
    (hP : P[x.pullback]? = some (pullbackBody x).compile) : ∀ p, (pullbackF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, pullbackBody, pullFinish, hL, hg, hw, hc, hf])
    (fun p => by simp [tm_simp, pullbackBody, pullFinish, Plain.pullback])

/-- `v0 = (n, (r, (w, (C, (B, j)))))`. -/
def layerBlockBody (x : Ix) :
    Tm [.prod .nat (.prod .nat (.prod .nat (.prod TProg (.prod TBlock .nat))))] TBlock :=
  .letE (.app (addF x.add) (.pair (.app (addF x.add) (.pair (.fst (.snd v0))
      (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v0))))) (.fst (.snd (.snd v0)))))
    (.app (blockAndF x) (.pair v0 (.pair
      (.app (pullbackF x) (.pair (.fst v1) (.pair (.fst (.snd v1)) (.pair (.fst (.snd (.snd v1)))
        (.pair (.fst (.snd (.snd (.snd v1)))) (.fst (.snd (.snd (.snd (.snd v1))))))))))
      (.app (weightBlockF x) (.pair (.fst (.snd v1)) (.pair v0 (.snd (.snd (.snd (.snd (.snd v1)))))))))))

def layerBlockF (x : Ix) :
    FnSig (.prod .nat (.prod .nat (.prod .nat (.prod TProg (.prod TBlock .nat))))) TBlock :=
  FnSig.exact x.layerBlock (layerBlockBody x)
    (fun p => Plain.layerBlock p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

@[simp] theorem layerBlockF_den (x : Ix)
    (p : (Ty.prod .nat (.prod .nat (.prod .nat (.prod TProg (.prod TBlock .nat))))).den) :
    (layerBlockF x).den p = Plain.layerBlock p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := rfl

theorem layerBlock_valid {x : Ix} (hL : LibOK P x) (ha : ∀ p, (blockAndF x).ValidAt P p)
    (hp : ∀ p, (pullbackF x).ValidAt P p) (hw : ∀ p, (weightBlockF x).ValidAt P p)
    (hP : P[x.layerBlock]? = some (layerBlockBody x).compile) : ∀ p, (layerBlockF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, layerBlockBody, hL, ha, hp, hw])
    (fun p => by simp [tm_simp, layerBlockBody, Plain.layerBlock])

/-! ## Quantum blocks and layers -/

/-- `v0 = (n, (rows, side))`. -/
def witnessBody (x : Ix) : Tm [.prod .nat (.prod TRows .bool)] .nat :=
  .ite (.snd (.snd v0)) (.app (lengthF TRow x.length) (.app (filterNonemptyCF x) (.fst (.snd v0))))
    (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v0)))

def witnessF (x : Ix) : FnSig (.prod .nat (.prod TRows .bool)) .nat :=
  FnSig.exact x.witness (witnessBody x) (fun p => Plain.witness p.1 p.2.1 p.2.2)

@[simp] theorem witnessF_den (x : Ix) (p : (Ty.prod .nat (.prod TRows .bool)).den) :
    (witnessF x).den p = Plain.witness p.1 p.2.1 p.2.2 := rfl

theorem witness_valid {x : Ix} (hL : LibOK P x) (hf : ∀ p, (filterNonemptyCF x).ValidAt P p)
    (hP : P[x.witness]? = some (witnessBody x).compile) : ∀ p, (witnessF x).ValidAt P p :=
  FnSig.exact_valid hP
    (fun p => by obtain ⟨n, rows, side⟩ := p; cases side <;> simp [tm_simp, witnessBody, hL, hf])
    (fun p => by obtain ⟨n, rows, side⟩ := p; cases side <;> simp [tm_simp, witnessBody, Plain.witness])

/-- `v0 = (n, (rows, side))`. -/
def quantumBlockBody (x : Ix) : Tm [.prod .nat (.prod TRows .bool)] TBlock :=
  .ite (.snd (.snd v0)) (.app (goodBlockF x) (.pair (.fst v0) (.fst (.snd v0))))
    (.app (badBlockF x) (.pair (.fst v0) (.fst (.snd v0))))

def quantumBlockF (x : Ix) : FnSig (.prod .nat (.prod TRows .bool)) TBlock :=
  FnSig.exact x.quantumBlock (quantumBlockBody x) (fun p => Plain.quantumBlock p.1 p.2.1 p.2.2)

@[simp] theorem quantumBlockF_den (x : Ix) (p : (Ty.prod .nat (.prod TRows .bool)).den) :
    (quantumBlockF x).den p = Plain.quantumBlock p.1 p.2.1 p.2.2 := rfl

theorem quantumBlock_valid {x : Ix} (hg : ∀ p, (goodBlockF x).ValidAt P p)
    (hb : ∀ p, (badBlockF x).ValidAt P p)
    (hP : P[x.quantumBlock]? = some (quantumBlockBody x).compile) :
    ∀ p, (quantumBlockF x).ValidAt P p :=
  FnSig.exact_valid hP
    (fun p => by obtain ⟨n, rows, side⟩ := p; cases side <;> simp [tm_simp, quantumBlockBody, hg, hb])
    (fun p => by
      obtain ⟨n, rows, side⟩ := p; cases side <;> simp [tm_simp, quantumBlockBody, Plain.quantumBlock])

/-- Argument of `quantumLayer`: `(n, (r, (rows, (C, (side, j)))))`. -/
scoped notation "TLayerArg" =>
  Ty.prod Ty.nat (Ty.prod Ty.nat (Ty.prod TRows (Ty.prod TProg (Ty.prod Ty.bool Ty.nat))))

def quantumLayerBody (x : Ix) : Tm [TLayerArg] TBlock :=
  .app (layerBlockF x) (.pair (.fst v0) (.pair (.fst (.snd v0)) (.pair (.app (witnessF x) (.pair (.fst v0) (.pair (.fst (.snd (.snd v0))) (.fst (.snd (.snd (.snd (.snd v0)))))))) (.pair (.fst (.snd (.snd (.snd v0)))) (.pair (.app (quantumBlockF x) (.pair (.fst v0) (.pair (.fst (.snd (.snd v0))) (.fst (.snd (.snd (.snd (.snd v0)))))))) (.snd (.snd (.snd (.snd (.snd v0))))))))))

def quantumLayerF (x : Ix) : FnSig TLayerArg TBlock :=
  FnSig.exact x.quantumLayer (quantumLayerBody x)
    (fun p => Plain.quantumLayer p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

@[simp] theorem quantumLayerF_den (x : Ix) (p : (TLayerArg).den) :
    (quantumLayerF x).den p =
      Plain.quantumLayer p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := rfl

theorem quantumLayer_valid {x : Ix} (hl : ∀ p, (layerBlockF x).ValidAt P p)
    (hw : ∀ p, (witnessF x).ValidAt P p) (hq : ∀ p, (quantumBlockF x).ValidAt P p)
    (hP : P[x.quantumLayer]? = some (quantumLayerBody x).compile) :
    ∀ p, (quantumLayerF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, quantumLayerBody, hl, hw, hq])
    (fun p => by simp [tm_simp, quantumLayerBody, Plain.quantumLayer])

/-! ## Hash cell and quantum cell -/

/-- `v0 = (q, (w, (B, (H, target))))`. -/
def hashCellBody (x : Ix) :
    Tm [.prod .nat (.prod .nat (.prod TBlock (.prod TProg (.list .bool))))] TBlock :=
  .letE (.app (addF x.add) (.pair (.fst v0) (.fst (.snd v0))))
    (.app (blockAndF x) (.pair v0 (.pair (.fst (.snd (.snd v1)))
      (.app (matchBlockF x) (.pair v0 (.pair
        (.pair (.app (gatesSF x) (.pair (.pair (.fst v1) (.fst (.snd v1))) (.fst (.fst (.snd (.snd (.snd v1)))))))
          (.app (wiresSF x) (.pair (.pair (.fst v1) (.fst (.snd v1))) (.snd (.fst (.snd (.snd (.snd v1))))))))
        (.snd (.snd (.snd (.snd v1))))))))))

def hashCellF (x : Ix) :
    FnSig (.prod .nat (.prod .nat (.prod TBlock (.prod TProg (.list .bool))))) TBlock :=
  FnSig.exact x.hashCell (hashCellBody x)
    (fun p => Plain.hashCell p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

@[simp] theorem hashCellF_den (x : Ix)
    (p : (Ty.prod .nat (.prod .nat (.prod TBlock (.prod TProg (.list .bool))))).den) :
    (hashCellF x).den p = Plain.hashCell p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := rfl

theorem hashCell_valid {x : Ix} (hL : LibOK P x) (ha : ∀ p, (blockAndF x).ValidAt P p)
    (hm : ∀ p, (matchBlockF x).ValidAt P p) (hg : ∀ p, (gatesSF x).ValidAt P p)
    (hw : ∀ p, (wiresSF x).ValidAt P p)
    (hP : P[x.hashCell]? = some (hashCellBody x).compile) : ∀ p, (hashCellF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, hashCellBody, hL, ha, hm, hg, hw])
    (fun p => by simp [tm_simp, hashCellBody, Plain.hashCell])

/-- Argument of `quantumCell`: `(n, (r, (rows, (C, (side, (j, (H, target)))))))`. -/
scoped notation "TCellArg" =>
  Ty.prod Ty.nat (Ty.prod Ty.nat (Ty.prod TRows (Ty.prod TProg (Ty.prod Ty.bool (Ty.prod Ty.nat
    (Ty.prod TProg (Ty.list Ty.bool)))))))

def quantumCellBody (x : Ix) : Tm [TCellArg] TBlock :=
  .app (hashCellF x) (.pair (.app (addF x.add) (.pair (.fst (.snd v0)) (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v0))))) (.pair (.app (witnessF x) (.pair (.fst v0) (.pair (.fst (.snd (.snd v0))) (.fst (.snd (.snd (.snd (.snd v0)))))))) (.pair (.app (quantumLayerF x) (.pair (.fst v0) (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0))) (.pair (.fst (.snd (.snd (.snd v0)))) (.pair (.fst (.snd (.snd (.snd (.snd v0))))) (.fst (.snd (.snd (.snd (.snd (.snd v0)))))))))))) (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd v0))))))) (.snd (.snd (.snd (.snd (.snd (.snd (.snd v0)))))))))))

def quantumCellF (x : Ix) : FnSig TCellArg TBlock :=
  FnSig.exact x.quantumCell (quantumCellBody x)
    (fun p => Plain.quantumCell p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2)

@[simp] theorem quantumCellF_den (x : Ix) (p : (TCellArg).den) :
    (quantumCellF x).den p = Plain.quantumCell p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
      p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2 := rfl

theorem quantumCell_valid {x : Ix} (hL : LibOK P x) (hh : ∀ p, (hashCellF x).ValidAt P p)
    (hw : ∀ p, (witnessF x).ValidAt P p) (hq : ∀ p, (quantumLayerF x).ValidAt P p)
    (hP : P[x.quantumCell]? = some (quantumCellBody x).compile) :
    ∀ p, (quantumCellF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, quantumCellBody, hL, hh, hw, hq])
    (fun p => by simp [tm_simp, quantumCellBody, Plain.quantumCell])

/-! ## Prefix units, request, padded serialization -/

def unitsCost (x : Ix) : ℕ → ℕ → List Bool → ℕ
  | _, _, [] => 10
  | k, q, _ :: pre => (predF x.pred).cost q + (succF x.succ).cost k + unitsCost x (k + 1) (q - 1) pre + 60

def unitsDepth (x : Ix) : ℕ → ℕ → List Bool → ℕ
  | _, _, [] => 1
  | k, q, _ :: pre => (predF x.pred).depth q + (succF x.succ).depth k + unitsDepth x (k + 1) (q - 1) pre + 5

def unitsMsize (x : Ix) : ℕ → ℕ → List Bool → ℕ
  | k, _, [] => 4 * k.size + 10
  | k, q, b :: pre => (predF x.pred).msize q + (succF x.succ).msize k +
      (Ty.enc (.prod .nat (.prod .nat (.list .bool))) (k + 1, q - 1, pre)).size +
      (Ty.enc TForm (Plain.units k q (b :: pre))).size + unitsMsize x (k + 1) (q - 1) pre + 20

/-- `(k, (q, pre)) ↦ units k q pre`. -/
@[simps] def unitsF (x : Ix) : FnSig (.prod .nat (.prod .nat (.list .bool))) TForm where
  idx := x.units
  den p := Plain.units p.1 p.2.1 p.2.2
  cost p := unitsCost x p.1 p.2.1 p.2.2
  depth p := unitsDepth x p.1 p.2.1 p.2.2
  msize p := unitsMsize x p.1 p.2.1 p.2.2

def unitsBody (x : Ix) : Tm [.prod .nat (.prod .nat (.list .bool))] TForm :=
  .lcase (.snd (.snd v0)) .lnil
    (.ite (.isZero (.fst (.snd v2))) (.lcons .lnil .lnil)
      (.lcons (.lcons (.pair (.fst v2) v0) .lnil)
        (.app (unitsF x) (.pair (.app (succF x.succ) (.fst v2))
          (.pair (.app (predF x.pred) (.fst (.snd v2))) v1)))))

theorem units_valid {x : Ix} (hL : LibOK P x) (hP : P[x.units]? = some (unitsBody x).compile) :
    ∀ p, (unitsF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.2.length) ?_
  rintro ⟨(k : ℕ), (q : ℕ), (_ | ⟨b, pre⟩)⟩ ih
  · constructor <;> tm_auto [unitsBody, unitsCost, unitsDepth, unitsMsize, Plain.units]
  · rcases q with _ | q
    · have h1 : (Ty.enc TForm ([[]] : List (List (ℕ × Bool)))).size = 3 := rfl
      constructor <;> tm_auto [unitsBody, unitsCost, unitsDepth, unitsMsize, Plain.units]
    · have hih := ih (k + 1, q, pre) (by simp)
      have e1 := Ty.sz_list_cons TClause [(k, b)] (Plain.units (k + 1) q pre)
      constructor <;> tm_auto [unitsBody, unitsCost, unitsDepth, unitsMsize, Plain.units, hih,
        hL.succ, hL.pred]

/-- `v0 = (q, (w, (B, pre)))`. -/
def requestBody (x : Ix) : Tm [.prod .nat (.prod .nat (.prod TBlock (.list .bool)))] (.prod .nat TForm) :=
  .pair (.app (addF x.add) (.pair (.fst v0) (.app (addF x.add) (.pair (.fst (.snd v0))
      (.fst (.fst (.snd (.snd v0))))))))
    (.app (appendF TClause x.append) (.pair (.snd (.fst (.snd (.snd v0))))
      (.app (unitsF x) (.pair .zero (.pair (.fst v0) (.snd (.snd (.snd v0))))))))

def requestF (x : Ix) : FnSig (.prod .nat (.prod .nat (.prod TBlock (.list .bool)))) (.prod .nat TForm) :=
  FnSig.exact x.request (requestBody x) (fun p => Plain.request p.1 p.2.1 p.2.2.1 p.2.2.2)

@[simp] theorem requestF_den (x : Ix) (p : (Ty.prod .nat (.prod .nat (.prod TBlock (.list .bool)))).den) :
    (requestF x).den p = Plain.request p.1 p.2.1 p.2.2.1 p.2.2.2 := rfl

theorem request_valid {x : Ix} (hL : LibOK P x) (hu : ∀ p, (unitsF x).ValidAt P p)
    (hP : P[x.request]? = some (requestBody x).compile) : ∀ p, (requestF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, requestBody, hL, hu])
    (fun p => by simp [tm_simp, requestBody, Plain.request])

/-- The serializer at the indices of `x`. -/
abbrev encodeX (x : Ix) : FnSig (.prod .nat TForm) TBits :=
  encodeF x.literal x.literals x.clause x.body x.encode

/-- `v0 = (D, (v, F))`. -/
def queryBody (x : Ix) : Tm [.prod .nat (.prod .nat TForm)] TBits :=
  .app (encodeX x) (.pair (.app (maxF x.max) (.pair (.fst (.snd v0))
      (.app (mulF x.mul) (.pair (.fst v0) (.app (lengthF TClause x.length) (.snd (.snd v0)))))))
    (.snd (.snd v0)))

def queryF (x : Ix) : FnSig (.prod .nat (.prod .nat TForm)) TBits :=
  FnSig.exact x.query (queryBody x) (fun p => Plain.query p.1 p.2)

@[simp] theorem queryF_den (x : Ix) (p : (Ty.prod .nat (.prod .nat TForm)).den) :
    (queryF x).den p = Plain.query p.1 p.2 := rfl

theorem query_valid {x : Ix} (hL : LibOK P x) (he : ∀ p, (encodeX x).ValidAt P p)
    (hP : P[x.query]? = some (queryBody x).compile) : ∀ p, (queryF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, queryBody, hL, he])
    (fun p => by simp [tm_simp, queryBody, Plain.query])

/-! ## The query bits -/

/-- Argument of the base query: `(n, (r, (rows, (C, (side, (j, (pre, D)))))))`. -/
scoped notation "TBaseArg" =>
  Ty.prod Ty.nat (Ty.prod Ty.nat (Ty.prod TRows (Ty.prod TProg (Ty.prod Ty.bool (Ty.prod Ty.nat
    (Ty.prod (Ty.list Ty.bool) Ty.nat))))))

def baseQueryBody (x : Ix) : Tm [TBaseArg] TBits :=
  .app (queryF x) (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd v0))))))) (.app (requestF x) (.pair (.app (addF x.add) (.pair (.fst (.snd v0)) (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v0))))) (.pair (.app (witnessF x) (.pair (.fst v0) (.pair (.fst (.snd (.snd v0))) (.fst (.snd (.snd (.snd (.snd v0)))))))) (.pair (.app (quantumLayerF x) (.pair (.fst v0) (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0))) (.pair (.fst (.snd (.snd (.snd v0)))) (.pair (.fst (.snd (.snd (.snd (.snd v0))))) (.fst (.snd (.snd (.snd (.snd (.snd v0)))))))))))) (.fst (.snd (.snd (.snd (.snd (.snd (.snd v0))))))))))))

def baseQueryF (x : Ix) : FnSig TBaseArg TBits :=
  FnSig.exact x.baseQuery (baseQueryBody x)
    (fun p => Plain.baseQuery p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2)

@[simp] theorem baseQueryF_den (x : Ix) (p : (TBaseArg).den) :
    (baseQueryF x).den p = Plain.baseQuery p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2 := rfl

theorem baseQuery_valid {x : Ix} (hL : LibOK P x) (hq : ∀ p, (queryF x).ValidAt P p)
    (hr : ∀ p, (requestF x).ValidAt P p) (hw : ∀ p, (witnessF x).ValidAt P p)
    (hl : ∀ p, (quantumLayerF x).ValidAt P p)
    (hP : P[x.baseQuery]? = some (baseQueryBody x).compile) : ∀ p, (baseQueryF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, baseQueryBody, hL, hq, hr, hw, hl])
    (fun p => by simp [tm_simp, baseQueryBody, Plain.baseQuery])

/-- Argument of the cell query:
`(n, (r, (rows, (C, (side, (j, (H, (target, (pre, D)))))))))`. -/
scoped notation "TCellQArg" =>
  Ty.prod Ty.nat (Ty.prod Ty.nat (Ty.prod TRows (Ty.prod TProg (Ty.prod Ty.bool (Ty.prod Ty.nat
    (Ty.prod TProg (Ty.prod (Ty.list Ty.bool) (Ty.prod (Ty.list Ty.bool) Ty.nat))))))))

def cellQueryBody (x : Ix) : Tm [TCellQArg] TBits :=
  .app (queryF x) (.pair (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd v0))))))))) (.app (requestF x) (.pair (.app (addF x.add) (.pair (.fst (.snd v0)) (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v0))))) (.pair (.app (witnessF x) (.pair (.fst v0) (.pair (.fst (.snd (.snd v0))) (.fst (.snd (.snd (.snd (.snd v0)))))))) (.pair (.app (quantumCellF x) (.pair (.fst v0) (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0))) (.pair (.fst (.snd (.snd (.snd v0)))) (.pair (.fst (.snd (.snd (.snd (.snd v0))))) (.pair (.fst (.snd (.snd (.snd (.snd (.snd v0)))))) (.pair (.fst (.snd (.snd (.snd (.snd (.snd (.snd v0))))))) (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd v0)))))))))))))))) (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd v0))))))))))))))

def cellQueryF (x : Ix) : FnSig TCellQArg TBits :=
  FnSig.exact x.cellQuery (cellQueryBody x)
    (fun p => Plain.cellQuery p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2)

@[simp] theorem cellQueryF_den (x : Ix) (p : (TCellQArg).den) :
    (cellQueryF x).den p = Plain.cellQuery p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
      p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2 := rfl

theorem cellQuery_valid {x : Ix} (hL : LibOK P x) (hq : ∀ p, (queryF x).ValidAt P p)
    (hr : ∀ p, (requestF x).ValidAt P p) (hw : ∀ p, (witnessF x).ValidAt P p)
    (hc : ∀ p, (quantumCellF x).ValidAt P p)
    (hP : P[x.cellQuery]? = some (cellQueryBody x).compile) : ∀ p, (cellQueryF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, cellQueryBody, hL, hq, hr, hw, hc])
    (fun p => by simp [tm_simp, cellQueryBody, Plain.cellQuery])

end QecReliability.Trans.Query
