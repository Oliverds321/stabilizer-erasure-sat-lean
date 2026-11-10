import Trans.Query.FLBase

/-!
# Trans.Query.FLCirc: wire maps, gate clauses, circuit compilation, block combinators

FL transcriptions (meaning = the `Plain` function of the same name):

| FL | meaning |
|---|---|
| `shiftWireF`, `litSF`, `clauseSF`, `formSF` | `Plain.shiftWire/litS/clauseS/formS` |
| `tableWireF`, `litTF`, `clauseTF`, `formTF` | `Plain.tableWire/litT/clauseT/formT` |
| `gateSF`, `gatesSF`, `wiresSF` | `Plain.gateS/gatesS/wiresS` |
| `gateClausesF`, `compileAtF` | `Plain.gateClauses/compileAt` |
| `blockAndF`, `blockMergeF` | `Plain.blockAnd/blockMerge` |
| `outputUnitsF`, `matchBlockF` | `Plain.outputUnits/matchBlock` |
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Query
open QecReliability.FL QecReliability.FL.Lib Tm NatSize

variable {P : Program}

/-- Validity facts of the `FL.Lib` functions at the indices of `x`. -/
structure LibOK (P : Program) (x : Ix) : Prop where
  succ : ∀ y, (succF x.succ).ValidAt P y
  pred : ∀ y, (predF x.pred).ValidAt P y
  add : ∀ y, (addF x.add).ValidAt P y
  sub : ∀ y, (subF x.sub).ValidAt P y
  le : ∀ y, (leF x.le).ValidAt P y
  lt : ∀ y, (ltF x.lt).ValidAt P y
  eq : ∀ y, (eqF x.eq).ValidAt P y
  max : ∀ y, (maxF x.max).ValidAt P y
  mul : ∀ y, (mulF x.mul).ValidAt P y
  bitLen : ∀ y, (bitLenF x.bitLen).ValidAt P y
  div2 : ∀ y, (div2F x.div2).ValidAt P y
  length : ∀ t y, (lengthF t x.length).ValidAt P y
  append : ∀ t y, (appendF t x.append).ValidAt P y
  replicate : ∀ t y, (replicateF t x.replicate).ValidAt P y
  getD : ∀ t y, (getDF t x.getD).ValidAt P y
  take : ∀ t y, (takeF t x.take).ValidAt P y
  drop : ∀ t y, (dropF t x.drop).ValidAt P y
  rangeFrom : ∀ y, (rangeFromF x.rangeFrom).ValidAt P y
  range : ∀ y, (rangeF x.range).ValidAt P y

attribute [simp] LibOK.succ LibOK.pred LibOK.add LibOK.sub LibOK.le LibOK.lt LibOK.eq LibOK.max
  LibOK.mul LibOK.bitLen LibOK.div2 LibOK.length LibOK.append LibOK.replicate LibOK.getD LibOK.take LibOK.drop
  LibOK.rangeFrom LibOK.range

/-! ## Shifts -/

def shiftWireBody (x : Ix) : Tm [.prod TEnvS .nat] .nat :=
  .ite (.app (ltF x.lt) (.pair (.snd v0) (.fst (.fst v0)))) (.snd v0)
    (.app (addF x.add) (.pair (.snd v0) (.snd (.fst v0))))

def shiftWireF (x : Ix) : FnSig (.prod TEnvS .nat) .nat :=
  FnSig.exact x.shiftWire (shiftWireBody x) (fun p => Plain.shiftWire p.1 p.2)

@[simp] theorem shiftWireF_den (x : Ix) (p : (Ty.prod TEnvS .nat).den) :
    (shiftWireF x).den p = Plain.shiftWire p.1 p.2 := rfl

theorem shiftWire_valid {x : Ix} (hL : LibOK P x) (hP : P[x.shiftWire]? = some (shiftWireBody x).compile) :
    ∀ p, (shiftWireF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, shiftWireBody, hL])
    (fun p => by simp [tm_simp, shiftWireBody, Plain.shiftWire])

def litSBody (x : Ix) : Tm [.prod TEnvS TLit] TLit :=
  .pair (.app (shiftWireF x) (.pair (.fst v0) (.fst (.snd v0)))) (.snd (.snd v0))

def litSF (x : Ix) : FnSig (.prod TEnvS TLit) TLit :=
  FnSig.exact x.litS (litSBody x) (fun p => Plain.litS p.1 p.2)

@[simp] theorem litSF_den (x : Ix) (p : (Ty.prod TEnvS TLit).den) :
    (litSF x).den p = Plain.litS p.1 p.2 := rfl

theorem litS_valid {x : Ix} (hs : ∀ p, (shiftWireF x).ValidAt P p)
    (hP : P[x.litS]? = some (litSBody x).compile) : ∀ p, (litSF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, litSBody, hs])
    (fun p => by simp [tm_simp, litSBody, Plain.litS])

def clauseSF (x : Ix) : FnSig (.prod TEnvS TClause) TClause := mapEnvF (litSF x) x.clauseS

@[simp] theorem clauseSF_den (x : Ix) (p : (Ty.prod TEnvS TClause).den) :
    (clauseSF x).den p = Plain.clauseS p.1 p.2 := rfl
@[simp] theorem clauseSF_idx (x : Ix) : (clauseSF x).idx = x.clauseS := rfl

theorem clauseS_valid {x : Ix} (hl : ∀ p, (litSF x).ValidAt P p)
    (hP : P[x.clauseS]? = some (mapEnvBody (litSF x) x.clauseS).compile) :
    ∀ p, (clauseSF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => hl _)

def formSF (x : Ix) : FnSig (.prod TEnvS TForm) TForm := mapEnvF (clauseSF x) x.formS

@[simp] theorem formSF_den (x : Ix) (p : (Ty.prod TEnvS TForm).den) :
    (formSF x).den p = Plain.formS p.1 p.2 := rfl
@[simp] theorem formSF_idx (x : Ix) : (formSF x).idx = x.formS := rfl

theorem formS_valid {x : Ix} (hc : ∀ p, (clauseSF x).ValidAt P p)
    (hP : P[x.formS]? = some (mapEnvBody (clauseSF x) x.formS).compile) :
    ∀ p, (formSF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => hc _)

/-! ## Table lookups -/

def tableWireBody (x : Ix) : Tm [.prod TEnvT .nat] .nat :=
  .ite (.app (ltF x.lt) (.pair (.snd v0) (.fst (.snd (.fst v0)))))
    (.app (getDF .nat x.getD) (.pair (.fst (.fst v0)) (.pair (.snd v0) .zero)))
    (.app (addF x.add) (.pair (.snd (.snd (.fst v0)))
      (.app (subF x.sub) (.pair (.snd v0) (.fst (.snd (.fst v0)))))))

def tableWireF (x : Ix) : FnSig (.prod TEnvT .nat) .nat :=
  FnSig.exact x.tableWire (tableWireBody x) (fun p => Plain.tableWire p.1 p.2)

@[simp] theorem tableWireF_den (x : Ix) (p : (Ty.prod TEnvT .nat).den) :
    (tableWireF x).den p = Plain.tableWire p.1 p.2 := rfl

theorem tableWire_valid {x : Ix} (hL : LibOK P x) (hP : P[x.tableWire]? = some (tableWireBody x).compile) :
    ∀ p, (tableWireF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, tableWireBody, hL])
    (fun p => by simp [tm_simp, tableWireBody, Plain.tableWire])

def litTBody (x : Ix) : Tm [.prod TEnvT TLit] TLit :=
  .pair (.app (tableWireF x) (.pair (.fst v0) (.fst (.snd v0)))) (.snd (.snd v0))

def litTF (x : Ix) : FnSig (.prod TEnvT TLit) TLit :=
  FnSig.exact x.litT (litTBody x) (fun p => Plain.litT p.1 p.2)

@[simp] theorem litTF_den (x : Ix) (p : (Ty.prod TEnvT TLit).den) :
    (litTF x).den p = Plain.litT p.1 p.2 := rfl

theorem litT_valid {x : Ix} (hs : ∀ p, (tableWireF x).ValidAt P p)
    (hP : P[x.litT]? = some (litTBody x).compile) : ∀ p, (litTF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, litTBody, hs])
    (fun p => by simp [tm_simp, litTBody, Plain.litT])

def clauseTF (x : Ix) : FnSig (.prod TEnvT TClause) TClause := mapEnvF (litTF x) x.clauseT

@[simp] theorem clauseTF_den (x : Ix) (p : (Ty.prod TEnvT TClause).den) :
    (clauseTF x).den p = Plain.clauseT p.1 p.2 := rfl

theorem clauseT_valid {x : Ix} (hl : ∀ p, (litTF x).ValidAt P p)
    (hP : P[x.clauseT]? = some (mapEnvBody (litTF x) x.clauseT).compile) :
    ∀ p, (clauseTF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => hl _)

def formTF (x : Ix) : FnSig (.prod TEnvT TForm) TForm := mapEnvF (clauseTF x) x.formT

@[simp] theorem formTF_den (x : Ix) (p : (Ty.prod TEnvT TForm).den) :
    (formTF x).den p = Plain.formT p.1 p.2 := rfl

theorem formT_valid {x : Ix} (hc : ∀ p, (clauseTF x).ValidAt P p)
    (hP : P[x.formT]? = some (mapEnvBody (clauseTF x) x.formT).compile) :
    ∀ p, (formTF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => hc _)

/-! ## Gate maps -/

def gateSBody (x : Ix) : Tm [.prod TEnvS TGate] TGate :=
  .ite (.fst (.snd v0))
    (.ite (.fst (.snd (.snd v0))) (.snd v0)
      (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0)))
        (.pair (.app (shiftWireF x) (.pair (.fst v0) (.fst (.snd (.snd (.snd v0))))))
          (.snd (.snd (.snd (.snd v0))))))))
    (.pair (.fst (.snd v0)) (.pair (.fst (.snd (.snd v0)))
      (.pair (.app (shiftWireF x) (.pair (.fst v0) (.fst (.snd (.snd (.snd v0))))))
        (.app (shiftWireF x) (.pair (.fst v0) (.snd (.snd (.snd (.snd v0)))))))))

def gateSF (x : Ix) : FnSig (.prod TEnvS TGate) TGate :=
  FnSig.exact x.gateS (gateSBody x) (fun p => Plain.gateS p.1 p.2)

@[simp] theorem gateSF_den (x : Ix) (p : (Ty.prod TEnvS TGate).den) :
    (gateSF x).den p = Plain.gateS p.1 p.2 := rfl

theorem gateS_valid {x : Ix} (hs : ∀ p, (shiftWireF x).ValidAt P p)
    (hP : P[x.gateS]? = some (gateSBody x).compile) : ∀ p, (gateSF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, gateSBody, hs])
    (fun p => by
      obtain ⟨e, u, s, a, b⟩ := p
      cases u <;> cases s <;> simp [tm_simp, gateSBody, Plain.gateS])

def gatesSF (x : Ix) : FnSig (.prod TEnvS TGates) TGates := mapEnvF (gateSF x) x.gatesS

@[simp] theorem gatesSF_den (x : Ix) (p : (Ty.prod TEnvS TGates).den) :
    (gatesSF x).den p = Plain.gatesS p.1 p.2 := rfl

theorem gatesS_valid {x : Ix} (hg : ∀ p, (gateSF x).ValidAt P p)
    (hP : P[x.gatesS]? = some (mapEnvBody (gateSF x) x.gatesS).compile) :
    ∀ p, (gatesSF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => hg _)

def wiresSF (x : Ix) : FnSig (.prod TEnvS TWires) TWires := mapEnvF (shiftWireF x) x.wiresS

@[simp] theorem wiresSF_den (x : Ix) (p : (Ty.prod TEnvS TWires).den) :
    (wiresSF x).den p = Plain.wiresS p.1 p.2 := rfl

theorem wiresS_valid {x : Ix} (hs : ∀ p, (shiftWireF x).ValidAt P p)
    (hP : P[x.wiresS]? = some (mapEnvBody (shiftWireF x) x.wiresS).compile) :
    ∀ p, (wiresSF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => hs _)

/-! ## Gate clauses and compilation -/

section Clauses
variable {Γ : List Ty}

abbrev mkCl1 (a : Tm Γ TLit) : Tm Γ TClause := .lcons a .lnil
abbrev mkCl2 (a b : Tm Γ TLit) : Tm Γ TClause := .lcons a (.lcons b .lnil)
abbrev mkCl3 (a b c : Tm Γ TLit) : Tm Γ TClause := .lcons a (.lcons b (.lcons c .lnil))

end Clauses

/-- `v0 = (out, (u, s, a, b))`. -/
def gateClausesBody : Tm [.prod .nat TGate] TForm :=
  .ite (.fst (.snd v0))
    (.ite (.fst (.snd (.snd v0)))
      (.lcons (mkCl1 (.pair (.fst v0) (.isPos (.fst (.snd (.snd (.snd v0))))))) .lnil)
      (.lcons (mkCl2 (.pair (.fst (.snd (.snd (.snd v0)))) .tt) (.pair (.fst v0) .tt))
        (.lcons (mkCl2 (.pair (.fst (.snd (.snd (.snd v0)))) .ff) (.pair (.fst v0) .ff)) .lnil)))
    (.ite (.fst (.snd (.snd v0)))
      (.lcons (mkCl3 (.pair (.fst (.snd (.snd (.snd v0)))) .tt)
          (.pair (.snd (.snd (.snd (.snd v0)))) .tt) (.pair (.fst v0) .ff))
        (.lcons (mkCl3 (.pair (.fst (.snd (.snd (.snd v0)))) .tt)
            (.pair (.snd (.snd (.snd (.snd v0)))) .ff) (.pair (.fst v0) .tt))
          (.lcons (mkCl3 (.pair (.fst (.snd (.snd (.snd v0)))) .ff)
              (.pair (.snd (.snd (.snd (.snd v0)))) .tt) (.pair (.fst v0) .tt))
            (.lcons (mkCl3 (.pair (.fst (.snd (.snd (.snd v0)))) .ff)
                (.pair (.snd (.snd (.snd (.snd v0)))) .ff) (.pair (.fst v0) .ff)) .lnil))))
      (.lcons (mkCl3 (.pair (.fst (.snd (.snd (.snd v0)))) .ff)
          (.pair (.snd (.snd (.snd (.snd v0)))) .ff) (.pair (.fst v0) .tt))
        (.lcons (mkCl2 (.pair (.fst (.snd (.snd (.snd v0)))) .tt) (.pair (.fst v0) .ff))
          (.lcons (mkCl2 (.pair (.snd (.snd (.snd (.snd v0)))) .tt) (.pair (.fst v0) .ff)) .lnil))))

def gateClausesF (x : Ix) : FnSig (.prod .nat TGate) TForm :=
  FnSig.exact x.gateClauses gateClausesBody (fun p => Plain.gateClauses p.1 p.2)

@[simp] theorem gateClausesF_den (x : Ix) (p : (Ty.prod .nat TGate).den) :
    (gateClausesF x).den p = Plain.gateClauses p.1 p.2 := rfl

theorem gateClauses_valid {x : Ix} (hP : P[x.gateClauses]? = some gateClausesBody.compile) :
    ∀ p, (gateClausesF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, gateClausesBody])
    (fun p => by
      obtain ⟨o, u, s, a, b⟩ := p
      cases u <;> cases s <;> simp [tm_simp, gateClausesBody, Plain.gateClauses])

def compileAtCost (x : Ix) : ℕ → List Plain.GateP → ℕ
  | _, [] => 10
  | k, g :: gs => (gateClausesF x).cost (k, g) + 15 * (Plain.gateClauses k g).length +
      (succF x.succ).cost k + compileAtCost x (k + 1) gs + 60

def compileAtDepth (x : Ix) : ℕ → List Plain.GateP → ℕ
  | _, [] => 1
  | k, g :: gs => (gateClausesF x).depth (k, g) + (Plain.gateClauses k g).length +
      (succF x.succ).depth k + compileAtDepth x (k + 1) gs + 5

def compileAtMsize (x : Ix) : ℕ → List Plain.GateP → ℕ
  | _, [] => 0
  | k, g :: gs => (gateClausesF x).msize (k, g) + (succF x.succ).msize k +
      (Ty.enc (.prod .nat TGate) (k, g)).size + (Ty.enc (.prod .nat TGates) (k + 1, gs)).size +
      (Ty.enc TForm (Plain.compileAt k (g :: gs))).size + compileAtMsize x (k + 1) gs + 10

@[simps] def compileAtF (x : Ix) : FnSig (.prod .nat TGates) TForm where
  idx := x.compileAt
  den p := Plain.compileAt p.1 p.2
  cost p := compileAtCost x p.1 p.2
  depth p := compileAtDepth x p.1 p.2
  msize p := compileAtMsize x p.1 p.2

def compileAtBody (x : Ix) : Tm [.prod .nat TGates] TForm :=
  .lcase (.snd v0) .lnil
    (.app (appendF TClause x.append) (.pair (.app (gateClausesF x) (.pair (.fst v2) v0))
      (.app (compileAtF x) (.pair (.app (succF x.succ) (.fst v2)) v1))))

theorem compileAt_valid {x : Ix} (hL : LibOK P x) (hg : ∀ p, (gateClausesF x).ValidAt P p)
    (hP : P[x.compileAt]? = some (compileAtBody x).compile) :
    ∀ p, (compileAtF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.length) ?_
  rintro ⟨(k : ℕ), (_ | ⟨g, gs⟩)⟩ ih
  · constructor <;> tm_auto [compileAtBody, compileAtCost, compileAtDepth, compileAtMsize,
      Plain.compileAt]
  · have hih := ih (k + 1, gs) (by simp)
    have e1 := Ty.sz_list_append TClause (Plain.gateClauses k g) (Plain.compileAt (k + 1) gs)
    constructor <;> tm_auto [compileAtBody, compileAtCost, compileAtDepth, compileAtMsize,
      Plain.compileAt, hih, hg, hL.append, hL.succ]

/-! ## Block conjunction and merge -/

def blockAndBody (x : Ix) : Tm [.prod .nat (.prod TBlock TBlock)] TBlock :=
  .pair (.app (addF x.add) (.pair (.fst (.fst (.snd v0))) (.fst (.snd (.snd v0)))))
    (.app (appendF TClause x.append) (.pair (.snd (.fst (.snd v0)))
      (.app (formSF x) (.pair (.pair (.fst v0) (.fst (.fst (.snd v0)))) (.snd (.snd (.snd v0)))))))

def blockAndF (x : Ix) : FnSig (.prod .nat (.prod TBlock TBlock)) TBlock :=
  FnSig.exact x.blockAnd (blockAndBody x) (fun p => Plain.blockAnd p.1 p.2.1 p.2.2)

@[simp] theorem blockAndF_den (x : Ix) (p : (Ty.prod .nat (.prod TBlock TBlock)).den) :
    (blockAndF x).den p = Plain.blockAnd p.1 p.2.1 p.2.2 := rfl

theorem blockAnd_valid {x : Ix} (hL : LibOK P x) (hf : ∀ p, (formSF x).ValidAt P p)
    (hP : P[x.blockAnd]? = some (blockAndBody x).compile) : ∀ p, (blockAndF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, blockAndBody, hL, hf])
    (fun p => by simp [tm_simp, blockAndBody, Plain.blockAnd])

def blockMergeCost (x : Ix) (n : ℕ) : List Plain.BlockP → ℕ
  | [] => 10
  | B :: Bs => (blockAndF x).cost (n, B, Plain.blockMerge n Bs) + blockMergeCost x n Bs + 30

def blockMergeDepth (x : Ix) (n : ℕ) : List Plain.BlockP → ℕ
  | [] => 1
  | B :: Bs => (blockAndF x).depth (n, B, Plain.blockMerge n Bs) + blockMergeDepth x n Bs + 5

def blockMergeMsize (x : Ix) (n : ℕ) : List Plain.BlockP → ℕ
  | [] => 3
  | B :: Bs => (blockAndF x).msize (n, B, Plain.blockMerge n Bs) +
      (Ty.enc (.prod .nat (.prod TBlock TBlock)) (n, B, Plain.blockMerge n Bs)).size +
      (Ty.enc (.prod .nat (.list TBlock)) (n, Bs)).size + blockMergeMsize x n Bs + 10

@[simps] def blockMergeF (x : Ix) : FnSig (.prod .nat (.list TBlock)) TBlock where
  idx := x.blockMerge
  den p := Plain.blockMerge p.1 p.2
  cost p := blockMergeCost x p.1 p.2
  depth p := blockMergeDepth x p.1 p.2
  msize p := blockMergeMsize x p.1 p.2

def blockMergeBody (x : Ix) : Tm [.prod .nat (.list TBlock)] TBlock :=
  .lcase (.snd v0) (.pair .zero .lnil)
    (.app (blockAndF x) (.pair (.fst v2) (.pair v0 (.app (blockMergeF x) (.pair (.fst v2) v1)))))

theorem blockMerge_valid {x : Ix} (ha : ∀ p, (blockAndF x).ValidAt P p)
    (hP : P[x.blockMerge]? = some (blockMergeBody x).compile) :
    ∀ p, (blockMergeF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.length) ?_
  rintro ⟨(n : ℕ), (_ | ⟨B, Bs⟩)⟩ ih
  · have h0 : (Ty.enc TForm ([] : List (List (ℕ × Bool)))).size = 1 := rfl
    constructor <;> tm_auto [blockMergeBody, blockMergeCost, blockMergeDepth, blockMergeMsize,
      Plain.blockMerge]
  · have hih := ih (n, Bs) (by simp)
    constructor <;> tm_auto [blockMergeBody, blockMergeCost, blockMergeDepth, blockMergeMsize,
      Plain.blockMerge, hih, ha]

/-! ## Output units and match blocks -/

def outputUnitsCost : List ℕ → List Bool → ℕ
  | _ :: os, _ :: bs => outputUnitsCost os bs + 30
  | _, _ => 10

def outputUnitsMsize : List ℕ → List Bool → ℕ
  | o :: os, b :: bs => (Ty.enc (.list .nat) (o :: os)).size + (Ty.enc (.list .bool) (b :: bs)).size +
      (Ty.enc TForm (Plain.outputUnits (o :: os) (b :: bs))).size + outputUnitsMsize os bs + 10
  | _, _ => 0

@[simps] def outputUnitsF (x : Ix) : FnSig (.prod (.list .nat) (.list .bool)) TForm where
  idx := x.outputUnits
  den p := Plain.outputUnits p.1 p.2
  cost p := outputUnitsCost p.1 p.2
  depth p := p.1.length + 1
  msize p := outputUnitsMsize p.1 p.2

def outputUnitsBody (x : Ix) : Tm [.prod (.list .nat) (.list .bool)] TForm :=
  .lcase (.fst v0) .lnil
    (.lcase (.snd v2) .lnil
      (.lcons (.lcons (.pair v2 v0) .lnil) (.app (outputUnitsF x) (.pair v3 v1))))

theorem outputUnits_valid {x : Ix} (hP : P[x.outputUnits]? = some (outputUnitsBody x).compile) :
    ∀ p, (outputUnitsF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.1.length) ?_
  rintro ⟨(_ | ⟨o, os⟩), (_ | ⟨b, bs⟩)⟩ ih
  · constructor <;> tm_auto [outputUnitsBody, outputUnitsCost, outputUnitsMsize, Plain.outputUnits]
  · constructor <;> tm_auto [outputUnitsBody, outputUnitsCost, outputUnitsMsize, Plain.outputUnits]
  · constructor <;> tm_auto [outputUnitsBody, outputUnitsCost, outputUnitsMsize, Plain.outputUnits]
  · have hih := ih (os, bs) (by simp)
    have e1 := Ty.sz_list_cons TClause [(o, b)] (Plain.outputUnits os bs)
    constructor <;> tm_auto [outputUnitsBody, outputUnitsCost, outputUnitsMsize,
      Plain.outputUnits, hih]

/-- `v0 = (v, ((gates, outs), bits))`. -/
def matchBlockBody (x : Ix) : Tm [.prod .nat (.prod TProg (.list .bool))] TBlock :=
  .pair (.app (lengthF TGate x.length) (.fst (.fst (.snd v0))))
    (.app (appendF TClause x.append)
      (.pair (.app (compileAtF x) (.pair (.fst v0) (.fst (.fst (.snd v0)))))
        (.app (outputUnitsF x) (.pair (.snd (.fst (.snd v0))) (.snd (.snd v0))))))

def matchBlockF (x : Ix) : FnSig (.prod .nat (.prod TProg (.list .bool))) TBlock :=
  FnSig.exact x.matchBlock (matchBlockBody x) (fun p => Plain.matchBlock p.1 p.2.1 p.2.2)

@[simp] theorem matchBlockF_den (x : Ix) (p : (Ty.prod .nat (.prod TProg (.list .bool))).den) :
    (matchBlockF x).den p = Plain.matchBlock p.1 p.2.1 p.2.2 := rfl

theorem matchBlock_valid {x : Ix} (hL : LibOK P x) (hc : ∀ p, (compileAtF x).ValidAt P p)
    (ho : ∀ p, (outputUnitsF x).ValidAt P p)
    (hP : P[x.matchBlock]? = some (matchBlockBody x).compile) : ∀ p, (matchBlockF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, matchBlockBody, hL, hc, ho])
    (fun p => by simp [tm_simp, matchBlockBody, Plain.matchBlock])

end QecReliability.Trans.Query
