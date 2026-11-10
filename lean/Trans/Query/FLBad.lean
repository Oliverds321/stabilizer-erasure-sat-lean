import Trans.Query.FLCirc

/-!
# Trans.Query.FLBad: sparse normalizer, pairing/support blocks, the Bad block

| FL | meaning |
|---|---|
| `coordWireF`, `rowWiresF`, `rowsWiresF` | coordinate wiring, `Plain.rowWires` (per row / all rows) |
| `parityGatesF`, `rowBlockF`, `rowBlocksF` | `Plain.parityGates/rowBlock` |
| `nonemptyF`, `filterNonemptyF` | `Plain.nonempty`, its filter |
| `normalizerF` | `Plain.normalizer` |
| `productParityGatesF`, `offsetPairF`, `offsetPairsF` | parity of products, offset pairs |
| `pairingPairsF`, `supportPairsF`, `supportClauseF`, `supportClausesF` | |
| `pairingBlockF`, `badBlockF` | `Plain.pairingBlock/badBlock` |
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Query
open QecReliability.FL QecReliability.FL.Lib Tm NatSize

variable {P : Program}

/-! ## Row wiring -/

def coordWireBody (x : Ix) : Tm [.prod TEnvS TCoord] .nat :=
  .ite (.fst (.snd v0)) (.app (addF x.add) (.pair (.fst (.fst v0)) (.snd (.snd v0))))
    (.app (addF x.add) (.pair (.snd (.fst v0)) (.snd (.snd v0))))

def coordWireF (x : Ix) : FnSig (.prod TEnvS TCoord) .nat :=
  FnSig.exact x.coordWire (coordWireBody x)
    (fun p => if p.2.1 then p.1.1 + p.2.2 else p.1.2 + p.2.2)

@[simp] theorem coordWireF_den (x : Ix) (p : (Ty.prod TEnvS TCoord).den) :
    (coordWireF x).den p = if p.2.1 then p.1.1 + p.2.2 else p.1.2 + p.2.2 := rfl

theorem coordWire_valid {x : Ix} (hL : LibOK P x) (hP : P[x.coordWire]? = some (coordWireBody x).compile) :
    ∀ p, (coordWireF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, coordWireBody, hL])
    (fun p => by obtain ⟨e, b, i⟩ := p; cases b <;> simp [tm_simp, coordWireBody])

def rowWiresF (x : Ix) : FnSig (.prod TEnvS TRow) TWires := mapEnvF (coordWireF x) x.rowWires

@[simp] theorem rowWiresF_den (x : Ix) (p : (Ty.prod TEnvS TRow).den) :
    (rowWiresF x).den p = Plain.rowWires p.1.1 p.1.2 p.2 := rfl

theorem rowWires_valid {x : Ix} (hc : ∀ p, (coordWireF x).ValidAt P p)
    (hP : P[x.rowWires]? = some (mapEnvBody (coordWireF x) x.rowWires).compile) :
    ∀ p, (rowWiresF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => hc _)

def rowsWiresF (x : Ix) : FnSig (.prod TEnvS TRows) (.list TWires) := mapEnvF (rowWiresF x) x.rowsWires

@[simp] theorem rowsWiresF_den (x : Ix) (p : (Ty.prod TEnvS TRows).den) :
    (rowsWiresF x).den p = p.2.map (fun row => Plain.rowWires p.1.1 p.1.2 row) := rfl

theorem rowsWires_valid {x : Ix} (hr : ∀ p, (rowWiresF x).ValidAt P p)
    (hP : P[x.rowsWires]? = some (mapEnvBody (rowWiresF x) x.rowsWires).compile) :
    ∀ p, (rowsWiresF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => hr _)

/-! ## Parity circuits and row blocks -/

def parityCost (x : Ix) (v : ℕ) : List ℕ → ℕ
  | [] => 20
  | _ :: xs => parityCost x v xs + 15 * (xs.length + 1) + (addF x.add).cost (v, xs.length) +
      (lengthF .nat x.length).cost xs + 60

def parityDepth (x : Ix) (v : ℕ) : List ℕ → ℕ
  | [] => 1
  | _ :: xs => parityDepth x v xs + xs.length + (addF x.add).depth (v, xs.length) +
      (lengthF .nat x.length).depth xs + 10

def parityMsize (x : Ix) (v : ℕ) : List ℕ → ℕ
  | [] => 20
  | y :: xs => parityMsize x v xs + (addF x.add).msize (v, xs.length) +
      (lengthF .nat x.length).msize xs + (Ty.enc (.prod .nat (.list .nat)) (v, y :: xs)).size +
      2 * (Ty.enc TGates (Plain.parityGates v (y :: xs))).size + 4 * (v + xs.length).size + 40

@[simps] def parityGatesF (x : Ix) : FnSig (.prod .nat (.list .nat)) TGates where
  idx := x.parityGates
  den p := Plain.parityGates p.1 p.2
  cost p := parityCost x p.1 p.2
  depth p := parityDepth x p.1 p.2
  msize p := parityMsize x p.1 p.2

def parityGatesBody (x : Ix) : Tm [.prod .nat (.list .nat)] TGates :=
  .lcase (.snd v0) (.lit ([Plain.constGate false] : List Plain.GateP))
    (.app (appendF TGate x.append) (.pair (.app (parityGatesF x) (.pair (.fst v2) v1))
      (.lcons (.pair .ff (.pair .tt (.pair v0 (.app (addF x.add)
        (.pair (.fst v2) (.app (lengthF .nat x.length) v1)))))) .lnil)))

theorem sz_constGate_list : (Ty.enc TGates [Plain.constGate false]).size = 13 := by
  simp [Ty.enc, Enc.list, Plain.constGate, Enc.bool, Enc.nat_zero]

theorem parityGates_length (v : ℕ) (xs : List ℕ) : (Plain.parityGates v xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons y xs ih => simp [Plain.parityGates, ih]

theorem parityGates_valid {x : Ix} (hL : LibOK P x)
    (hP : P[x.parityGates]? = some (parityGatesBody x).compile) :
    ∀ p, (parityGatesF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.length) ?_
  rintro ⟨(v : ℕ), (_ | ⟨y, xs⟩)⟩ ih
  · have h0 := sz_constGate_list
    constructor <;> tm_auto [parityGatesBody, parityCost, parityDepth, parityMsize, Plain.parityGates]
  · have hih := ih (v, xs) (by simp)
    have e1 := Ty.sz_list_append TGate (Plain.parityGates v xs) [(false, true, y, v + xs.length)]
    have e2 := parityGates_length v xs
    constructor <;> tm_auto [parityGatesBody, parityCost, parityDepth, parityMsize,
      Plain.parityGates, hih, hL.append, hL.add, hL.length]

/-- `v0 = (v, row)`; `rowBlock v row = (|row| + 1, compileAt v (parity v row) ++ [[(v + |row|, false)]])`. -/
def rowBlockBody (x : Ix) : Tm [.prod .nat (.list .nat)] TBlock :=
  .letE (.app (lengthF .nat x.length) (.snd v0))
    (.pair (.app (succF x.succ) v0)
      (.app (appendF TClause x.append)
        (.pair (.app (compileAtF x) (.pair (.fst v1) (.app (parityGatesF x) v1)))
          (.lcons (.lcons (.pair (.app (addF x.add) (.pair (.fst v1) v0)) .ff) .lnil) .lnil))))

def rowBlockF (x : Ix) : FnSig (.prod .nat (.list .nat)) TBlock :=
  FnSig.exact x.rowBlock (rowBlockBody x) (fun p => Plain.rowBlock p.1 p.2)

@[simp] theorem rowBlockF_den (x : Ix) (p : (Ty.prod .nat (.list .nat)).den) :
    (rowBlockF x).den p = Plain.rowBlock p.1 p.2 := rfl

theorem rowBlock_valid {x : Ix} (hL : LibOK P x) (hc : ∀ p, (compileAtF x).ValidAt P p)
    (hpar : ∀ p, (parityGatesF x).ValidAt P p)
    (hP : P[x.rowBlock]? = some (rowBlockBody x).compile) : ∀ p, (rowBlockF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, rowBlockBody, hL, hc, hpar])
    (fun p => by simp [tm_simp, rowBlockBody, Plain.rowBlock])

def rowBlocksF (x : Ix) : FnSig (.prod .nat (.list TWires)) (.list TBlock) :=
  mapEnvF (rowBlockF x) x.rowBlocks

@[simp] theorem rowBlocksF_den (x : Ix) (p : (Ty.prod .nat (.list TWires)).den) :
    (rowBlocksF x).den p = p.2.map (fun row => Plain.rowBlock p.1 row) := rfl

theorem rowBlocks_valid {x : Ix} (hr : ∀ p, (rowBlockF x).ValidAt P p)
    (hP : P[x.rowBlocks]? = some (mapEnvBody (rowBlockF x) x.rowBlocks).compile) :
    ∀ p, (rowBlocksF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => hr _)

/-! ## Nonempty rows -/

/-- `!row.isEmpty` (any element type; the compiled body does not depend on it). -/
def nonemptyBody (t : Ty) : Tm [.list t] .bool := .lcase v0 .ff .tt

def nonemptyF (t : Ty) (x : Ix) : FnSig (.list t) .bool :=
  FnSig.exact x.nonempty (nonemptyBody t) (fun row => !row.isEmpty)

@[simp] theorem nonemptyF_den (t : Ty) (x : Ix) (row : (Ty.list t).den) :
    (nonemptyF t x).den row = !row.isEmpty := rfl

theorem nonempty_valid {t : Ty} {x : Ix} (hP : P[x.nonempty]? = some (nonemptyBody t).compile) :
    ∀ p, (nonemptyF t x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by cases p <;> simp [tm_simp, nonemptyBody])
    (fun p => by cases p <;> simp [tm_simp, nonemptyBody])

def filterNonemptyF (x : Ix) : FnSig (.list TWires) (.list TWires) :=
  filterF (nonemptyF .nat x) x.filterNonempty

@[simp] theorem filterNonemptyF_den (x : Ix) (rows : (Ty.list TWires).den) :
    (filterNonemptyF x).den rows = rows.filter Plain.nonempty := rfl

theorem filterNonempty_valid {x : Ix} (hn : ∀ p, (nonemptyF .nat x).ValidAt P p)
    (hP : P[x.filterNonempty]? = some (filterBody (nonemptyF .nat x) x.filterNonempty).compile) :
    ∀ p, (filterNonemptyF x).ValidAt P p := fun p => filter_valid hP p (fun _ _ => hn _)

/-! ## Normalizer block -/

/-- `v0 = (v, ((ox, oz), rows))`. -/
def normalizerBody (x : Ix) : Tm [.prod .nat (.prod TEnvS TRows)] TBlock :=
  .app (blockMergeF x) (.pair (.fst v0)
    (.app (rowBlocksF x) (.pair (.fst v0) (.app (filterNonemptyF x) (.app (rowsWiresF x) (.snd v0))))))

def normalizerF (x : Ix) : FnSig (.prod .nat (.prod TEnvS TRows)) TBlock :=
  FnSig.exact x.normalizer (normalizerBody x) (fun p => Plain.normalizer p.1 p.2.1.1 p.2.1.2 p.2.2)

@[simp] theorem normalizerF_den (x : Ix) (p : (Ty.prod .nat (.prod TEnvS TRows)).den) :
    (normalizerF x).den p = Plain.normalizer p.1 p.2.1.1 p.2.1.2 p.2.2 := rfl

theorem normalizer_valid {x : Ix} (hm : ∀ p, (blockMergeF x).ValidAt P p)
    (hb : ∀ p, (rowBlocksF x).ValidAt P p) (hf : ∀ p, (filterNonemptyF x).ValidAt P p)
    (hw : ∀ p, (rowsWiresF x).ValidAt P p)
    (hP : P[x.normalizer]? = some (normalizerBody x).compile) : ∀ p, (normalizerF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, normalizerBody, hm, hb, hf, hw])
    (fun p => by simp [tm_simp, normalizerBody, Plain.normalizer])

/-! ## Parity of products -/

def ppCost (x : Ix) (v : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 20
  | _ :: ps => ppCost x v ps + 15 * (2 * ps.length + 1) + (addF x.add).cost (v, 2 * ps.length) +
      2 * (lengthF (.prod .nat .nat) x.length).cost ps + (succF x.succ).cost (v + 2 * ps.length) +
      4 * ps.length.size + 80

def ppDepth (x : Ix) (v : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 1
  | _ :: ps => ppDepth x v ps + 2 * ps.length + (addF x.add).depth (v, 2 * ps.length) +
      (lengthF (.prod .nat .nat) x.length).depth ps + (succF x.succ).depth (v + 2 * ps.length) + 10

def ppMsize (x : Ix) (v : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 20
  | p :: ps => ppMsize x v ps + (addF x.add).msize (v, 2 * ps.length) +
      (lengthF (.prod .nat .nat) x.length).msize ps + (succF x.succ).msize (v + 2 * ps.length) +
      (Ty.enc (.prod .nat (.list (.prod .nat .nat))) (v, p :: ps)).size +
      2 * (Ty.enc TGates (Plain.productParityGates v (p :: ps))).size +
      8 * (v + 2 * ps.length).size + 8 * ps.length.size + 60

@[simps] def productParityGatesF (x : Ix) : FnSig (.prod .nat (.list (.prod .nat .nat))) TGates where
  idx := x.productParityGates
  den p := Plain.productParityGates p.1 p.2
  cost p := ppCost x p.1 p.2
  depth p := ppDepth x p.1 p.2
  msize p := ppMsize x p.1 p.2

def productParityGatesBody (x : Ix) : Tm [.prod .nat (.list (.prod .nat .nat))] TGates :=
  .lcase (.snd v0) (.lit ([Plain.constGate false] : List Plain.GateP))
    (.letE (.app (addF x.add) (.pair (.fst v2) (.bit .ff (.app (lengthF (.prod .nat .nat) x.length) v1))))
      (.app (appendF TGate x.append) (.pair (.app (productParityGatesF x) (.pair (.fst v3) v2))
        (.lcons (.pair .ff (.pair .ff v1))
          (.lcons (.pair .ff (.pair .tt (.pair (.app (succF x.succ) v0) v0))) .lnil)))))

theorem productParityGates_length (v : ℕ) (ps : List (ℕ × ℕ)) :
    (Plain.productParityGates v ps).length = 2 * ps.length + 1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [Plain.productParityGates, ih]; omega

theorem productParityGates_valid {x : Ix} (hL : LibOK P x)
    (hP : P[x.productParityGates]? = some (productParityGatesBody x).compile) :
    ∀ p, (productParityGatesF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.length) ?_
  rintro ⟨(v : ℕ), (_ | ⟨⟨a, b⟩, ps⟩)⟩ ih
  · have h0 := sz_constGate_list
    constructor <;> tm_auto [productParityGatesBody, ppCost, ppDepth, ppMsize,
      Plain.productParityGates]
  · have hih := ih (v, ps) (by simp)
    have e1 := Ty.sz_list_append TGate (Plain.productParityGates v ps)
      [(false, false, a, b), (false, true, v + 2 * ps.length + 1, v + 2 * ps.length)]
    have e2 := productParityGates_length v ps
    have e3 := size_succ_le (v + 2 * ps.length)
    have e4 := Ty.sz_list_cons TGate (false, false, a, b)
      [(false, true, v + 2 * ps.length + 1, v + 2 * ps.length)]
    constructor <;> tm_auto [productParityGatesBody, ppCost, ppDepth, ppMsize,
      Plain.productParityGates, hih, hL.append, hL.add, hL.length, hL.succ]

/-! ## Offset pairs, pairing and support -/

def offsetPairBody (x : Ix) : Tm [.prod TEnvS .nat] (.prod .nat .nat) :=
  .pair (.app (addF x.add) (.pair (.fst (.fst v0)) (.snd v0)))
    (.app (addF x.add) (.pair (.snd (.fst v0)) (.snd v0)))

def offsetPairF (x : Ix) : FnSig (.prod TEnvS .nat) (.prod .nat .nat) :=
  FnSig.exact x.offsetPair (offsetPairBody x) (fun p => (p.1.1 + p.2, p.1.2 + p.2))

@[simp] theorem offsetPairF_den (x : Ix) (p : (Ty.prod TEnvS .nat).den) :
    (offsetPairF x).den p = (p.1.1 + p.2, p.1.2 + p.2) := rfl

theorem offsetPair_valid {x : Ix} (hL : LibOK P x) (hP : P[x.offsetPair]? = some (offsetPairBody x).compile) :
    ∀ p, (offsetPairF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, offsetPairBody, hL])
    (fun p => by simp [tm_simp, offsetPairBody])

/-- `((a, b), is) ↦ is.map (i ↦ (a + i, b + i))`. -/
def offsetPairsF (x : Ix) : FnSig (.prod TEnvS (.list .nat)) (.list (.prod .nat .nat)) :=
  mapEnvF (offsetPairF x) x.offsetPairs

@[simp] theorem offsetPairsF_den (x : Ix) (p : (Ty.prod TEnvS (.list .nat)).den) :
    (offsetPairsF x).den p = p.2.map (fun i => (p.1.1 + i, p.1.2 + i)) := rfl

theorem offsetPairs_valid {x : Ix} (ho : ∀ p, (offsetPairF x).ValidAt P p)
    (hP : P[x.offsetPairs]? = some (mapEnvBody (offsetPairF x) x.offsetPairs).compile) :
    ∀ p, (offsetPairsF x).ValidAt P p := fun p => mapEnv_valid hP p (fun _ _ => ho _)

/-- `v0 = (n, ((ox, oz), (ox', oz')))`. -/
def pairingPairsBody (x : Ix) : Tm [.prod .nat (.prod TEnvS TEnvS)] (.list (.prod .nat .nat)) :=
  .letE (.app (rangeF x.range) (.fst v0))
    (.app (appendF (.prod .nat .nat) x.append)
      (.pair (.app (offsetPairsF x) (.pair (.pair (.fst (.fst (.snd v1))) (.snd (.snd (.snd v1)))) v0))
        (.app (offsetPairsF x) (.pair (.pair (.snd (.fst (.snd v1))) (.fst (.snd (.snd v1)))) v0))))

def pairingPairsF (x : Ix) : FnSig (.prod .nat (.prod TEnvS TEnvS)) (.list (.prod .nat .nat)) :=
  FnSig.exact x.pairingPairs (pairingPairsBody x)
    (fun p => Plain.pairingPairs p.1 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)

@[simp] theorem pairingPairsF_den (x : Ix) (p : (Ty.prod .nat (.prod TEnvS TEnvS)).den) :
    (pairingPairsF x).den p = Plain.pairingPairs p.1 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2 := rfl

theorem pairingPairs_valid {x : Ix} (hL : LibOK P x) (ho : ∀ p, (offsetPairsF x).ValidAt P p)
    (hP : P[x.pairingPairs]? = some (pairingPairsBody x).compile) :
    ∀ p, (pairingPairsF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, pairingPairsBody, hL, ho])
    (fun p => by simp [tm_simp, pairingPairsBody, Plain.pairingPairs, Plain.offsetPairs])

/-- `v0 = (n, ((ox, oz), oe))`. -/
def supportPairsBody (x : Ix) : Tm [.prod .nat (.prod TEnvS .nat)] (.list (.prod .nat .nat)) :=
  .letE (.app (rangeF x.range) (.fst v0))
    (.app (appendF (.prod .nat .nat) x.append)
      (.pair (.app (offsetPairsF x) (.pair (.pair (.fst (.fst (.snd v1))) (.snd (.snd v1))) v0))
        (.app (offsetPairsF x) (.pair (.pair (.snd (.fst (.snd v1))) (.snd (.snd v1))) v0))))

def supportPairsF (x : Ix) : FnSig (.prod .nat (.prod TEnvS .nat)) (.list (.prod .nat .nat)) :=
  FnSig.exact x.supportPairs (supportPairsBody x)
    (fun p => Plain.supportPairs p.1 p.2.1.1 p.2.1.2 p.2.2)

@[simp] theorem supportPairsF_den (x : Ix) (p : (Ty.prod .nat (.prod TEnvS .nat)).den) :
    (supportPairsF x).den p = Plain.supportPairs p.1 p.2.1.1 p.2.1.2 p.2.2 := rfl

theorem supportPairs_valid {x : Ix} (hL : LibOK P x) (ho : ∀ p, (offsetPairsF x).ValidAt P p)
    (hP : P[x.supportPairs]? = some (supportPairsBody x).compile) :
    ∀ p, (supportPairsF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, supportPairsBody, hL, ho])
    (fun p => by simp [tm_simp, supportPairsBody, Plain.supportPairs, Plain.offsetPairs])

def supportClauseBody : Tm [.prod .nat .nat] TClause :=
  mkCl2 (.pair (.fst v0) .ff) (.pair (.snd v0) .tt)

def supportClauseF (x : Ix) : FnSig (.prod .nat .nat) TClause :=
  FnSig.exact x.supportClause supportClauseBody (fun p => [(p.1, false), (p.2, true)])

@[simp] theorem supportClauseF_den (x : Ix) (p : (Ty.prod .nat .nat).den) :
    (supportClauseF x).den p = [(p.1, false), (p.2, true)] := rfl

theorem supportClause_valid {x : Ix} (hP : P[x.supportClause]? = some supportClauseBody.compile) :
    ∀ p, (supportClauseF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, supportClauseBody])
    (fun p => by simp [tm_simp, supportClauseBody])

def supportClausesF (x : Ix) : FnSig (.list (.prod .nat .nat)) TForm :=
  mapF (supportClauseF x) x.supportClauses

@[simp] theorem supportClausesF_den (x : Ix) (ps : (Ty.list (.prod .nat .nat)).den) :
    (supportClausesF x).den ps = Plain.supportClauses ps := rfl

theorem supportClauses_valid {x : Ix} (hs : ∀ p, (supportClauseF x).ValidAt P p)
    (hP : P[x.supportClauses]? = some (mapBody (supportClauseF x) x.supportClauses).compile) :
    ∀ p, (supportClausesF x).ValidAt P p := fun p => map_valid hP p (fun _ _ => hs _)

/-- `v0 = (v, ps)`. -/
def pairingBlockBody (x : Ix) : Tm [.prod .nat (.list (.prod .nat .nat))] TBlock :=
  .letE (.bit .ff (.app (lengthF (.prod .nat .nat) x.length) (.snd v0)))
    (.pair (.app (succF x.succ) v0)
      (.app (appendF TClause x.append)
        (.pair (.app (compileAtF x) (.pair (.fst v1) (.app (productParityGatesF x) v1)))
          (.lcons (.lcons (.pair (.app (addF x.add) (.pair (.fst v1) v0)) .tt) .lnil) .lnil))))

def pairingBlockF (x : Ix) : FnSig (.prod .nat (.list (.prod .nat .nat))) TBlock :=
  FnSig.exact x.pairingBlock (pairingBlockBody x) (fun p => Plain.pairingBlock p.1 p.2)

@[simp] theorem pairingBlockF_den (x : Ix) (p : (Ty.prod .nat (.list (.prod .nat .nat))).den) :
    (pairingBlockF x).den p = Plain.pairingBlock p.1 p.2 := rfl

theorem pairingBlock_valid {x : Ix} (hL : LibOK P x) (hc : ∀ p, (compileAtF x).ValidAt P p)
    (hpp : ∀ p, (productParityGatesF x).ValidAt P p)
    (hP : P[x.pairingBlock]? = some (pairingBlockBody x).compile) :
    ∀ p, (pairingBlockF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, pairingBlockBody, hL, hc, hpp])
    (fun p => by simp [tm_simp, pairingBlockBody, Plain.pairingBlock])

/-! ## The Bad block -/

/-- Context of the Bad block body: `[4n, 3n, 2n, 5n, (n, rows)]`. -/
abbrev BadCtx : List Ty := [Ty.nat, Ty.nat, Ty.nat, Ty.nat, Ty.prod Ty.nat TRows]

def badNorm1 (x : Ix) : Tm BadCtx TBlock :=
  .app (normalizerF x) (.pair v3 (.pair (.pair (.fst v4) v2) (.snd v4)))
def badNorm2 (x : Ix) : Tm BadCtx TBlock :=
  .app (normalizerF x) (.pair v3 (.pair (.pair v1 v0) (.snd v4)))
def badSupport (x : Ix) : Tm BadCtx TBlock :=
  .pair .zero (.app (supportClausesF x)
    (.app (supportPairsF x) (.pair (.fst v4) (.pair (.pair v1 v0) .zero))))
def badPairing (x : Ix) : Tm BadCtx TBlock :=
  .app (pairingBlockF x) (.pair v3 (.app (pairingPairsF x)
    (.pair (.fst v4) (.pair (.pair v1 v0) (.pair (.fst v4) v2)))))
def badAnd (x : Ix) (A B : Tm BadCtx TBlock) : Tm BadCtx TBlock :=
  .app (blockAndF x) (.pair v3 (.pair A B))

/-- `v0 = (n, rows)`; let-bound `5n, 2n, 3n, 4n`. -/
def badBlockBody (x : Ix) : Tm [.prod .nat TRows] TBlock :=
  .letE (.app (mulF x.mul) (.pair (.lit (5 : ℕ)) (.fst v0)))
  (.letE (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v1)))
  (.letE (.app (mulF x.mul) (.pair (.lit (3 : ℕ)) (.fst v2)))
  (.letE (.app (mulF x.mul) (.pair (.lit (4 : ℕ)) (.fst v3)))
    (badAnd x (badNorm1 x) (badAnd x (badNorm2 x) (badAnd x (badSupport x) (badPairing x)))))))

def badBlockF (x : Ix) : FnSig (.prod .nat TRows) TBlock :=
  FnSig.exact x.badBlock (badBlockBody x) (fun p => Plain.badBlock p.1 p.2)

@[simp] theorem badBlockF_den (x : Ix) (p : (Ty.prod .nat TRows).den) :
    (badBlockF x).den p = Plain.badBlock p.1 p.2 := rfl

theorem badBlock_valid {x : Ix} (hL : LibOK P x) (ha : ∀ p, (blockAndF x).ValidAt P p)
    (hn : ∀ p, (normalizerF x).ValidAt P p) (hsc : ∀ p, (supportClausesF x).ValidAt P p)
    (hsp : ∀ p, (supportPairsF x).ValidAt P p) (hpb : ∀ p, (pairingBlockF x).ValidAt P p)
    (hpp : ∀ p, (pairingPairsF x).ValidAt P p)
    (hP : P[x.badBlock]? = some (badBlockBody x).compile) : ∀ p, (badBlockF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by
      simp [tm_simp, badBlockBody, badAnd, badNorm1, badNorm2, badSupport, badPairing, hL, ha, hn,
        hsc, hsp, hpb, hpp])
    (fun p => by
      simp [tm_simp, badBlockBody, badAnd, badNorm1, badNorm2, badSupport, badPairing, Plain.badBlock])

end QecReliability.Trans.Query
