import Trans.Query.FLBad

/-!
# Trans.Query.FLGood: sparse reconstruction, cleaning block, the Good block

| FL | meaning |
|---|---|
| `setF` | `(xs, i, a) ↦ xs.set i a` |
| `recZeroF`, `recAddIncF`, `recAddRowF`, `synthesizeF` | `Plain.recZero/recAddInc/recAddRow/synthesize` |
| `condEqF`, `condEqsF`, `cleaningF` | `Plain.condEq/condEqs/cleaning` |
| `filterNonemptyCF` | `Plain.trimRows` |
| `goodBlockF` | `Plain.goodBlock` |
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Query
open QecReliability.FL QecReliability.FL.Lib Tm NatSize

variable {P : Program}

/-! ## List update -/

def setCost (x : Ix) : List ℕ → ℕ → ℕ
  | [], _ => 10
  | _ :: ys, i => if i = 0 then 20 else (predF x.pred).cost i + setCost x ys (i - 1) + 40

def setDepth (x : Ix) : List ℕ → ℕ → ℕ
  | [], _ => 1
  | _ :: ys, i => if i = 0 then 1 else (predF x.pred).depth i + setDepth x ys (i - 1) + 5

def setMsize (x : Ix) : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | y :: ys, i, a => (Ty.enc (.list .nat) ((y :: ys).set i a)).size + (predF x.pred).msize i +
      (Ty.enc (.prod (.list .nat) (.prod .nat .nat)) (ys, i - 1, a)).size + setMsize x ys (i - 1) a + 10

@[simps] def setF (x : Ix) : FnSig (.prod (.list .nat) (.prod .nat .nat)) (.list .nat) where
  idx := x.set
  den p := p.1.set p.2.1 p.2.2
  cost p := setCost x p.1 p.2.1
  depth p := setDepth x p.1 p.2.1
  msize p := setMsize x p.1 p.2.1 p.2.2

def setBody (x : Ix) : Tm [.prod (.list .nat) (.prod .nat .nat)] (.list .nat) :=
  .lcase (.fst v0) .lnil
    (.ncase (.fst (.snd v2)) (.lcons (.snd (.snd v2)) v1)
      (.lcons v2 (.app (setF x) (.pair v3 (.pair (.app (predF x.pred) (.fst (.snd v4)))
        (.snd (.snd v4)))))))

theorem set_valid {x : Ix} (hL : LibOK P x) (hP : P[x.set]? = some (setBody x).compile) :
    ∀ p, (setF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.1.length) ?_
  rintro ⟨(_ | ⟨y, ys⟩), (i : ℕ), (a : ℕ)⟩ ih
  · constructor <;> tm_auto [setBody, setCost, setDepth, setMsize]
  · by_cases hi : i = 0
    · subst hi
      constructor <;> tm_auto [setBody, setCost, setDepth, setMsize]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hih := ih (ys, j, a) (by simp)
      constructor <;> tm_auto [setBody, setCost, setDepth, setMsize, hih, hL.pred]

/-! ## Reconstruction steps -/

/-- `v0 = (n, v)`. -/
def recZeroBody (x : Ix) : Tm [.prod .nat .nat] TRec :=
  .letE (.app (replicateF .nat x.replicate) v0)
    (.pair (.lit ([Plain.constGate false] : List Plain.GateP)) (.pair v0 v0))

def recZeroF (x : Ix) : FnSig (.prod .nat .nat) TRec :=
  FnSig.exact x.recZero (recZeroBody x) (fun p => Plain.recZero p.1 p.2)

@[simp] theorem recZeroF_den (x : Ix) (p : (Ty.prod .nat .nat).den) :
    (recZeroF x).den p = Plain.recZero p.1 p.2 := rfl

theorem recZero_valid {x : Ix} (hL : LibOK P x) (hP : P[x.recZero]? = some (recZeroBody x).compile) :
    ∀ p, (recZeroF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, recZeroBody, hL])
    (fun p => by simp [tm_simp, recZeroBody, Plain.recZero])

/-- Context `[w, (v, (R, (c, coeff)))]` with `w = v + |R.1|`. -/
abbrev IncCtx : List Ty := [Ty.nat, Ty.prod Ty.nat (Ty.prod TRec (Ty.prod TCoord Ty.nat))]

def incOld (x : Ix) : Tm IncCtx .nat :=
  .ite (.fst (.fst (.snd (.snd v1))))
    (.app (getDF .nat x.getD) (.pair (.snd (.snd (.fst (.snd v1)))) (.pair (.snd (.fst (.snd (.snd v1)))) .zero)))
    (.app (getDF .nat x.getD) (.pair (.fst (.snd (.fst (.snd v1)))) (.pair (.snd (.fst (.snd (.snd v1)))) .zero)))

def incOuts (x : Ix) : Tm IncCtx (.prod (.list .nat) (.list .nat)) :=
  .ite (.fst (.fst (.snd (.snd v1))))
    (.pair (.fst (.snd (.fst (.snd v1))))
      (.app (setF x) (.pair (.snd (.snd (.fst (.snd v1)))) (.pair (.snd (.fst (.snd (.snd v1)))) v0))))
    (.pair (.app (setF x) (.pair (.fst (.snd (.fst (.snd v1)))) (.pair (.snd (.fst (.snd (.snd v1)))) v0)))
      (.snd (.snd (.fst (.snd v1)))))

/-- `v0 = (v, (R, (c, coeff)))`. -/
def recAddIncBody (x : Ix) : Tm [.prod .nat (.prod TRec (.prod TCoord .nat))] TRec :=
  .letE (.app (addF x.add) (.pair (.fst v0) (.app (lengthF TGate x.length) (.fst (.fst (.snd v0))))))
    (.pair (.app (appendF TGate x.append) (.pair (.fst (.fst (.snd v1)))
        (.lcons (.pair .ff (.pair .tt (.pair (incOld x) (.snd (.snd (.snd v1)))))) .lnil)))
      (incOuts x))

def recAddIncF (x : Ix) : FnSig (.prod .nat (.prod TRec (.prod TCoord .nat))) TRec :=
  FnSig.exact x.recAddInc (recAddIncBody x) (fun p => Plain.recAddInc p.1 p.2.1 p.2.2.1 p.2.2.2)

@[simp] theorem recAddIncF_den (x : Ix) (p : (Ty.prod .nat (.prod TRec (.prod TCoord .nat))).den) :
    (recAddIncF x).den p = Plain.recAddInc p.1 p.2.1 p.2.2.1 p.2.2.2 := rfl

theorem recAddInc_valid {x : Ix} (hL : LibOK P x) (hs : ∀ p, (setF x).ValidAt P p)
    (hP : P[x.recAddInc]? = some (recAddIncBody x).compile) : ∀ p, (recAddIncF x).ValidAt P p :=
  FnSig.exact_valid hP
    (fun p => by
      obtain ⟨v, R, ⟨b, i⟩, c⟩ := p
      cases b <;> simp [tm_simp, recAddIncBody, incOld, incOuts, hL, hs])
    (fun p => by
      obtain ⟨v, R, ⟨b, i⟩, c⟩ := p
      cases b <;> simp [tm_simp, recAddIncBody, incOld, incOuts, Plain.recAddInc])

def recAddRowCost (x : Ix) (v : ℕ) (R : Plain.RecP) (coeff : ℕ) : List Plain.Coord → ℕ
  | [] => 20
  | c :: cs => (recAddIncF x).cost (v, Plain.recAddRow v R coeff cs, c, coeff) +
      recAddRowCost x v R coeff cs + 30

def recAddRowDepth (x : Ix) (v : ℕ) (R : Plain.RecP) (coeff : ℕ) : List Plain.Coord → ℕ
  | [] => 1
  | c :: cs => (recAddIncF x).depth (v, Plain.recAddRow v R coeff cs, c, coeff) +
      recAddRowDepth x v R coeff cs + 5

def recAddRowMsize (x : Ix) (v : ℕ) (R : Plain.RecP) (coeff : ℕ) : List Plain.Coord → ℕ
  | [] => 0
  | c :: cs => (recAddIncF x).msize (v, Plain.recAddRow v R coeff cs, c, coeff) +
      (Ty.enc (.prod .nat (.prod TRec (.prod TCoord .nat))) (v, Plain.recAddRow v R coeff cs, c, coeff)).size +
      (Ty.enc (.prod .nat (.prod .nat (.prod TRec TRow))) (v, coeff, R, cs)).size +
      recAddRowMsize x v R coeff cs + 10

/-- `(v, (coeff, (R, cs))) ↦ recAddRow v R coeff cs`. -/
@[simps] def recAddRowF (x : Ix) : FnSig (.prod .nat (.prod .nat (.prod TRec TRow))) TRec where
  idx := x.recAddRow
  den p := Plain.recAddRow p.1 p.2.2.1 p.2.1 p.2.2.2
  cost p := recAddRowCost x p.1 p.2.2.1 p.2.1 p.2.2.2
  depth p := recAddRowDepth x p.1 p.2.2.1 p.2.1 p.2.2.2
  msize p := recAddRowMsize x p.1 p.2.2.1 p.2.1 p.2.2.2

def recAddRowBody (x : Ix) : Tm [.prod .nat (.prod .nat (.prod TRec TRow))] TRec :=
  .lcase (.snd (.snd (.snd v0))) (.fst (.snd (.snd v0)))
    (.app (recAddIncF x) (.pair (.fst v2)
      (.pair (.app (recAddRowF x) (.pair (.fst v2) (.pair (.fst (.snd v2)) (.pair (.fst (.snd (.snd v2))) v1))))
        (.pair v0 (.fst (.snd v2))))))

theorem recAddRow_valid {x : Ix} (hi : ∀ p, (recAddIncF x).ValidAt P p)
    (hP : P[x.recAddRow]? = some (recAddRowBody x).compile) : ∀ p, (recAddRowF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.2.2.length) ?_
  rintro ⟨(v : ℕ), (coeff : ℕ), R, (_ | ⟨c, cs⟩)⟩ ih
  · constructor <;> tm_auto [recAddRowBody, recAddRowCost, recAddRowDepth, recAddRowMsize,
      Plain.recAddRow]
  · have hih := ih (v, coeff, R, cs) (by simp)
    constructor
    · tm_auto [recAddRowBody, recAddRowCost, recAddRowDepth, recAddRowMsize, Plain.recAddRow, hih, hi]
    · tm_auto [recAddRowBody, recAddRowCost, recAddRowDepth, recAddRowMsize, Plain.recAddRow, hih, hi]
    · tm_auto [recAddRowBody, recAddRowCost, recAddRowDepth, recAddRowMsize, Plain.recAddRow, hih, hi]
    · tm_auto [recAddRowBody, recAddRowCost, recAddRowDepth, recAddRowMsize, Plain.recAddRow, hih, hi]
    · tm_auto [recAddRowBody, recAddRowCost, recAddRowDepth, recAddRowMsize, Plain.recAddRow, hih, hi]

def synthCost (x : Ix) (n v : ℕ) : ℕ → List (List Plain.Coord) → ℕ
  | _, [] => (recZeroF x).cost (n, v) + 30
  | base, row :: rows => (recAddRowF x).cost (v, base, Plain.synthesize n v (base + 1) rows, row) +
      (succF x.succ).cost base + synthCost x n v (base + 1) rows + 40

def synthDepth (x : Ix) (n v : ℕ) : ℕ → List (List Plain.Coord) → ℕ
  | _, [] => (recZeroF x).depth (n, v) + 2
  | base, row :: rows => (recAddRowF x).depth (v, base, Plain.synthesize n v (base + 1) rows, row) +
      (succF x.succ).depth base + synthDepth x n v (base + 1) rows + 5

def synthMsize (x : Ix) (n v : ℕ) : ℕ → List (List Plain.Coord) → ℕ
  | base, [] => (recZeroF x).msize (n, v) + (Ty.enc (.prod .nat .nat) (n, v)).size + 4 * base.size + 10
  | base, row :: rows => (recAddRowF x).msize (v, base, Plain.synthesize n v (base + 1) rows, row) +
      (succF x.succ).msize base +
      (Ty.enc (.prod .nat (.prod .nat (.prod TRec TRow))) (v, base, Plain.synthesize n v (base + 1) rows, row)).size +
      (Ty.enc (.prod .nat (.prod .nat (.prod .nat TRows))) (n, v, base + 1, rows)).size +
      synthMsize x n v (base + 1) rows + 10

/-- `(n, (v, (base, rows))) ↦ synthesize n v base rows`. -/
@[simps] def synthesizeF (x : Ix) : FnSig (.prod .nat (.prod .nat (.prod .nat TRows))) TRec where
  idx := x.synthesize
  den p := Plain.synthesize p.1 p.2.1 p.2.2.1 p.2.2.2
  cost p := synthCost x p.1 p.2.1 p.2.2.1 p.2.2.2
  depth p := synthDepth x p.1 p.2.1 p.2.2.1 p.2.2.2
  msize p := synthMsize x p.1 p.2.1 p.2.2.1 p.2.2.2

def synthesizeBody (x : Ix) : Tm [.prod .nat (.prod .nat (.prod .nat TRows))] TRec :=
  .lcase (.snd (.snd (.snd v0))) (.app (recZeroF x) (.pair (.fst v0) (.fst (.snd v0))))
    (.app (recAddRowF x) (.pair (.fst (.snd v2)) (.pair (.fst (.snd (.snd v2)))
      (.pair (.app (synthesizeF x) (.pair (.fst v2) (.pair (.fst (.snd v2))
          (.pair (.app (succF x.succ) (.fst (.snd (.snd v2)))) v1))))
        v0))))

theorem synthesize_valid {x : Ix} (hL : LibOK P x) (hz : ∀ p, (recZeroF x).ValidAt P p)
    (hr : ∀ p, (recAddRowF x).ValidAt P p)
    (hP : P[x.synthesize]? = some (synthesizeBody x).compile) : ∀ p, (synthesizeF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.2.2.length) ?_
  rintro ⟨(n : ℕ), (v : ℕ), (base : ℕ), (_ | ⟨row, rows⟩)⟩ ih
  · constructor <;> tm_auto [synthesizeBody, synthCost, synthDepth, synthMsize, Plain.synthesize, hz]
  · have hih := ih (n, v, base + 1, rows) (by simp)
    constructor <;> tm_auto [synthesizeBody, synthCost, synthDepth, synthMsize, Plain.synthesize,
      hih, hr, hL.succ]

/-! ## Cleaning block -/

/-- `v0 = (e, (x, y))`. -/
def condEqBody : Tm [.prod .nat (.prod .nat .nat)] TForm :=
  .lcons (mkCl3 (.pair (.fst v0) .ff) (.pair (.fst (.snd v0)) .ff) (.pair (.snd (.snd v0)) .tt))
    (.lcons (mkCl3 (.pair (.fst v0) .ff) (.pair (.fst (.snd v0)) .tt) (.pair (.snd (.snd v0)) .ff)) .lnil)

def condEqF (x : Ix) : FnSig (.prod .nat (.prod .nat .nat)) TForm :=
  FnSig.exact x.condEq condEqBody (fun p => Plain.condEq p.1 p.2.1 p.2.2)

@[simp] theorem condEqF_den (x : Ix) (p : (Ty.prod .nat (.prod .nat .nat)).den) :
    (condEqF x).den p = Plain.condEq p.1 p.2.1 p.2.2 := rfl

theorem condEq_valid {x : Ix} (hP : P[x.condEq]? = some condEqBody.compile) :
    ∀ p, (condEqF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, condEqBody])
    (fun p => by simp [tm_simp, condEqBody, Plain.condEq])

def condEqsCost (x : Ix) (oz : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 10
  | i, s :: ss => (addF x.add).cost (oz, i) + (condEqF x).cost (i, s, oz + i) + 15 * 2 +
      (succF x.succ).cost i + condEqsCost x oz (i + 1) ss + 60

def condEqsDepth (x : Ix) (oz : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 1
  | i, s :: ss => (addF x.add).depth (oz, i) + (condEqF x).depth (i, s, oz + i) +
      (succF x.succ).depth i + condEqsDepth x oz (i + 1) ss + 10

def condEqsMsize (x : Ix) (oz : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | i, s :: ss => (addF x.add).msize (oz, i) + (condEqF x).msize (i, s, oz + i) +
      (succF x.succ).msize i + (Ty.enc (.prod .nat (.prod .nat .nat)) (i, s, oz + i)).size +
      (Ty.enc (.prod .nat (.prod .nat (.list .nat))) (oz, i + 1, ss)).size +
      2 * (Ty.enc TForm (Plain.condEqs oz i (s :: ss))).size + condEqsMsize x oz (i + 1) ss + 10

/-- `(oz, (i, ss)) ↦ condEqs oz i ss`. -/
@[simps] def condEqsF (x : Ix) : FnSig (.prod .nat (.prod .nat (.list .nat))) TForm where
  idx := x.condEqs
  den p := Plain.condEqs p.1 p.2.1 p.2.2
  cost p := condEqsCost x p.1 p.2.1 p.2.2
  depth p := condEqsDepth x p.1 p.2.1 p.2.2
  msize p := condEqsMsize x p.1 p.2.1 p.2.2

def condEqsBody (x : Ix) : Tm [.prod .nat (.prod .nat (.list .nat))] TForm :=
  .lcase (.snd (.snd v0)) .lnil
    (.app (appendF TClause x.append)
      (.pair (.app (condEqF x) (.pair (.fst (.snd v2)) (.pair v0
          (.app (addF x.add) (.pair (.fst v2) (.fst (.snd v2)))))))
        (.app (condEqsF x) (.pair (.fst v2) (.pair (.app (succF x.succ) (.fst (.snd v2))) v1)))))

theorem condEqs_valid {x : Ix} (hL : LibOK P x) (hc : ∀ p, (condEqF x).ValidAt P p)
    (hP : P[x.condEqs]? = some (condEqsBody x).compile) : ∀ p, (condEqsF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.2.length) ?_
  rintro ⟨(oz : ℕ), (i : ℕ), (_ | ⟨s, ss⟩)⟩ ih
  · constructor <;> tm_auto [condEqsBody, condEqsCost, condEqsDepth, condEqsMsize, Plain.condEqs]
  · have hih := ih (oz, i + 1, ss) (by simp)
    have e1 := Ty.sz_list_append TClause (Plain.condEq i s (oz + i)) (Plain.condEqs oz (i + 1) ss)
    have e2 : (Plain.condEq i s (oz + i)).length = 2 := rfl
    constructor <;> tm_auto [condEqsBody, condEqsCost, condEqsDepth, condEqsMsize, Plain.condEqs,
      hih, hc, hL.append, hL.add, hL.succ]

/-- `v0 = (n, (v, R))`. -/
def cleaningBody (x : Ix) : Tm [.prod .nat (.prod .nat TRec)] TBlock :=
  .pair (.app (lengthF TGate x.length) (.fst (.snd (.snd v0))))
    (.app (appendF TClause x.append)
      (.pair (.app (compileAtF x) (.pair (.fst (.snd v0)) (.fst (.snd (.snd v0)))))
        (.app (appendF TClause x.append)
          (.pair (.app (condEqsF x) (.pair (.fst v0) (.pair .zero (.fst (.snd (.snd (.snd v0)))))))
            (.app (condEqsF x) (.pair (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v0)))
              (.pair .zero (.snd (.snd (.snd (.snd v0)))))))))))

def cleaningF (x : Ix) : FnSig (.prod .nat (.prod .nat TRec)) TBlock :=
  FnSig.exact x.cleaning (cleaningBody x) (fun p => Plain.cleaning p.1 p.2.1 p.2.2)

@[simp] theorem cleaningF_den (x : Ix) (p : (Ty.prod .nat (.prod .nat TRec)).den) :
    (cleaningF x).den p = Plain.cleaning p.1 p.2.1 p.2.2 := rfl

theorem cleaning_valid {x : Ix} (hL : LibOK P x) (hc : ∀ p, (compileAtF x).ValidAt P p)
    (he : ∀ p, (condEqsF x).ValidAt P p)
    (hP : P[x.cleaning]? = some (cleaningBody x).compile) : ∀ p, (cleaningF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, cleaningBody, hL, hc, he])
    (fun p => by simp [tm_simp, cleaningBody, Plain.cleaning])

/-! ## The Good block -/

def filterNonemptyCF (x : Ix) : FnSig TRows TRows := filterF (nonemptyF TCoord x) x.filterNonemptyC

@[simp] theorem filterNonemptyCF_den (x : Ix) (rows : (TRows).den) :
    (filterNonemptyCF x).den rows = Plain.trimRows rows := rfl

theorem filterNonemptyC_valid {x : Ix} (hn : ∀ p, (nonemptyF TCoord x).ValidAt P p)
    (hP : P[x.filterNonemptyC]? = some (filterBody (nonemptyF TCoord x) x.filterNonemptyC).compile) :
    ∀ p, (filterNonemptyCF x).ValidAt P p := fun p => filter_valid hP p (fun _ _ => hn _)

/-- Context `[v, 3n, T, (n, rows)]` with `T = trimRows rows`, `v = 3n + |T|`. -/
abbrev GoodCtx : List Ty := [Ty.nat, Ty.nat, TRows, Ty.prod Ty.nat TRows]

def goodNorm (x : Ix) : Tm GoodCtx TBlock :=
  .app (normalizerF x) (.pair v0 (.pair (.pair (.fst v3)
    (.app (mulF x.mul) (.pair (.lit (2 : ℕ)) (.fst v3)))) (.snd v3)))

def goodClean (x : Ix) : Tm GoodCtx TBlock :=
  .app (cleaningF x) (.pair (.fst v3) (.pair v0
    (.app (synthesizeF x) (.pair (.fst v3) (.pair v0 (.pair v1 v2))))))

/-- `v0 = (n, rows)`. -/
def goodBlockBody (x : Ix) : Tm [.prod .nat TRows] TBlock :=
  .letE (.app (filterNonemptyCF x) (.snd v0))
  (.letE (.app (mulF x.mul) (.pair (.lit (3 : ℕ)) (.fst v1)))
  (.letE (.app (addF x.add) (.pair v0 (.app (lengthF TRow x.length) v1)))
    (.app (blockAndF x) (.pair v0 (.pair (goodNorm x) (goodClean x))))))

def goodBlockF (x : Ix) : FnSig (.prod .nat TRows) TBlock :=
  FnSig.exact x.goodBlock (goodBlockBody x) (fun p => Plain.goodBlock p.1 p.2)

@[simp] theorem goodBlockF_den (x : Ix) (p : (Ty.prod .nat TRows).den) :
    (goodBlockF x).den p = Plain.goodBlock p.1 p.2 := rfl

theorem goodBlock_valid {x : Ix} (hL : LibOK P x) (ha : ∀ p, (blockAndF x).ValidAt P p)
    (hn : ∀ p, (normalizerF x).ValidAt P p) (hc : ∀ p, (cleaningF x).ValidAt P p)
    (hs : ∀ p, (synthesizeF x).ValidAt P p) (hf : ∀ p, (filterNonemptyCF x).ValidAt P p)
    (hP : P[x.goodBlock]? = some (goodBlockBody x).compile) : ∀ p, (goodBlockF x).ValidAt P p :=
  FnSig.exact_valid hP
    (fun p => by simp [tm_simp, goodBlockBody, goodNorm, goodClean, hL, ha, hn, hc, hs, hf])
    (fun p => by simp [tm_simp, goodBlockBody, goodNorm, goodClean, Plain.goodBlock])

end QecReliability.Trans.Query
