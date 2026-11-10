import Trans.Query.FLGood

/-!
# Trans.Query.FLPop: ripple adder, adder tree, population counter, weight block

| FL | meaning |
|---|---|
| `adderGatesF`, `rippleF` | `Plain.adderGates/ripple` |
| `countTreeF` | `Plain.countTree` |
| `pow2SizeF`, `paddedWiresF`, `populationF` | `Plain.pow2Size/paddedWires/population` |
| `weightBlockF` | `Plain.weightBlock` |
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Query
open QecReliability.FL QecReliability.FL.Lib Tm NatSize

variable {P : Program}

/-! ## Full adder and ripple adder -/

/-- `v0 = (v, (a, (b, c)))`. -/
def adderGatesBody (x : Ix) : Tm [.prod .nat (.prod .nat (.prod .nat .nat))] TGates :=
  .lcons (.pair .ff (.pair .tt (.pair (.fst (.snd v0)) (.fst (.snd (.snd v0))))))
  (.lcons (.pair .ff (.pair .tt (.pair (.fst v0) (.snd (.snd (.snd v0))))))
  (.lcons (.pair .ff (.pair .ff (.pair (.fst (.snd v0)) (.fst (.snd (.snd v0))))))
  (.lcons (.pair .ff (.pair .ff (.pair (.fst v0) (.snd (.snd (.snd v0))))))
  (.lcons (.pair .ff (.pair .tt (.pair (.app (addF x.add) (.pair (.fst v0) (.lit (2 : ℕ))))
      (.app (addF x.add) (.pair (.fst v0) (.lit (3 : ℕ))))))) .lnil))))

def adderGatesF (x : Ix) : FnSig (.prod .nat (.prod .nat (.prod .nat .nat))) TGates :=
  FnSig.exact x.adderGates (adderGatesBody x) (fun p => Plain.adderGates p.1 p.2.1 p.2.2.1 p.2.2.2)

@[simp] theorem adderGatesF_den (x : Ix) (p : (Ty.prod .nat (.prod .nat (.prod .nat .nat))).den) :
    (adderGatesF x).den p = Plain.adderGates p.1 p.2.1 p.2.2.1 p.2.2.2 := rfl

theorem adderGates_valid {x : Ix} (hL : LibOK P x) (hP : P[x.adderGates]? = some (adderGatesBody x).compile) :
    ∀ p, (adderGatesF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, adderGatesBody, hL])
    (fun p => by simp [tm_simp, adderGatesBody, Plain.adderGates])

def rippleCost (x : Ix) : ℕ → List ℕ → List ℕ → ℕ → ℕ
  | v, a :: as, b :: bs, c => (addF x.add).cost (v, 5) + (addF x.add).cost (v, 4) +
      (adderGatesF x).cost (v, a, b, c) + (succF x.succ).cost v + rippleCost x (v + 5) as bs (v + 4) + 200
  | _, _, _, _ => 30

def rippleDepth (x : Ix) : ℕ → List ℕ → List ℕ → ℕ → ℕ
  | v, a :: as, b :: bs, c => (addF x.add).depth (v, 5) + (addF x.add).depth (v, 4) +
      (adderGatesF x).depth (v, a, b, c) + (succF x.succ).depth v + rippleDepth x (v + 5) as bs (v + 4) + 20
  | _, _, _, _ => 2

def rippleMsize (x : Ix) : ℕ → List ℕ → List ℕ → ℕ → ℕ
  | v, a :: as, b :: bs, c => (addF x.add).msize (v, 5) + (addF x.add).msize (v, 4) +
      (adderGatesF x).msize (v, a, b, c) + (succF x.succ).msize v +
      (Ty.enc (.prod .nat (.prod .nat (.prod .nat .nat))) (v, a, b, c)).size +
      (Ty.enc (.prod .nat (.prod (.list .nat) (.prod (.list .nat) .nat))) (v + 5, as, bs, v + 4)).size +
      3 * (Ty.enc TProg (Plain.ripple v (a :: as) (b :: bs) c)).size +
      rippleMsize x (v + 5) as bs (v + 4) + 20
  | _, _, _, c => 4 * c.size + 20

/-- `(v, (xs, (ys, c))) ↦ ripple v xs ys c`. -/
@[simps] def rippleF (x : Ix) : FnSig (.prod .nat (.prod (.list .nat) (.prod (.list .nat) .nat))) TProg where
  idx := x.ripple
  den p := Plain.ripple p.1 p.2.1 p.2.2.1 p.2.2.2
  cost p := rippleCost x p.1 p.2.1 p.2.2.1 p.2.2.2
  depth p := rippleDepth x p.1 p.2.1 p.2.2.1 p.2.2.2
  msize p := rippleMsize x p.1 p.2.1 p.2.2.1 p.2.2.2

def rippleBody (x : Ix) : Tm [.prod .nat (.prod (.list .nat) (.prod (.list .nat) .nat))] TProg :=
  .lcase (.fst (.snd v0)) (.pair .lnil (.lcons (.snd (.snd (.snd v0))) .lnil))
    (.lcase (.fst (.snd (.snd v2))) (.pair .lnil (.lcons (.snd (.snd (.snd v2))) .lnil))
      (.letE (.app (rippleF x) (.pair (.app (addF x.add) (.pair (.fst v4) (.lit (5 : ℕ))))
          (.pair v3 (.pair v1 (.app (addF x.add) (.pair (.fst v4) (.lit (4 : ℕ))))))))
        (.pair (.app (appendF TGate x.append) (.pair (.app (adderGatesF x)
            (.pair (.fst v5) (.pair v3 (.pair v1 (.snd (.snd (.snd v5))))))) (.fst v0)))
          (.lcons (.app (succF x.succ) (.fst v5)) (.snd v0)))))

theorem adderGates_length (v a b c : ℕ) : (Plain.adderGates v a b c).length = 5 := rfl

theorem size_four : Nat.size 4 = 3 := by
  have := size_half (n := 4) (by omega); rw [show 4 / 2 = 2 by rfl, size_two] at this; omega

theorem size_five : Nat.size 5 = 3 := by
  have := size_half (n := 5) (by omega); rw [show 5 / 2 = 2 by rfl, size_two] at this; omega

theorem ripple_cons (v a b c : ℕ) (as bs : List ℕ) :
    Plain.ripple v (a :: as) (b :: bs) c =
      (Plain.adderGates v a b c ++ (Plain.ripple (v + 5) as bs (v + 4)).1,
        (v + 1) :: (Plain.ripple (v + 5) as bs (v + 4)).2) := rfl
theorem ripple_nil (v : ℕ) (bs : List ℕ) (c : ℕ) : Plain.ripple v [] bs c = ([], [c]) := rfl
theorem ripple_cons_nil (v a : ℕ) (as : List ℕ) (c : ℕ) : Plain.ripple v (a :: as) [] c = ([], [c]) := rfl

theorem ripple_valid {x : Ix} (hL : LibOK P x) (ha : ∀ p, (adderGatesF x).ValidAt P p)
    (hP : P[x.ripple]? = some (rippleBody x).compile) : ∀ p, (rippleF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.1.length) ?_
  rintro ⟨(v : ℕ), (_ | ⟨a, as⟩), (_ | ⟨b, bs⟩), (c : ℕ)⟩ ih
  all_goals have h0 : (Ty.enc TGates ([] : List Plain.GateP)).size = 1 := rfl
  · constructor <;> tm_auto [rippleBody, rippleCost, rippleDepth, rippleMsize, ripple_nil]
  · constructor <;> tm_auto [rippleBody, rippleCost, rippleDepth, rippleMsize, ripple_nil]
  · constructor <;> tm_auto [rippleBody, rippleCost, rippleDepth, rippleMsize, ripple_cons_nil]
  · have hih := ih (v + 5, as, bs, v + 4) (by simp)
    have e1 := Ty.sz_list_append TGate (Plain.adderGates v a b c) (Plain.ripple (v + 5) as bs (v + 4)).1
    have e2 := adderGates_length v a b c
    have e3 := size_four
    have e4 := size_five
    constructor
    · simp [tm_simp, rippleBody, hih, ha, hL.add, hL.append, hL.succ]
    · simp only [tm_simp, rippleBody, ripple_cons, rippleF_den, adderGatesF_den, appendF_den,
        succF_den, addF_den]
    · tm_auto [rippleBody, rippleCost, ripple_cons, hih, ha, hL.add, hL.append, hL.succ]
    · tm_auto [rippleBody, rippleDepth, ripple_cons, hih, ha, hL.add, hL.append, hL.succ]
    · tm_lean [rippleBody, rippleMsize, ripple_cons, rippleF_msize, rippleF_den, addF_msize,
        addF_den, succF_msize, succF_den, appendF_msize, appendF_den, adderGatesF_den]

/-! ## Adder tree -/

/-- Argument of the adder tree: `(v, (k, (xs, z)))`. -/
scoped notation "TTreeArg" => Ty.prod Ty.nat (Ty.prod Ty.nat (Ty.prod (Ty.list Ty.nat) Ty.nat))

/-- The combination step of `Plain.countTree v k` (`k ≥ 1`) after the two recursive calls. -/
def treeCombine (v k : ℕ) (L R : Plain.ProgP) (z : ℕ) : Plain.ProgP :=
  ((L.1 ++ Plain.gatesS (v, L.1.length) R.1) ++
      (Plain.ripple (v + (L.1 ++ Plain.gatesS (v, L.1.length) R.1).length)
        ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).take k)
        ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).drop k) z).1,
    (Plain.ripple (v + (L.1 ++ Plain.gatesS (v, L.1.length) R.1).length)
        ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).take k)
        ((L.2 ++ Plain.wiresS (v, L.1.length) R.2).drop k) z).2)

theorem countTree_succ (v k : ℕ) (xs : List ℕ) (z : ℕ) :
    Plain.countTree v (k + 1) xs z = treeCombine v (k + 1)
      (Plain.countTree v k (xs.take (xs.length / 2)) z)
      (Plain.countTree v k (xs.drop (xs.length / 2)) z) z := rfl

/-- The two recursive arguments. -/
def treeSplit (p : (TTreeArg).den) : (Ty.prod TTreeArg TTreeArg).den :=
  ((p.1, p.2.1 - 1, p.2.2.1.take (p.2.2.1.length / 2), p.2.2.2),
    (p.1, p.2.1 - 1, p.2.2.1.drop (p.2.2.1.length / 2), p.2.2.2))

/-- Context `[km, h, (v, (k, (xs, z)))]`. -/
def treeSplitBody (x : Ix) : Tm [TTreeArg] (.prod TTreeArg TTreeArg) :=
  .letE (.app (div2F x.div2) (.app (lengthF .nat x.length) (.fst (.snd (.snd v0)))))
  (.letE (.app (predF x.pred) (.fst (.snd v1)))
    (.pair (.pair (.fst v2) (.pair v0 (.pair (.app (takeF .nat x.take) (.pair v1 (.fst (.snd (.snd v2)))))
        (.snd (.snd (.snd v2))))))
      (.pair (.fst v2) (.pair v0 (.pair (.app (dropF .nat x.drop) (.pair v1 (.fst (.snd (.snd v2)))))
        (.snd (.snd (.snd v2))))))))

def treeSplitF (x : Ix) : FnSig TTreeArg (.prod TTreeArg TTreeArg) :=
  FnSig.exact x.treeSplit (treeSplitBody x) treeSplit

@[simp] theorem treeSplitF_den (x : Ix) (p : (TTreeArg).den) : (treeSplitF x).den p = treeSplit p := rfl

theorem treeSplit_valid {x : Ix} (hL : LibOK P x) (hP : P[x.treeSplit]? = some (treeSplitBody x).compile) :
    ∀ p, (treeSplitF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, treeSplitBody, hL])
    (fun p => by simp [tm_simp, treeSplitBody, treeSplit])

/-- Context `[os, gs, lg, ((v, (k, (xs, z))), (L, R))]`. -/
abbrev CombCtx : List Ty := [TWires, TGates, Ty.nat, Ty.prod TTreeArg (Ty.prod TProg TProg)]

def combFinish (x : Ix) : Tm CombCtx TProg :=
  .letE (.app (rippleF x) (.pair (.app (addF x.add) (.pair (.fst (.fst v3)) (.app (lengthF TGate x.length) v1)))
      (.pair (.app (takeF .nat x.take) (.pair (.fst (.snd (.fst v3))) v0))
        (.pair (.app (dropF .nat x.drop) (.pair (.fst (.snd (.fst v3))) v0))
          (.snd (.snd (.snd (.fst v3))))))))
    (.pair (.app (appendF TGate x.append) (.pair v2 (.fst v0))) (.snd v0))

/-- `v0 = ((v, (k, (xs, z))), (L, R))`. -/
def treeCombineBody (x : Ix) : Tm [.prod TTreeArg (.prod TProg TProg)] TProg :=
  .letE (.app (lengthF TGate x.length) (.fst (.fst (.snd v0))))
  (.letE (.app (appendF TGate x.append) (.pair (.fst (.fst (.snd v1)))
      (.app (gatesSF x) (.pair (.pair (.fst (.fst v1)) v0) (.fst (.snd (.snd v1)))))))
  (.letE (.app (appendF .nat x.append) (.pair (.snd (.fst (.snd v2)))
      (.app (wiresSF x) (.pair (.pair (.fst (.fst v2)) v1) (.snd (.snd (.snd v2)))))))
    (combFinish x)))

def treeCombineF (x : Ix) : FnSig (.prod TTreeArg (.prod TProg TProg)) TProg :=
  FnSig.exact x.treeCombine (treeCombineBody x)
    (fun p => treeCombine p.1.1 p.1.2.1 p.2.1 p.2.2 p.1.2.2.2)

@[simp] theorem treeCombineF_den (x : Ix) (p : (Ty.prod TTreeArg (.prod TProg TProg)).den) :
    (treeCombineF x).den p = treeCombine p.1.1 p.1.2.1 p.2.1 p.2.2 p.1.2.2.2 := rfl

theorem treeCombine_valid {x : Ix} (hL : LibOK P x) (hg : ∀ p, (gatesSF x).ValidAt P p)
    (hw : ∀ p, (wiresSF x).ValidAt P p) (hr : ∀ p, (rippleF x).ValidAt P p)
    (hP : P[x.treeCombine]? = some (treeCombineBody x).compile) :
    ∀ p, (treeCombineF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, treeCombineBody, combFinish, hL, hg, hw, hr])
    (fun p => by simp [tm_simp, treeCombineBody, combFinish, treeCombine])

def countTreeCost (x : Ix) (v : ℕ) : ℕ → List ℕ → ℕ → ℕ
  | 0, _, _ => 30
  | k + 1, xs, z =>
    countTreeCost x v k (xs.take (xs.length / 2)) z + countTreeCost x v k (xs.drop (xs.length / 2)) z +
      (treeSplitF x).cost (v, k + 1, xs, z) +
      (treeCombineF x).cost ((v, k + 1, xs, z), Plain.countTree v k (xs.take (xs.length / 2)) z,
        Plain.countTree v k (xs.drop (xs.length / 2)) z) + 100

def countTreeDepth (x : Ix) (v : ℕ) : ℕ → List ℕ → ℕ → ℕ
  | 0, _, _ => 2
  | k + 1, xs, z =>
    countTreeDepth x v k (xs.take (xs.length / 2)) z + countTreeDepth x v k (xs.drop (xs.length / 2)) z +
      (treeSplitF x).depth (v, k + 1, xs, z) +
      (treeCombineF x).depth ((v, k + 1, xs, z), Plain.countTree v k (xs.take (xs.length / 2)) z,
        Plain.countTree v k (xs.drop (xs.length / 2)) z) + 10

def countTreeMsize (x : Ix) (v : ℕ) : ℕ → List ℕ → ℕ → ℕ
  | 0, xs, z => (Ty.enc (.list .nat) xs).size + 4 * z.size + 20
  | k + 1, xs, z =>
    countTreeMsize x v k (xs.take (xs.length / 2)) z + countTreeMsize x v k (xs.drop (xs.length / 2)) z +
      (treeSplitF x).msize (v, k + 1, xs, z) +
      (treeCombineF x).msize ((v, k + 1, xs, z), Plain.countTree v k (xs.take (xs.length / 2)) z,
        Plain.countTree v k (xs.drop (xs.length / 2)) z) +
      (Ty.enc (.prod TTreeArg (.prod TProg TProg)) ((v, k + 1, xs, z),
        Plain.countTree v k (xs.take (xs.length / 2)) z,
        Plain.countTree v k (xs.drop (xs.length / 2)) z)).size + 10

/-- `(v, (k, (xs, z))) ↦ countTree v k xs z`. -/
@[simps] def countTreeF (x : Ix) : FnSig TTreeArg TProg where
  idx := x.countTree
  den p := Plain.countTree p.1 p.2.1 p.2.2.1 p.2.2.2
  cost p := countTreeCost x p.1 p.2.1 p.2.2.1 p.2.2.2
  depth p := countTreeDepth x p.1 p.2.1 p.2.2.1 p.2.2.2
  msize p := countTreeMsize x p.1 p.2.1 p.2.2.1 p.2.2.2

def countTreeBody (x : Ix) : Tm [TTreeArg] TProg :=
  .ite (.isZero (.fst (.snd v0))) (.pair .lnil (.fst (.snd (.snd v0))))
    (.letE (.app (treeSplitF x) v0)
      (.app (treeCombineF x) (.pair v1 (.pair (.app (countTreeF x) (.fst v0))
        (.app (countTreeF x) (.snd v0))))))

theorem countTree_valid {x : Ix} (hs : ∀ p, (treeSplitF x).ValidAt P p)
    (hc : ∀ p, (treeCombineF x).ValidAt P p)
    (hP : P[x.countTree]? = some (countTreeBody x).compile) : ∀ p, (countTreeF x).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun p => p.2.1) ?_
  rintro ⟨(v : ℕ), (k : ℕ), xs, (z : ℕ)⟩ ih
  rcases k with _ | k
  · have h0 : (Ty.enc TGates ([] : List Plain.GateP)).size = 1 := rfl
    constructor <;> tm_auto [countTreeBody, countTreeCost, countTreeDepth, countTreeMsize,
      Plain.countTree]
  · have hl := ih (v, k, xs.take (xs.length / 2), z) (by simp)
    have hr := ih (v, k, xs.drop (xs.length / 2), z) (by simp)
    constructor <;> tm_auto [countTreeBody, countTreeCost, countTreeDepth, countTreeMsize,
      countTree_succ, treeSplit, hl, hr, hc, hs]

/-! ## Population counter -/

@[simps] def pow2SizeF (x : Ix) : FnSig .nat .nat where
  idx := x.pow2Size
  den n := Plain.pow2Size n
  cost n := 30 * n.size + 20
  depth n := n.size + 2
  msize n := 8 * n.size + 20

def pow2SizeBody (x : Ix) : Tm [.nat] .nat :=
  .ncase v0 (.lit (1 : ℕ)) (.letE (.app (pow2SizeF x) v1) (.bit .ff v0))

theorem pow2Size_rec {n : ℕ} (hn : n ≠ 0) : Plain.pow2Size n = 2 * Plain.pow2Size (n / 2) := by
  unfold Plain.pow2Size
  rw [← size_half hn, pow_succ]; ring

theorem pow2Size_size (n : ℕ) : (Plain.pow2Size n).size ≤ n.size + 1 := by
  unfold Plain.pow2Size
  rw [Nat.size_le]
  exact Nat.pow_lt_pow_right (by omega) (by omega)

theorem pow2Size_valid {x : Ix} (hP : P[x.pow2Size]? = some (pow2SizeBody x).compile) :
    ∀ n, (pow2SizeF x).ValidAt P n := by
  refine FnSig.valid_of_body _ _ hP (fun n => n) fun (n : ℕ) ih => ?_
  by_cases hn : n = 0
  · subst hn; constructor <;> tm_auto [pow2SizeBody, Plain.pow2Size]
  · have hs := size_half hn
    have hih := ih (n / 2) (by omega)
    have h1 := pow2Size_rec hn
    have h2 := pow2Size_size (n / 2)
    have h3 : Plain.pow2Size (n / 2) ≠ 0 := by unfold Plain.pow2Size; positivity
    constructor <;> tm_auto [pow2SizeBody, hn, hih, h1]

/-- `n ↦ range n ++ replicate (pow2Size (max 1 n) - n) n`. -/
def paddedWiresBody (x : Ix) : Tm [.nat] (.list .nat) :=
  .app (appendF .nat x.append) (.pair (.app (rangeF x.range) v0)
    (.app (replicateF .nat x.replicate) (.pair (.app (subF x.sub)
      (.pair (.app (pow2SizeF x) (.app (maxF x.max) (.pair (.lit (1 : ℕ)) v0))) v0)) v0)))

def paddedWiresF (x : Ix) : FnSig .nat (.list .nat) :=
  FnSig.exact x.paddedWires (paddedWiresBody x) Plain.paddedWires

@[simp] theorem paddedWiresF_den (x : Ix) (n : ℕ) : (paddedWiresF x).den n = Plain.paddedWires n := rfl

theorem paddedWires_valid {x : Ix} (hL : LibOK P x) (hp : ∀ n, (pow2SizeF x).ValidAt P n)
    (hP : P[x.paddedWires]? = some (paddedWiresBody x).compile) : ∀ n, (paddedWiresF x).ValidAt P n :=
  FnSig.exact_valid hP (fun n => by simp [tm_simp, paddedWiresBody, hL, hp])
    (fun n => by simp [tm_simp, paddedWiresBody, Plain.paddedWires])

def populationBody (x : Ix) : Tm [.nat] TProg :=
  .letE (.app (countTreeF x) (.pair (.app (succF x.succ) v0)
      (.pair (.app (bitLenF x.bitLen) (.app (maxF x.max) (.pair (.lit (1 : ℕ)) v0)))
        (.pair (.app (paddedWiresF x) v0) v0))))
    (.pair (.lcons (.lit (Plain.constGate false : Plain.GateP)) (.fst v0)) (.snd v0))

def populationF (x : Ix) : FnSig .nat TProg :=
  FnSig.exact x.population (populationBody x) Plain.population

@[simp] theorem populationF_den (x : Ix) (n : ℕ) : (populationF x).den n = Plain.population n := rfl

theorem population_valid {x : Ix} (hL : LibOK P x) (hc : ∀ p, (countTreeF x).ValidAt P p)
    (hp : ∀ n, (paddedWiresF x).ValidAt P n)
    (hP : P[x.population]? = some (populationBody x).compile) : ∀ n, (populationF x).ValidAt P n :=
  FnSig.exact_valid hP (fun n => by simp [tm_simp, populationBody, hL, hc, hp])
    (fun n => by simp [tm_simp, populationBody, Plain.population])

/-! ## Weight block -/

/-- `v0 = (r, (v, j))`. -/
def weightBlockBody (x : Ix) : Tm [.prod .nat (.prod .nat .nat)] TBlock :=
  .letE (.app (populationF x) (.fst v0))
  (.letE (.app (subF x.sub) (.pair (.fst (.snd v1)) (.fst v1)))
    (.app (matchBlockF x) (.pair (.fst (.snd v2))
      (.pair (.pair (.app (gatesSF x) (.pair (.pair (.fst v2) v0) (.fst v1)))
          (.app (wiresSF x) (.pair (.pair (.fst v2) v0) (.snd v1))))
        (.app (wordF x.word) (.pair (.app (succF x.succ)
            (.app (bitLenF x.bitLen) (.app (maxF x.max) (.pair (.lit (1 : ℕ)) (.fst v2)))))
          (.snd (.snd v2))))))))

def weightBlockF (x : Ix) : FnSig (.prod .nat (.prod .nat .nat)) TBlock :=
  FnSig.exact x.weightBlock (weightBlockBody x) (fun p => Plain.weightBlock p.1 p.2.1 p.2.2)

@[simp] theorem weightBlockF_den (x : Ix) (p : (Ty.prod .nat (.prod .nat .nat)).den) :
    (weightBlockF x).den p = Plain.weightBlock p.1 p.2.1 p.2.2 := rfl

theorem weightBlock_valid {x : Ix} (hL : LibOK P x) (hp : ∀ n, (populationF x).ValidAt P n)
    (hm : ∀ p, (matchBlockF x).ValidAt P p) (hg : ∀ p, (gatesSF x).ValidAt P p)
    (hw : ∀ p, (wiresSF x).ValidAt P p) (hword : ∀ p, (wordF x.word).ValidAt P p)
    (hP : P[x.weightBlock]? = some (weightBlockBody x).compile) : ∀ p, (weightBlockF x).ValidAt P p :=
  FnSig.exact_valid hP (fun p => by simp [tm_simp, weightBlockBody, hL, hp, hm, hg, hw, hword])
    (fun p => by simp [tm_simp, weightBlockBody, Plain.weightBlock])

end QecReliability.Trans.Query
