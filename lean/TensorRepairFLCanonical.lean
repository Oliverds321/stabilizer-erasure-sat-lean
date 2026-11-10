import TensorRepairFL
import TensorRepairFLCanonicalBits
import Trans.Control.Rank

/-! Installed FL construction of canonical latent bit words and recognition of
corner keys. The bit word has length equal to the total number of latent causes,
not the number of coefficient slots. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid)

structure CanonicalIndices where
  bit : ℕ
  blockMap : ℕ
  block : ℕ
  bitsStep : ℕ
  bitsFold : ℕ
  bits : ℕ
  cornerStep : ℕ
  cornerFold : ℕ
  corner : ℕ

abbrev TBits : Ty := .list .bool

def bitsStepR (s : List ℕ × List Bool) (r : ℕ) : List ℕ × List Bool :=
  match s.1 with
  | [] => ([],s.2)
  | k :: ks => (ks,s.2 ++ canonicalBlock r k)

def cornerR : List ℕ → List ℕ → Bool
  | [], [] => true
  | r :: ds, k :: ks => (decide (k=0) || decide (k=r)) && cornerR ds ks
  | _, _ => false

def cornerStepR (s : List ℕ × Bool) (r : ℕ) : List ℕ × Bool :=
  match s.1 with
  | [] => ([],false)
  | k :: ks => (ks,s.2 && (decide (k=0) || decide (k=r)))

theorem bitsFoldR (ds ks : List ℕ) (acc : List Bool) :
    ds.foldl bitsStepR (ks,acc) = (ks.drop ds.length,acc ++ canonicalBits ds ks) := by
  induction ds generalizing ks acc with
  | nil => simp [canonicalBits]
  | cons r ds ih =>
    cases ks with
    | nil => simp [List.foldl_cons, bitsStepR, ih, canonicalBits]
    | cons k ks => simp [List.foldl_cons, bitsStepR, ih, canonicalBits, List.append_assoc]

theorem cornerFold_finish (ds ks : List ℕ) (b : Bool) :
    keyFinish (ds.foldl cornerStepR (ks,b)) = (b && cornerR ds ks) := by
  induction ds generalizing ks b with
  | nil => cases ks <;> simp [keyFinish,cornerR]
  | cons r ds ih =>
    cases ks with
    | nil => simpa [List.foldl_cons,cornerStepR,cornerR] using ih [] false
    | cons k ks =>
      simpa only [List.foldl_cons,cornerStepR,cornerR,Bool.and_assoc] using
        ih ks (b && (decide (k=0) || decide (k=r)))

theorem cornerR_index (ds : List ℕ) (j : TensorBernstein.Grid ds) :
    cornerR ds (TensorMachine.indexList ds j) = RationalTensorRepair.cornerTest ds j := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    rcases j with ⟨j,js⟩
    change ((decide (j.val = 0) || decide (j.val = r)) &&
      cornerR ds (TensorMachine.indexList ds js)) =
      ((j.val == 0 || j.val == r) && RationalTensorRepair.cornerTest ds js)
    have hb : (decide (j.val = 0) || decide (j.val = r)) =
        (j.val == 0 || j.val == r) := by
      by_cases h0 : j.val = 0 <;> by_cases hr : j.val = r <;> simp [h0,hr]
    rw [ih, hb]

variable (L : Lib) (i : CanonicalIndices) (iappend : ℕ)

def canonicalBitBody : Tm [.prod .nat .nat] .bool :=
  .not (.app (leF L.le) v0)

def canonicalBitF := bodySig i.bit (canonicalBitBody L)

def blockBody : Tm [.prod .nat .nat] TBits :=
  .app (Trans.Hash.mapEnvF (canonicalBitF L i) i.blockMap)
    (.pair (.snd v0) (.app (rangeF L.range) (.fst v0)))

def blockF := bodySig i.block (blockBody L i)

def bitsStepBody : Tm [.prod (.prod TKey TBits) .nat] (.prod TKey TBits) :=
  .lcase (.fst (.fst v0)) (.pair .lnil (.snd (.fst v0)))
    (.pair v1 (.app (appendF .bool iappend)
      (.pair (.snd (.fst v2)) (.app (blockF L i) (.pair (.snd v2) v0)))))

def bitsStepF := bodySig i.bitsStep (bitsStepBody L i iappend)

def bitsBody : Tm [.prod TKey TKey] TBits :=
  .snd (.app (foldlF (bitsStepF L i iappend) i.bitsFold)
    (.pair (.pair (.snd v0) .lnil) (.fst v0)))

def bitsF := bodySig i.bits (bitsBody L i iappend)

def cornerStepBody : Tm [.prod (.prod TKey .bool) .nat] (.prod TKey .bool) :=
  .lcase (.fst (.fst v0)) (.pair .lnil .ff)
    (.pair v1 (.and (.snd (.fst v2))
      (.or (.isZero v0) (.app (eqF L.eq) (.pair v0 (.snd v2))))))

def cornerStepF := bodySig i.cornerStep (cornerStepBody L)

def cornerBody : Tm [.prod TKey TKey] .bool :=
  .letE (.app (foldlF (cornerStepF L i) i.cornerFold)
    (.pair (.pair (.snd v0) .tt) (.fst v0))) <|
    .lcase (.fst v0) (.snd v0) .ff

def cornerF := bodySig i.corner (cornerBody L i)

theorem canonicalBitF_den (k x : ℕ) : (canonicalBitF L i).den (k,x) = decide (x<k) := by
  simp only [canonicalBitF,bodySig_den,canonicalBitBody,tm_simp]
  by_cases h : k ≤ x
  · have hn : ¬ x < k := Nat.not_lt.mpr h
    simp [h,hn]
  · have hl : x < k := Nat.lt_of_not_ge h
    simp [h,hl]

theorem blockF_den (r k : ℕ) : (blockF L i).den (r,k) = canonicalBlock r k := by
  change (List.range r).map (fun x => (canonicalBitF L i).den (k,x)) =
    (List.range r).map (fun x => decide (x<k))
  apply List.map_congr_left
  intro x hx
  exact canonicalBitF_den L i k x

theorem bitsStepF_den (ks : List ℕ) (acc : List Bool) (r : ℕ) :
    (bitsStepF L i iappend).den ((ks,acc),r) = bitsStepR (ks,acc) r := by
  cases ks with
  | nil => rfl
  | cons k ks =>
    change (ks,acc ++ (blockF L i).den (r,k)) = _
    rw [blockF_den]
    rfl

theorem bitsFold_den (ds : List ℕ) (s : List ℕ × List Bool) :
    foldlDen (bitsStepF L i iappend) s ds = ds.foldl bitsStepR s := by
  induction ds generalizing s with
  | nil => rfl
  | cons r ds ih =>
    rcases s with ⟨ks,acc⟩
    rw [foldlDen_cons,bitsStepF_den,ih,List.foldl_cons]

theorem bitsF_den (ds ks : List ℕ) :
    (bitsF L i iappend).den (ds,ks) = canonicalBits ds ks := by
  change (foldlDen (bitsStepF L i iappend) (ks,[]) ds).2 = _
  rw [bitsFold_den,bitsFoldR]
  rfl

theorem cornerStepF_den (ks : List ℕ) (b : Bool) (r : ℕ) :
    (cornerStepF L i).den ((ks,b),r) = cornerStepR (ks,b) r := by
  cases ks <;> simp [cornerStepF,bodySig_den,cornerStepBody,tm_simp,cornerStepR]

theorem cornerFold_den (ds : List ℕ) (s : List ℕ × Bool) :
    foldlDen (cornerStepF L i) s ds = ds.foldl cornerStepR s := by
  induction ds generalizing s with
  | nil => rfl
  | cons r ds ih =>
    rcases s with ⟨ks,b⟩
    rw [foldlDen_cons,cornerStepF_den,ih,List.foldl_cons]

theorem cornerF_den (ds ks : List ℕ) : (cornerF L i).den (ds,ks) = cornerR ds ks := by
  simp only [cornerF,bodySig_den,cornerBody,tm_simp,foldlF_den]
  rw [cornerFold_den]
  have h := cornerFold_finish ds ks true
  generalize he : ds.foldl cornerStepR (ks,true) = s at h ⊢
  rcases s with ⟨js,b⟩
  cases js <;> simpa only [keyFinish,Bool.true_and] using h

structure CanonicalIndices.OK (P : FL.Program) : Prop where
  bit : P[i.bit]? = some (canonicalBitBody L).compile
  blockMap : P[i.blockMap]? = some (Trans.Hash.mapEnvBody (canonicalBitF L i) i.blockMap).compile
  block : P[i.block]? = some (blockBody L i).compile
  bitsStep : P[i.bitsStep]? = some (bitsStepBody L i iappend).compile
  bitsFold : P[i.bitsFold]? = some (foldlBody (bitsStepF L i iappend) i.bitsFold).compile
  bits : P[i.bits]? = some (bitsBody L i iappend).compile
  cornerStep : P[i.cornerStep]? = some (cornerStepBody L).compile
  cornerFold : P[i.cornerFold]? = some (foldlBody (cornerStepF L i) i.cornerFold).compile
  corner : P[i.corner]? = some (cornerBody L i).compile

variable {L i iappend} {P : FL.Program}

theorem canonicalBit_valid (hL : L.OK P) (hi : CanonicalIndices.OK L i iappend P) :
    ∀ x, (canonicalBitF L i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.bit
  simp [canonicalBitBody,tm_simp,hL.le]

theorem block_valid (hL : L.OK P) (hi : CanonicalIndices.OK L i iappend P) :
    ∀ x, (blockF L i).ValidAt P x := by
  have hm := Trans.Hash.mapEnv_validAll (canonicalBit_valid hL hi) hi.blockMap
  intro x
  apply bodySig_valid hi.block
  simp [blockBody,tm_simp,hL.range,hm]

theorem bitsStep_valid (hL : L.OK P) (hi : CanonicalIndices.OK L i iappend P)
    (ha : ∀ x, (appendF .bool iappend).ValidAt P x) :
    ∀ x, (bitsStepF L i iappend).ValidAt P x := by
  intro x
  apply bodySig_valid hi.bitsStep
  simp [bitsStepBody,tm_simp,block_valid hL hi,ha] <;> split <;> trivial

theorem bits_valid (hL : L.OK P) (hi : CanonicalIndices.OK L i iappend P)
    (ha : ∀ x, (appendF .bool iappend).ValidAt P x) :
    ∀ x, (bitsF L i iappend).ValidAt P x := by
  have hf := Trans.Hash.foldl_validAll (bitsStep_valid hL hi ha) hi.bitsFold
  intro x
  apply bodySig_valid hi.bits
  simp [bitsBody,tm_simp,hf]

theorem cornerStep_valid (hL : L.OK P) (hi : CanonicalIndices.OK L i iappend P) :
    ∀ x, (cornerStepF L i).ValidAt P x := by
  intro x
  apply bodySig_valid hi.cornerStep
  simp [cornerStepBody,tm_simp,hL.eq] <;> split <;> trivial

theorem corner_valid (hL : L.OK P) (hi : CanonicalIndices.OK L i iappend P) :
    ∀ x, (cornerF L i).ValidAt P x := by
  have hf := Trans.Hash.foldl_validAll (cornerStep_valid hL hi) hi.cornerFold
  intro x
  apply bodySig_valid hi.corner
  simp [cornerBody,tm_simp,hf] <;> split <;> trivial

end QecReliability.TensorMachine.RepairFL
