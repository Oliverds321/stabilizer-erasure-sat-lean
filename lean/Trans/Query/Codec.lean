import Trans.Query.ListEnv
import OracleCost.QueryCodec

/-!
# Trans.Query.Codec: `QueryCodec.encode` in FL

Plain formulas are `list (list (nat × bool))` (`QueryCodec.PlainFormula`), literals are
`(index, sign)`. The functions transcribed here are exactly those of
`OracleCost/QueryCodec.lean`:

| FL | meaning |
|---|---|
| `wordF` | `(k, n) ↦ word k n` |
| `natHeaderF` | `n ↦ natHeader n` |
| `literalF` | `(k, lit) ↦ literal k lit` |
| `literalsF` (`flatMapEnvF literalF`) | `(k, ls) ↦ literals k ls` |
| `clauseF` | `(k, c) ↦ clause k c` |
| `bodyF` (`flatMapEnvF clauseF`) | `(k, F) ↦ body k F` |
| `encodeF` | `(v, F) ↦ natHeader v ++ natHeader F.length ++ body v.size F` |

`encodeF_den` identifies `encodeF` with `QueryCodec.encode` on a request (via `plain`).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Query
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.OracleCost

/-- Literal `(index, sign)`, clause, plain formula. -/
scoped notation "TLit" => Ty.prod Ty.nat Ty.bool
scoped notation "TClause" => Ty.list (Ty.prod Ty.nat Ty.bool)
scoped notation "TForm" => Ty.list (Ty.list (Ty.prod Ty.nat Ty.bool))
scoped notation "TBits" => Ty.list Ty.bool

variable {P : Program}

/-! ## `word` -/

def wordCost : ℕ → ℕ
  | 0 => 10
  | k + 1 => wordCost k + 25 * (k + 1).size + 80

@[simp] theorem wordCost_zero : wordCost 0 = 10 := rfl
@[simp] theorem wordCost_succ (k : ℕ) : wordCost (k + 1) = wordCost k + 25 * (k + 1).size + 80 := rfl

theorem sz_word (k n : ℕ) : (Ty.enc (.list .bool) (QueryCodec.word k n)).size ≤ 4 * k + 1 := by
  have h := Ty.sz_list_le .bool (QueryCodec.word k n) 3 (fun b _ => Ty.sz_bool_le b)
  simp only [QueryCodec.word_length] at h
  omega

@[simps] def wordF (i : ℕ) : FnSig (.prod .nat .nat) TBits where
  idx := i
  den p := QueryCodec.word p.1 p.2
  cost p := wordCost p.1
  depth p := p.1 + p.1.size + 2
  msize p := 4 * p.1 + 8 * p.1.size + 4 * p.2.size + 20

def wordBody (ip i : ℕ) : Tm [.prod .nat .nat] TBits :=
  .ncase (.fst v0) .lnil
    (.lcons (.odd (.snd v2)) (.app (wordF i) (.pair (.app (predF ip) (.fst v2)) (.div2 (.snd v2)))))

theorem word_valid {ip i : ℕ} (hp : ∀ n, (predF ip).ValidAt P n)
    (hP : P[i]? = some (wordBody ip i).compile) : ∀ x, (wordF i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.1) ?_
  rintro ⟨(k : ℕ), (n : ℕ)⟩ ih
  by_cases hk : k = 0
  · subst hk; constructor <;> tm_auto [wordBody, QueryCodec.word]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hih := ih (m, n / 2) (by simp)
  have h1 := size_mono (show m ≤ m + 1 by omega)
  have h2 := size_half_le n
  have h3 : 1 ≤ (m + 1).size := size_pos_of_ne (by omega)
  have h4 := sz_word m (n / 2)
  by_cases hn : n = 0
  · subst hn
    have h5 := sz_word m 0
    constructor
    · tm_auto [wordBody, hp, hih, QueryCodec.word]
    · tm_auto [wordBody, hp, hih, QueryCodec.word]
    · tm_auto [wordBody, hp, hih, QueryCodec.word]
    · tm_auto [wordBody, hp, hih, QueryCodec.word]
    · tm_auto [wordBody, hp, hih, QueryCodec.word]
  · constructor
    · tm_auto [wordBody, hp, hih, QueryCodec.word, hn]
    · tm_auto [wordBody, hp, hih, QueryCodec.word, hn]
    · tm_auto [wordBody, hp, hih, QueryCodec.word, hn]
    · tm_auto [wordBody, hp, hih, QueryCodec.word, hn]
    · tm_auto [wordBody, hp, hih, QueryCodec.word, hn]

/-! ## `natHeader` -/

def natHeaderCost (n : ℕ) : ℕ :=
  30 * (n.size + 1) * (n.size + 1) + 40 * (n.size + 1) * (n.size.size + 1) + wordCost n.size +
    15 * n.size + 60

@[simps] def natHeaderF (i : ℕ) : FnSig .nat TBits where
  idx := i
  den n := QueryCodec.natHeader n
  cost n := natHeaderCost n
  depth n := 2 * n.size + 2 * n.size.size + 10
  msize n := 24 * n.size + 4 * n.size.size + 40

def natHeaderBody (ib ir ia iw : ℕ) : Tm [.nat] TBits :=
  .letE (.app (bitLenF ib) v0)
    (.app (appendF .bool ia) (.pair (.app (replicateF .bool ir) (.pair v0 .tt))
      (.lcons .ff (.app (wordF iw) (.pair v0 v1)))))

theorem sz_replicate_true (k : ℕ) :
    (Ty.enc (.list .bool) (List.replicate k true)).size = 4 * k + 1 := by
  rw [Ty.sz_replicate]; simp; omega

theorem natHeader_valid {ib ir ia iw i : ℕ} (hb : ∀ n, (bitLenF ib).ValidAt P n)
    (hr : ∀ x, (replicateF .bool ir).ValidAt P x) (ha : ∀ x, (appendF .bool ia).ValidAt P x)
    (hw : ∀ x, (wordF iw).ValidAt P x)
    (hP : P[i]? = some (natHeaderBody ib ir ia iw).compile) : ∀ n, (natHeaderF i).ValidAt P n := by
  refine FnSig.valid_of_body_nonrec _ _ hP fun (n : ℕ) => ?_
  have h1 := sz_replicate_true n.size
  have h2 := sz_word n.size n
  have h3 := size_le_self n.size
  constructor <;> tm_auto [natHeaderBody, hb, hr, ha, hw, natHeaderCost, QueryCodec.natHeader]

/-! ## Literals and clauses -/

theorem size_one : Nat.size 1 = 1 := by
  have := size_half (n := 1) (by omega); simpa using this.symm

theorem size_two : Nat.size 2 = 2 := by
  have := size_half (n := 2) (by omega); rw [show 2 / 2 = 1 by rfl, size_one] at this; omega

@[simps] def literalF (i : ℕ) : FnSig (.prod .nat TLit) TBits where
  idx := i
  den p := QueryCodec.literal p.1 p.2
  cost p := wordCost p.1 + 20
  depth p := p.1 + p.1.size + 3
  msize p := 8 * p.1 + 8 * p.1.size + 4 * p.2.1.size + 30

def literalBody (iw : ℕ) : Tm [.prod .nat TLit] TBits :=
  .lcons (.snd (.snd v0)) (.app (wordF iw) (.pair (.fst v0) (.fst (.snd v0))))

theorem literal_valid {iw i : ℕ} (hw : ∀ x, (wordF iw).ValidAt P x)
    (hP : P[i]? = some (literalBody iw).compile) : ∀ x, (literalF i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(k : ℕ), (j : ℕ), b⟩
  have h2 := sz_word k j
  constructor <;> tm_auto [literalBody, hw, QueryCodec.literal]

/-- `literals = flatMapEnv literal`. -/
abbrev literalsF (il i : ℕ) : FnSig (.prod .nat TClause) TBits := flatMapEnvF (literalF il) i

theorem literalsF_den (il i : ℕ) (p : ℕ × List (ℕ × Bool)) :
    (literalsF il i).den p = QueryCodec.literals p.1 p.2 := rfl

theorem literals_valid {il ia i : ℕ} (hl : ∀ x, (literalF il).ValidAt P x)
    (ha : ∀ x, (appendF .bool ia).ValidAt P x)
    (hP : P[i]? = some (flatMapEnvBody (literalF il) ia i).compile) :
    ∀ x, (literalsF il i).ValidAt P x :=
  fun x => flatMapEnv_valid ha hP x (fun _ _ => hl _)

/-- `clause (k, c) = word 2 c.length ++ literals k c`. -/
@[simps] def clauseF (il ils i : ℕ) : FnSig (.prod .nat TClause) TBits where
  idx := i
  den p := QueryCodec.clause p.1 p.2
  cost p := (lengthF TLit 0).cost p.2 + wordCost 2 + (literalsF il ils).cost p + 15 * 2 + 60
  depth p := (lengthF TLit 0).depth p.2 + (literalsF il ils).depth p + 10
  msize p := (lengthF TLit 0).msize p.2 + (literalsF il ils).msize p + 4 * p.2.length.size + 120

def clauseBody (il ils ilen iw ia : ℕ) : Tm [.prod .nat TClause] TBits :=
  .app (appendF .bool ia)
    (.pair (.app (wordF iw) (.pair (.lit (2 : ℕ)) (.app (lengthF TLit ilen) (.snd v0))))
      (.app (literalsF il ils) v0))

theorem clause_valid {il ils ilen iw ia i : ℕ} (hls : ∀ x, (literalsF il ils).ValidAt P x)
    (hlen : ∀ x, (lengthF TLit ilen).ValidAt P x) (hw : ∀ x, (wordF iw).ValidAt P x)
    (ha : ∀ x, (appendF .bool ia).ValidAt P x)
    (hP : P[i]? = some (clauseBody il ils ilen iw ia).compile) :
    ∀ x, (clauseF il ils i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(k : ℕ), c⟩
  have h2 := sz_word 2 c.length
  have h3 : (Enc.nat 2).size = 7 := by
    rw [Enc.nat_pos (by omega)]; simp [Enc.nat_one, Enc.bool]
  have h4 : Nat.size 2 = 2 := size_two
  constructor <;> tm_auto [clauseBody, hls, hlen, hw, ha, QueryCodec.clause, QueryCodec.literals,
    flatMapEnvMsize, flatMapEnvDepth]

/-- `body = flatMapEnv clause`. -/
abbrev bodyF (il ils ic i : ℕ) : FnSig (.prod .nat TForm) TBits := flatMapEnvF (clauseF il ils ic) i

theorem bodyF_den (il ils ic i : ℕ) (p : ℕ × List (List (ℕ × Bool))) :
    (bodyF il ils ic i).den p = QueryCodec.body p.1 p.2 := rfl

theorem body_valid {il ils ic ia i : ℕ} (hc : ∀ x, (clauseF il ils ic).ValidAt P x)
    (ha : ∀ x, (appendF .bool ia).ValidAt P x)
    (hP : P[i]? = some (flatMapEnvBody (clauseF il ils ic) ia i).compile) :
    ∀ x, (bodyF il ils ic i).ValidAt P x :=
  fun x => flatMapEnv_valid ha hP x (fun _ _ => hc _)

/-! ## `encode` -/

/-- The serialization of a plain formula over `v` variables. -/
def encodePlain (v : ℕ) (F : QueryCodec.PlainFormula) : List Bool :=
  QueryCodec.natHeader v ++ QueryCodec.natHeader F.length ++ QueryCodec.body v.size F

theorem encode_eq_encodePlain (req : SATRequest) :
    QueryCodec.encode req = encodePlain req.varCount (QueryCodec.plain req.formula) := by
  simp [QueryCodec.encode, encodePlain, QueryCodec.plain]

theorem sz_bits (xs : List Bool) : (Ty.enc (.list .bool) xs).size ≤ 4 * xs.length + 1 := by
  have h := Ty.sz_list_le .bool xs 3 (fun b _ => Ty.sz_bool_le b)
  omega

def encodeCost (il ils ic ib : ℕ) (v : ℕ) (F : List (List (ℕ × Bool))) : ℕ :=
  natHeaderCost v + natHeaderCost F.length + (lengthF TClause 0).cost F +
    30 * (v.size + 1) * (v.size + 1) + (bodyF il ils ic ib).cost (v.size, F) +
    30 * v.size + 30 * F.length.size + 150

def encodeDepth (il ils ic ib : ℕ) (v : ℕ) (F : List (List (ℕ × Bool))) : ℕ :=
  2 * v.size + 2 * v.size.size + 2 * F.length.size + 2 * F.length.size.size +
    (lengthF TClause 0).depth F + 2 * v.size + (bodyF il ils ic ib).depth (v.size, F) + 40

def encodeMsize (il ils ic ib : ℕ) (v : ℕ) (F : List (List (ℕ × Bool))) : ℕ :=
  24 * v.size + 4 * v.size.size + 24 * F.length.size + 4 * F.length.size.size +
    (lengthF TClause 0).msize F + (bodyF il ils ic ib).msize (v.size, F) +
    2 * (Ty.enc (.list .bool) (encodePlain v F)).size + (Ty.enc TForm F).size + 200

@[simps] def encodeF (il ils ic ib i : ℕ) : FnSig (.prod .nat TForm) TBits where
  idx := i
  den p := encodePlain p.1 p.2
  cost p := encodeCost il ils ic ib p.1 p.2
  depth p := encodeDepth il ils ic ib p.1 p.2
  msize p := encodeMsize il ils ic ib p.1 p.2

def encodeBody (il ils ic ib ih ilen ibl ia : ℕ) : Tm [.prod .nat TForm] TBits :=
  .app (appendF .bool ia) (.pair (.app (natHeaderF ih) (.fst v0))
    (.app (appendF .bool ia) (.pair (.app (natHeaderF ih) (.app (lengthF TClause ilen) (.snd v0)))
      (.app (bodyF il ils ic ib) (.pair (.app (bitLenF ibl) (.fst v0)) (.snd v0))))))

theorem encode_valid {il ils ic ib ih ilen ibl ia i : ℕ}
    (hb : ∀ x, (bodyF il ils ic ib).ValidAt P x) (hh : ∀ x, (natHeaderF ih).ValidAt P x)
    (hlen : ∀ x, (lengthF TClause ilen).ValidAt P x) (hbl : ∀ x, (bitLenF ibl).ValidAt P x)
    (ha : ∀ x, (appendF .bool ia).ValidAt P x)
    (hP : P[i]? = some (encodeBody il ils ic ib ih ilen ibl ia).compile) :
    ∀ x, (encodeF il ils ic ib i).ValidAt P x := by
  refine FnSig.valid_of_body_nonrec _ _ hP ?_
  rintro ⟨(v : ℕ), F⟩
  have hbody : QueryCodec.body v.size F = List.flatMap (fun x => QueryCodec.clause v.size x) F := rfl
  have e1 := Ty.sz_list_append .bool (QueryCodec.natHeader v)
    (QueryCodec.natHeader F.length ++ List.flatMap (fun x => QueryCodec.clause v.size x) F)
  have e2 := Ty.sz_list_append .bool (QueryCodec.natHeader F.length)
    (List.flatMap (fun x => QueryCodec.clause v.size x) F)
  have e3 : (Ty.enc (.list .bool) (encodePlain v F)).size =
      (Ty.enc (.list .bool) (QueryCodec.natHeader v ++
        (QueryCodec.natHeader F.length ++ List.flatMap (fun x => QueryCodec.clause v.size x) F))).size := by
    simp [encodePlain, List.append_assoc, hbody]
  have p1 := Ty.sz_pos (.list .bool) (List.flatMap (fun x => QueryCodec.clause v.size x) F)
  have p2 := Ty.sz_pos (.list .bool) (QueryCodec.natHeader F.length)
  have p3 := Ty.sz_pos (.list .bool) (QueryCodec.natHeader v)
  have l1 := QueryCodec.natHeader_length v
  have l2 := QueryCodec.natHeader_length F.length
  constructor
  · tm_auto [encodeBody, hb, hh, hlen, hbl, ha]
  · simp [tm_simp, encodeBody, encodePlain, List.append_assoc, hbody]
  · tm_auto [encodeBody, hb, hh, hlen, hbl, ha, encodeCost]
  · tm_auto [encodeBody, hb, hh, hlen, hbl, ha, encodeDepth]
  · tm_auto [encodeBody, hb, hh, hlen, hbl, ha, encodeMsize]

end QecReliability.Trans.Query
