import Trans.Control.Base
import Trans.Hash.FLWalk
import WholeWrapperInputEncoding

/-!
# Trans.Wire.Base: library indices and plain readers for the input encoding

* `Lib`: program indices of the FL library functions used by the wire package, and
  `Lib.OK P L` (all valid in `P`; `divModF` only for positive divisors).
* Plain (total) readers of the self-delimiting input encoding
  (`WholeWrapperCandidate.InputEncoding.problemBits`):
  - `ones bs`: number of leading `true`s (as a `foldr`);
  - `wordVal bs`: little-endian value (as a `foldr` of `bitNat`);
  - `hdr bs = (value, rest)`: one `QueryCodec.natHeader` (`hdr_natHeader`);
  - `coordR`: one coordinate (`coordR_coordBits`);
  - `many f k bs`: `k` items read by `f` (a `foldl` over `range k`, then `reverse`),
    `many_flatMap`: reading back `xs.flatMap enc`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Wire
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.OracleCost

/-! ## Library indices -/

/-- Program indices of the library functions used by the wire package. -/
structure Lib where
  succ : ℕ
  pred : ℕ
  add : ℕ
  sub : ℕ
  le : ℕ
  eq : ℕ
  mul : ℕ
  bitLen : ℕ
  dm : ℕ
  take : ℕ
  drop : ℕ
  range : ℕ
  rev : ℕ
  rep : ℕ

/-- `divModF` at the library indices. -/
abbrev Lib.dmF (L : Lib) : FnSig (.prod .nat .nat) (.prod .nat .nat) :=
  Hash.divModF L.le L.sub L.dm

/-- The library functions are valid in `P` (element-type generic for list functions). -/
structure Lib.OK (P : Program) (L : Lib) : Prop where
  succ : ∀ x, (succF L.succ).ValidAt P x
  pred : ∀ x, (predF L.pred).ValidAt P x
  add : ∀ x, (addF L.add).ValidAt P x
  sub : ∀ x, (subF L.sub).ValidAt P x
  le : ∀ x, (leF L.le).ValidAt P x
  eq : ∀ x, (eqF L.eq).ValidAt P x
  mul : ∀ x, (mulF L.mul).ValidAt P x
  bitLen : ∀ x, (bitLenF L.bitLen).ValidAt P x
  dm : ∀ x : ℕ × ℕ, 0 < x.2 → L.dmF.ValidAt P x
  take : ∀ (t : Ty) x, (takeF t L.take).ValidAt P x
  drop : ∀ (t : Ty) x, (dropF t L.drop).ValidAt P x
  range : ∀ x, (rangeF L.range).ValidAt P x
  rev : ∀ (t : Ty) x, (reverseF t L.rev).ValidAt P x
  rep : ∀ (t : Ty) x, (replicateF t L.rep).ValidAt P x

@[simp] theorem Lib.dmF_den (L : Lib) (x : ℕ × ℕ) : L.dmF.den x = (x.1 / x.2, x.1 % x.2) := rfl

/-! ## Plain readers -/

/-- One step of `ones`. -/
def onesStep (b : Bool) (acc : ℕ) : ℕ := if b then acc + 1 else 0

/-- Number of leading `true`s. -/
def ones (bs : List Bool) : ℕ := bs.foldr onesStep 0

/-- Little-endian value of a bit string. -/
def wordVal (bs : List Bool) : ℕ := bs.foldr bitNat 0

/-- Read one `natHeader`: `(value, rest)`. -/
def hdr (bs : List Bool) : ℕ × List Bool :=
  (wordVal ((bs.drop (ones bs + 1)).take (ones bs)), (bs.drop (ones bs + 1)).drop (ones bs))

theorem ones_prefix (k : ℕ) (tl : List Bool) :
    ones (List.replicate k true ++ false :: tl) = k := by
  induction k with
  | zero => simp [ones, onesStep]
  | succ k ih =>
    simp only [ones, List.replicate_succ, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih]
    simp [onesStep]

theorem wordVal_word (k n : ℕ) (h : n < 2 ^ k) : wordVal (QueryCodec.word k n) = n := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using h
    subst this; rfl
  | succ k ih =>
    have h2 : n / 2 < 2 ^ k := by rw [pow_succ] at h; omega
    have ih' := ih (n / 2) h2
    simp only [wordVal] at ih'
    simp only [QueryCodec.word, wordVal, List.foldr_cons, ih', bitNat]
    split_ifs with hb <;> simp at hb <;> omega

theorem drop_prefix (k : ℕ) (tl : List Bool) :
    (List.replicate k true ++ false :: tl).drop (k + 1) = tl := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ] using ih

theorem hdr_natHeader (n : ℕ) (rest : List Bool) :
    hdr (QueryCodec.natHeader n ++ rest) = (n, rest) := by
  have e : QueryCodec.natHeader n ++ rest =
      List.replicate n.size true ++ false :: (QueryCodec.word n.size n ++ rest) := by
    simp [QueryCodec.natHeader]
  rw [e]
  unfold hdr
  rw [ones_prefix, drop_prefix]
  have hl := QueryCodec.word_length n.size n
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
    wordVal_word _ _ (Nat.lt_size_self n)]
  rfl

/-- Read one coordinate: a type bit, then a header. -/
def coordR : List Bool → (Bool × ℕ) × List Bool
  | [] => ((false, 0), [])
  | b :: tl => ((b, (hdr tl).1), (hdr tl).2)

theorem coordR_coordBits {n : ℕ} (c : SharedCircuit.PauliCoord n) (rest : List Bool) :
    coordR (WholeWrapperCandidate.InputEncoding.coordBits c ++ rest) = (Query.encCoord c, rest) := by
  cases c with
  | inl i =>
    simp only [WholeWrapperCandidate.InputEncoding.coordBits, List.cons_append, coordR,
      hdr_natHeader, Query.encCoord]
  | inr i =>
    simp only [WholeWrapperCandidate.InputEncoding.coordBits, List.cons_append, coordR,
      hdr_natHeader, Query.encCoord]

/-- One step of `many`. -/
def manyStep {α : Type} (f : List Bool → α × List Bool) (st : List α × List Bool) (_ : ℕ) :
    List α × List Bool :=
  ((f st.2).1 :: st.1, (f st.2).2)

/-- Read `k` items with `f`. -/
def many {α : Type} (f : List Bool → α × List Bool) (k : ℕ) (bs : List Bool) :
    List α × List Bool :=
  (((List.range k).foldl (manyStep f) ([], bs)).1.reverse,
    ((List.range k).foldl (manyStep f) ([], bs)).2)

theorem foldl_manyStep {α β : Type} (f : List Bool → α × List Bool) (enc : β → List Bool)
    (g : β → α) (hf : ∀ x rest, f (enc x ++ rest) = (g x, rest)) (rest : List Bool) :
    ∀ (xs : List β) (l : List ℕ) (acc : List α), l.length = xs.length →
      l.foldl (manyStep f) (acc, xs.flatMap enc ++ rest) = ((xs.map g).reverse ++ acc, rest) := by
  intro xs
  induction xs with
  | nil =>
    intro l acc hl
    cases l with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons x xs ih =>
    intro l acc hl
    cases l with
    | nil => simp at hl
    | cons i l =>
      simp only [List.length_cons, add_left_inj] at hl
      simp only [List.foldl_cons, List.flatMap_cons, List.append_assoc]
      have hs : manyStep f (acc, enc x ++ (xs.flatMap enc ++ rest)) i =
          (g x :: acc, xs.flatMap enc ++ rest) := by
        simp only [manyStep, hf]
      rw [hs, ih l (g x :: acc) hl]
      simp

theorem many_flatMap {α β : Type} (f : List Bool → α × List Bool) (enc : β → List Bool)
    (g : β → α) (hf : ∀ x rest, f (enc x ++ rest) = (g x, rest)) (xs : List β)
    (rest : List Bool) : many f xs.length (xs.flatMap enc ++ rest) = (xs.map g, rest) := by
  unfold many
  rw [foldl_manyStep f enc g hf rest xs _ [] (by simp)]
  simp

end QecReliability.Trans.Wire
