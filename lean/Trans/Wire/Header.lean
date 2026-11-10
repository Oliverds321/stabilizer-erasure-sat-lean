import Trans.Wire.Base

/-!
# Trans.Wire.Header: FL readers for headers, coordinates and repetitions

All functions are `bodySig`s (bounds = exact compositional bounds of the body) over library
recursions (`foldrF`, `foldlF`, `takeF`, `dropF`, `rangeF`, `reverseF`); no new recursion.

| FL | meaning |
|---|---|
| `onesF` (`foldrF onesStepF`) | `(bs, 0) ↦ ones bs` |
| `wordValF` (`foldrF bitStepF`) | `(bs, 0) ↦ wordVal bs` |
| `hdrF` | `bs ↦ hdr bs` (one `natHeader`) |
| `coordF` | `bs ↦ coordR bs` |
| `manyF F` (`foldlF (manyStepF F)` + `reverseF`) | `(k, bs) ↦ many F.den k bs` |

Every function is valid at every argument (`*_valid`), given `Lib.OK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Wire
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_valid)

/-- Indices of the header readers. -/
structure HIx where
  onesStep : ℕ
  ones : ℕ
  bitStep : ℕ
  wordVal : ℕ
  hdr : ℕ
  coord : ℕ

variable (L : Lib) (h : HIx)

/-! ## Bodies and signatures -/

def onesStepBody : Tm [.prod .bool .nat] .nat :=
  .ite (.fst v0) (.app (succF L.succ) (.snd v0)) .zero
def onesStepF : FnSig (.prod .bool .nat) .nat := bodySig h.onesStep (onesStepBody L)
def onesF : FnSig (.prod (.list .bool) .nat) .nat := foldrF (onesStepF L h) h.ones

def bitStepBody : Tm [.prod .bool .nat] .nat := .bit (.fst v0) (.snd v0)
def bitStepF : FnSig (.prod .bool .nat) .nat := bodySig h.bitStep bitStepBody
def wordValF : FnSig (.prod (.list .bool) .nat) .nat := foldrF (bitStepF h) h.wordVal

/-- `bs ↦ (wordVal (take k r), drop k r)` with `k = ones bs`, `r = drop (k+1) bs`. -/
def hdrBody : Tm [.list .bool] (.prod .nat (.list .bool)) :=
  .letE (.app (onesF L h) (.pair v0 .zero)) <|
  .letE (.app (dropF .bool L.drop) (.pair (.app (succF L.succ) v0) v1)) <|
  .pair (.app (wordValF h) (.pair (.app (takeF .bool L.take) (.pair v1 v0)) .zero))
    (.app (dropF .bool L.drop) (.pair v1 v0))
def hdrF : FnSig (.list .bool) (.prod .nat (.list .bool)) := bodySig h.hdr (hdrBody L h)

/-- One coordinate. -/
def coordBody : Tm [.list .bool] (.prod (.prod .bool .nat) (.list .bool)) :=
  .lcase v0 (.lit ((false, 0), []))
    (.letE (.app (hdrF L h) v1) (.pair (.pair v1 (.fst v0)) (.snd v0)))
def coordF : FnSig (.list .bool) (.prod (.prod .bool .nat) (.list .bool)) :=
  bodySig h.coord (coordBody L h)

section Many
variable {t : Ty} (F : FnSig (.list .bool) (.prod t (.list .bool)))

def manyStepBody : Tm [.prod (.prod (.list t) (.list .bool)) .nat] (.prod (.list t) (.list .bool)) :=
  .letE (.app F (.snd (.fst v0))) (.pair (.lcons (.fst v0) (.fst (.fst v1))) (.snd v0))
def manyStepF (i : ℕ) : FnSig (.prod (.prod (.list t) (.list .bool)) .nat) (.prod (.list t) (.list .bool)) :=
  bodySig i (manyStepBody F)

/-- `(k, bs) ↦ many F.den k bs`. -/
def manyBody (iStep iFold : ℕ) : Tm [.prod .nat (.list .bool)] (.prod (.list t) (.list .bool)) :=
  .letE (.app (foldlF (manyStepF F iStep) iFold)
      (.pair (.pair .lnil (.snd v0)) (.app (rangeF L.range) (.fst v0)))) <|
  .pair (.app (reverseF t L.rev) (.fst v0)) (.snd v0)
def manyF (iStep iFold i : ℕ) : FnSig (.prod .nat (.list .bool)) (.prod (.list t) (.list .bool)) :=
  bodySig i (manyBody L F iStep iFold)

end Many

/-! ## Meaning -/

theorem onesStepF_den (x : Bool × ℕ) : (onesStepF L h).den x = onesStep x.1 x.2 := by
  obtain ⟨b, n⟩ := x
  cases b <;> simp [onesStepF, bodySig_den, onesStepBody, tm_simp, onesStep]

theorem onesF_den (bs : List Bool) : (onesF L h).den (bs, 0) = ones bs := by
  simp only [onesF, foldrF_den, foldrDen, ones]
  congr 1

theorem bitStepF_den (x : Bool × ℕ) : (bitStepF h).den x = bitNat x.1 x.2 := by
  obtain ⟨b, n⟩ := x
  simp [bitStepF, bodySig_den, bitStepBody, tm_simp]

theorem wordValF_den (bs : List Bool) : (wordValF h).den (bs, 0) = wordVal bs := by
  simp only [wordValF, foldrF_den, foldrDen, wordVal]
  congr 1

theorem hdrF_den (bs : List Bool) : (hdrF L h).den bs = hdr bs := by
  simp only [hdrF, bodySig_den, hdrBody, tm_simp, dropF_den, takeF_den, succF_den]
  rw [onesF_den, wordValF_den]
  rfl

theorem coordF_den (bs : List Bool) : (coordF L h).den bs = coordR bs := by
  cases bs with
  | nil => rfl
  | cons b tl =>
    simp only [coordF, bodySig_den, coordBody, tm_simp]
    rw [hdrF_den]
    rfl

theorem manyF_den {t : Ty} (F : FnSig (.list .bool) (.prod t (.list .bool))) (iStep iFold i : ℕ)
    (k : ℕ) (bs : List Bool) : (manyF L F iStep iFold i).den (k, bs) = many F.den k bs := by
  simp only [manyF, bodySig_den, manyBody, tm_simp, foldlF_den, foldlDen, rangeF_den,
    reverseF_den]
  rfl

/-! ## Validity -/

/-- The bodies are installed at their indices. -/
structure HIx.OK (P : Program) : Prop where
  onesStep : P[h.onesStep]? = some (onesStepBody L).compile
  ones : P[h.ones]? = some (foldrBody (onesStepF L h) h.ones).compile
  bitStep : P[h.bitStep]? = some bitStepBody.compile
  wordVal : P[h.wordVal]? = some (foldrBody (bitStepF h) h.wordVal).compile
  hdr : P[h.hdr]? = some (hdrBody L h).compile
  coord : P[h.coord]? = some (coordBody L h).compile

section Valid
variable {L h} {P : Program} (hL : L.OK P) (hH : h.OK L P)
include hL hH

theorem ones_valid : ∀ x, (onesF L h).ValidAt P x := by
  have hs : ∀ x, (onesStepF L h).ValidAt P x := fun x => by
    refine bodySig_valid hH.onesStep ?_
    obtain ⟨b, n⟩ := x
    cases b <;> simp [tm_simp, onesStepBody, hL.succ]
  exact Hash.foldr_validAll hs hH.ones

theorem wordVal_valid : ∀ x, (wordValF h).ValidAt P x := by
  have hs : ∀ x, (bitStepF h).ValidAt P x := fun x =>
    bitSig_valid' hH.bitStep x
  exact Hash.foldr_validAll hs hH.wordVal
where
  bitSig_valid' {P : Program} {i : ℕ} (hb : P[i]? = some bitStepBody.compile) (x : Bool × ℕ) :
      (bodySig i bitStepBody).ValidAt P x :=
    bodySig_valid hb (by simp [tm_simp, bitStepBody])

theorem hdr_valid : ∀ x, (hdrF L h).ValidAt P x := fun x => by
  refine bodySig_valid hH.hdr ?_
  simp [tm_simp, hdrBody, ones_valid hL hH, wordVal_valid hL hH, hL.succ, hL.take, hL.drop]

theorem coord_valid : ∀ x, (coordF L h).ValidAt P x := fun x => by
  refine bodySig_valid hH.coord ?_
  cases x with
  | nil => simp [tm_simp, coordBody]
  | cons b tl => simp [tm_simp, coordBody, hdr_valid hL hH]

end Valid

theorem many_valid {L : Lib} {P : Program} (hL : L.OK P) {t : Ty}
    {F : FnSig (.list .bool) (.prod t (.list .bool))} {iStep iFold i : ℕ}
    (hF : ∀ x, F.ValidAt P x) (hS : P[iStep]? = some (manyStepBody F).compile)
    (hFo : P[iFold]? = some (foldlBody (manyStepF F iStep) iFold).compile)
    (hM : P[i]? = some (manyBody L F iStep iFold).compile) :
    ∀ x, (manyF L F iStep iFold i).ValidAt P x := by
  have hs : ∀ x, (manyStepF F iStep).ValidAt P x := fun x =>
    bodySig_valid hS (by simp [tm_simp, manyStepBody, hF])
  have hf := Hash.foldl_validAll hs hFo
  exact fun x => bodySig_valid hM (by simp [tm_simp, manyBody, hf, hL.range, hL.rev])

end QecReliability.Trans.Wire
