import Trans.Hash.Main
import ActualMGGInstantiationCandidate

/-!
# Trans.HashCallees.Base: library indices for the hash callees

`Lib` collects the program indices of the FL library functions used by the callees
(`FL/Lib/{Nat,List}.lean`, `divModF` from `Trans/Hash/FLWalk.lean`, `pcomposeF` and its
table helpers from `Trans/Hash/FLWire.lean`); `Lib.OK P L` says they are valid in `P`.
Every validity theorem of this package takes one `L.OK P` instead of a dozen hypotheses.
-/

set_option autoImplicit false

namespace QecReliability.Trans.HashCallees
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.Trans.Hash

/-- Program indices of the library functions. -/
structure Lib where
  succ : ℕ
  pred : ℕ
  add : ℕ
  sub : ℕ
  le : ℕ
  lt : ℕ
  mul : ℕ
  dm : ℕ
  range : ℕ
  len : ℕ
  app : ℕ
  rep : ℕ
  odd : ℕ
  div2 : ℕ
  gd : ℕ

/-- `divModF` at the library indices. -/
abbrev Lib.dmF (L : Lib) : FnSig (.prod .nat .nat) (.prod .nat .nat) := divModF L.le L.sub L.dm

/-- The library functions are valid in `P`. -/
structure Lib.OK (P : Program) (L : Lib) : Prop where
  succ : ∀ x, (succF L.succ).ValidAt P x
  pred : ∀ x, (predF L.pred).ValidAt P x
  add : ∀ x, (addF L.add).ValidAt P x
  sub : ∀ x, (subF L.sub).ValidAt P x
  le : ∀ x, (leF L.le).ValidAt P x
  lt : ∀ x, (ltF L.lt).ValidAt P x
  mul : ∀ x, (mulF L.mul).ValidAt P x
  dm : ∀ x : ℕ × ℕ, 0 < x.2 → L.dmF.ValidAt P x
  range : ∀ x, (rangeF L.range).ValidAt P x
  len : ∀ (t : Ty) x, (lengthF t L.len).ValidAt P x
  app : ∀ (t : Ty) x, (appendF t L.app).ValidAt P x
  rep : ∀ (t : Ty) x, (replicateF t L.rep).ValidAt P x
  odd : ∀ x, (oddF L.odd).ValidAt P x
  div2 : ∀ x, (div2F L.div2).ValidAt P x
  gd : ∀ x, (getDF .nat L.gd).ValidAt P x

theorem Lib.OK.dm' {P : Program} {L : Lib} (h : L.OK P) (a : ℕ) {b : ℕ} (hb : 0 < b) :
    L.dmF.ValidAt P (a, b) := h.dm (a, b) hb

@[simp] theorem Lib.dmF_den (L : Lib) (x : ℕ × ℕ) : L.dmF.den x = (x.1 / x.2, x.1 % x.2) := rfl

end QecReliability.Trans.HashCallees
