import Trans.Hash.FLWire

/-!
# Trans.Hash.FLList: small list functions

* `ipairsF t`: `[(x₀, k), (x₁, k+1), …]` (generic `idxPairs`), with mirror bounds
  `ipCost/ipDepth/ipMsize`;
* `setF` (`List.set` on naturals, as a map over `ipairs`), `dropLastF` (`take (len-1)`).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Hash
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.Trans.Query.Plain

variable {P : Program}

/-- Generic `idxPairs`. -/
def ipairs {α : Type} : List α → ℕ → List (α × ℕ)
  | [], _ => []
  | x :: xs, k => (x, k) :: ipairs xs (k + 1)

theorem idxPairs_eq (os : List ℕ) (k : ℕ) : idxPairs os k = ipairs os k := by
  induction os generalizing k with
  | nil => rfl
  | cons o os ih => simp [idxPairs, ipairs, ih]

theorem ipairs_length {α : Type} (xs : List α) (k : ℕ) : (ipairs xs k).length = xs.length := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => simp [ipairs, ih]

theorem ipairs_getElem {α : Type} (xs : List α) (k j : ℕ) (h : j < (ipairs xs k).length) :
    (ipairs xs k)[j] = (xs[j]'(by simpa [ipairs_length] using h), k + j) := by
  induction xs generalizing k j with
  | nil => simp [ipairs] at h
  | cons x xs ih =>
    cases j with
    | zero => simp [ipairs]
    | succ j =>
      simp only [ipairs, List.getElem_cons_succ]
      rw [ih]; simp; omega

def ipCost {α : Type} : List α → ℕ → ℕ
  | [], _ => 10
  | _ :: xs, k => ipCost xs (k + 1) + 25 * k.size + 60

def ipDepth {α : Type} : List α → ℕ → ℕ
  | [], _ => 1
  | _ :: xs, k => max (ipDepth xs (k + 1)) (k.size + 1) + 1

theorem enc_ip_cons (t : Ty) (x : t.den) (k : ℕ) (l : List (t.den × ℕ)) :
    (Ty.enc (.list (.prod t .nat)) ((x, k) :: l)).size =
      1 + (1 + (t.enc x).size + (Enc.nat k).size) + (Ty.enc (.list (.prod t .nat)) l).size := rfl

@[simps] def ipairsF (t : Ty) (i : ℕ) : FnSig (.prod (.list t) .nat) (.list (.prod t .nat)) where
  idx := i
  den p := ipairs p.1 p.2
  cost p := ipCost p.1 p.2
  depth p := ipDepth p.1 p.2
  msize p := 2 * (Ty.enc (.list (.prod t .nat)) (ipairs p.1 p.2)).size +
    8 * (p.2 + p.1.length).size + (Ty.enc (.list t) p.1).size + 30

def ipairsBody (t : Ty) (isucc i : ℕ) : Tm [.prod (.list t) .nat] (.list (.prod t .nat)) :=
  .lcase (.fst v0) .lnil
    (.lcons (.pair v0 (.snd v2)) (.app (ipairsF t i) (.pair v1 (.app (succF isucc) (.snd v2)))))

theorem ipairs_valid {t : Ty} {isucc i : ℕ} (hs : ∀ n, (succF isucc).ValidAt P n)
    (hP : P[i]? = some (ipairsBody t isucc i).compile) :
    ∀ p, (ipairsF t i).ValidAt P p := by
  refine FnSig.valid_of_body _ _ hP (fun (p : (Ty.prod (.list t) .nat).den) => p.1.length) ?_
  rintro ⟨(_ | ⟨x, xs⟩), (k : ℕ)⟩ ih
  · constructor <;> tm_auto [ipairsBody, ipCost, ipDepth, ipairs]
  · have hih := ih (xs, k + 1) (by simp)
    have hg : (Ty.enc (.list (.prod t .nat)) (ipairs (x :: xs) k)).size =
        1 + (Ty.enc (.prod t .nat) (x, k)).size +
          (Ty.enc (.list (.prod t .nat)) (ipairs xs (k + 1))).size :=
      Ty.sz_list_cons (.prod t .nat) (x, k) (ipairs xs (k + 1))
    have hg' : (Ty.enc (.list (.prod t .nat)) ((x, k) :: ipairs xs (k + 1))).size =
        1 + (Ty.enc (.prod t .nat) (x, k)).size +
          (Ty.enc (.list (.prod t .nat)) (ipairs xs (k + 1))).size :=
      Ty.sz_list_cons (.prod t .nat) (x, k) (ipairs xs (k + 1))
    have hp : (Ty.enc (.prod t .nat) (x, k)).size = 1 + (t.enc x).size + (Enc.nat k).size := rfl
    have hl := Ty.sz_list_cons t x xs
    have hS : k + 1 + xs.length = k + (x :: xs).length := by simp; omega
    have h1 := size_mono (show k ≤ k + (x :: xs).length by omega)
    have h2 := Enc.nat_size_le (k + 1)
    have h3 := size_mono (show k + 1 ≤ k + (x :: xs).length by simp)
    constructor
    · tm_auto [ipairsBody, hih, hs]
    · tm_auto [ipairsBody, hih, hs, ipairs]
    · tm_auto [ipairsBody, hih, hs, ipCost]
    · tm_auto [ipairsBody, hih, hs, ipDepth]
    · tm_lean [ipairsBody, hih, hs, ipairsF_msize, ipairsF_den, succF_msize, succF_den, hS]

/-! ## `List.set` and `dropLast` on naturals -/

theorem set_eq_map (l : List ℕ) (i a : ℕ) :
    l.set i a = (ipairs l 0).map (fun p => if p.2 = i then a else p.1) := by
  apply List.ext_getElem
  · simp [ipairs_length]
  · intro j h1 h2
    simp only [List.getElem_set, List.getElem_map, ipairs_getElem, Nat.zero_add]
    split_ifs <;> first | rfl | omega

/-- One element of `set`: `((i, a), (x, j)) ↦ if j = i then a else x`. -/
def setStepBody (ieq : ℕ) : Tm [.prod (.prod .nat .nat) (.prod .nat .nat)] .nat :=
  .ite (.app (eqF ieq) (.pair (.snd (.snd v0)) (.fst (.fst v0)))) (.snd (.fst v0))
    (.fst (.snd v0))

def setStepF (ieq i : ℕ) : FnSig (.prod (.prod .nat .nat) (.prod .nat .nat)) .nat :=
  exactSig i (setStepBody ieq) (fun x => if x.2.2 = x.1.1 then x.1.2 else x.2.1)

theorem setStep_valid {ieq i : ℕ} (heq : ∀ x, (eqF ieq).ValidAt P x)
    (hP : P[i]? = some (setStepBody ieq).compile) : ∀ x, (setStepF ieq i).ValidAt P x :=
  fun x => exactSig_valid hP (fun _ => True) (fun _ _ => by simp [tm_simp, setStepBody, heq])
    (fun x _ => by simp [tm_simp, setStepBody]) x trivial

/-- `set (l, i, a) = l.set i a`; `imap = mapEnvF (setStepF ieq is) im`. -/
def setBody (iip : ℕ) (imap : FnSig (.prod (.prod .nat .nat) (.list (.prod .nat .nat))) (.list .nat)) :
    Tm [.prod (.list .nat) (.prod .nat .nat)] (.list .nat) :=
  .app imap (.pair (.snd v0) (.app (ipairsF .nat iip) (.pair (.fst v0) .zero)))

def setF (iip : ℕ) (imap : FnSig (.prod (.prod .nat .nat) (.list (.prod .nat .nat))) (.list .nat))
    (i : ℕ) : FnSig (.prod (.list .nat) (.prod .nat .nat)) (.list .nat) :=
  exactSig i (setBody iip imap) (fun x => x.1.set x.2.1 x.2.2)

theorem set_valid {isucc iip ieq is im i : ℕ} (hs : ∀ n, (succF isucc).ValidAt P n)
    (hip : P[iip]? = some (ipairsBody .nat isucc iip).compile)
    (heq : ∀ x, (eqF ieq).ValidAt P x) (hss : P[is]? = some (setStepBody ieq).compile)
    (hm : P[im]? = some (mapEnvBody (setStepF ieq is) im).compile)
    (hP : P[i]? = some (setBody iip (mapEnvF (setStepF ieq is) im)).compile) :
    ∀ x, (setF iip (mapEnvF (setStepF ieq is) im) i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      simp only [setBody, tm_simp, true_and]
      exact ⟨ipairs_valid hs hip _,
        mapEnv_valid hm _ (fun y _ => setStep_valid heq hss _)⟩)
    (fun x _ => by
      simp only [setBody, tm_simp, mapEnvF_den, ipairsF_den, setStepF, exactSig_den]
      rw [set_eq_map]) x trivial

theorem dropLast_eq_take {α : Type} (l : List α) : l.dropLast = l.take (l.length - 1) :=
  List.dropLast_eq_take

def dropLastBody (ilen ipred itake : ℕ) : Tm [.list .nat] (.list .nat) :=
  .app (takeF .nat itake) (.pair (.app (predF ipred) (.app (lengthF .nat ilen) v0)) v0)

def dropLastF (ilen ipred itake i : ℕ) : FnSig (.list .nat) (.list .nat) :=
  exactSig i (dropLastBody ilen ipred itake) (fun l => l.dropLast)

theorem dropLast_valid {ilen ipred itake i : ℕ} (hlen : ∀ x, (lengthF .nat ilen).ValidAt P x)
    (hpred : ∀ x, (predF ipred).ValidAt P x) (htake : ∀ x, (takeF .nat itake).ValidAt P x)
    (hP : P[i]? = some (dropLastBody ilen ipred itake).compile) :
    ∀ x, (dropLastF ilen ipred itake i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun _ _ => by simp [tm_simp, dropLastBody, hlen, hpred, htake])
    (fun x _ => by simp [tm_simp, dropLastBody, List.dropLast_eq_take]) x trivial

end QecReliability.Trans.Hash
