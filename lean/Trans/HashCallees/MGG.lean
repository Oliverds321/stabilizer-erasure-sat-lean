import Trans.HashCallees.Base

/-!
# Trans.HashCallees.MGG: the lazy MGG rotation and neighbour map

Plain layer (values instead of `Fin`):
* `coordP n a b c inv`: one shear coordinate `a ± (2b + c) mod n`;
* `mggRotP n v p` (`p < 8`): the MGG rotation `mgg_rot` on `v = x * n + y`, written with the
  three bits of the port (which coordinate moves, the `+1` shift, the inverse);
* `lazyRotP s v i`: the rotation of `lazyMGGPortGraph s` (ports `≥ 8` hold);
* `nbrP s v i`: `gNbr actualMGG s v i` (`0` off the domain).

Correspondence: `mggNbr_bits`, `lazyMGG_rotation` (values of the rotation of
`lazyMGGPortGraph s hs`), `gNbr_actual : gNbr actualMGG = nbrP`.

FL: `coordF`, `mggRotF`, `lazyRotF`, `nbrF` (exact signatures), validity
`coord_valid` (`n > 0`), `mggRot_valid`, `lazyRot_valid` (`s > 0`), `nbr_valid` (all arguments).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.HashCallees
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.Trans.Hash

/-! ## Plain layer -/

/-- One shear coordinate: `(a + 2b + c) mod n`, or its inverse `(a + 2n - (2b + c)) mod n`. -/
def coordP (n a b : ℕ) (c inv : Bool) : ℕ :=
  if inv then (a + 2 * n - bitNat c b) % n else (a + bitNat c b) % n

/-- The MGG rotation on values for a port `p < 8` (vertex `v = x * n + y`). -/
def mggRotP (n v p : ℕ) : ℕ × ℕ :=
  ((if decide (p / 2 % 2 = 1) then v / n
      else coordP n (v / n) (v % n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))) * n +
    (if decide (p / 2 % 2 = 1)
      then coordP n (v % n) (v / n) (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))
      else v % n),
   if decide (p % 2 = 1) then p - 1 else p + 1)

/-- The rotation of the half-lazy MGG graph on values. -/
def lazyRotP (s v i : ℕ) : ℕ × ℕ := if i < 8 then mggRotP s v i else (v, i)

/-- The neighbour map of `actualMGG` on values. -/
def nbrP (s v i : ℕ) : ℕ := if 3 ≤ s ∧ v < s * s ∧ i < 16 then (lazyRotP s v i).1 else 0

/-! ## Correspondence -/

theorem mggNbr_bits (n x y p : ℕ) (hp : p < 8) :
    mggNbr n x y p =
      (if decide (p / 2 % 2 = 1) then x
        else coordP n x y (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1)),
       if decide (p / 2 % 2 = 1) then coordP n y x (decide (p / 2 / 2 % 2 = 1)) (decide (p % 2 = 1))
        else y,
       if decide (p % 2 = 1) then p - 1 else p + 1) := by
  interval_cases p <;> simp only [mggNbr, coordP, bitNat] <;> norm_num <;>
    (try simp only [Prod.mk.injEq]) <;> (try refine ⟨?_, ?_⟩) <;>
    (try simp only [Prod.mk.injEq, and_true, true_and]) <;>
    (try (congr 1; omega)) <;> (try ring_nf) <;> (try (congr 1; omega))

theorem mggRotP_eq (n v p : ℕ) (hp : p < 8) :
    mggRotP n v p = ((mggNbr n (v / n) (v % n) p).1 * n + (mggNbr n (v / n) (v % n) p).2.1,
      (mggNbr n (v / n) (v % n) p).2.2) := by
  rw [mggNbr_bits n _ _ p hp]; rfl

open ExpanderWalk in
/-- **The rotation of `lazyMGGPortGraph s` on values.** -/
theorem lazyMGG_rotation (s : ℕ) (hs : 3 ≤ s) (v : Fin (s * s)) (i : Fin 16) :
    ((lazyMGGPortGraph s hs).rotation (v, i)).1.val = (lazyRotP s v.val i.val).1 ∧
    ((lazyMGGPortGraph s hs).rotation (v, i)).2.val = (lazyRotP s v.val i.val).2 := by
  change ((mggPortGraph s hs).lazyRotation (v, i)).1.val = _ ∧
    ((mggPortGraph s hs).lazyRotation (v, i)).2.val = _
  by_cases hi : i.val < 8
  · obtain ⟨j, rfl⟩ : ∃ j : Fin 8, i = Fin.castAdd 8 j := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    rw [PortGraph.lazyRotation_left]
    have hj : j.val < 8 := j.isLt
    simp only [lazyRotP, Fin.coe_castAdd, if_pos hj]
    rw [mggRotP_eq _ _ _ j.isLt]
    exact ⟨rfl, rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j : Fin 8, i = Fin.natAdd 8 j :=
      ⟨⟨i.val - 8, by omega⟩, Fin.ext (by simp; omega)⟩
    rw [PortGraph.lazyRotation_right]
    have hj : ¬ 8 + j.val < 8 := by omega
    refine ⟨?_, ?_⟩ <;> (try simp only [lazyRotP, Fin.coe_natAdd, if_neg hj]) <;> (try rfl)

open UniformAdapter in
/-- **The neighbour oracle of the hash: `gNbr actualMGG = nbrP`.** -/
theorem gNbr_actual (s v i : ℕ) : gNbr actualMGG s v i = nbrP s v i := by
  unfold gNbr nbrP
  by_cases h : 3 ≤ s ∧ v < s * s ∧ i < 16
  · rw [dif_pos h, if_pos h]
    exact (lazyMGG_rotation s h.1 ⟨v, h.2.1⟩ ⟨i, h.2.2⟩).1
  · rw [dif_neg h, if_neg h]

/-! ## FL -/

variable {P : Program}

abbrev TCoord : Ty := .prod .nat (.prod .nat (.prod .nat (.prod .bool .bool)))

/-- `(n, a, b, c, inv) ↦ coordP n a b c inv`. -/
def coordBody (L : Lib) : Tm [TCoord] .nat :=
  .ite (.snd (.snd (.snd (.snd v0))))
    (.snd (.app L.dmF (.pair
      (.app (subF L.sub) (.pair (.app (addF L.add) (.pair (.fst (.snd v0)) (.bit .ff (.fst v0))))
        (.bit (.fst (.snd (.snd (.snd v0)))) (.fst (.snd (.snd v0))))))
      (.fst v0))))
    (.snd (.app L.dmF (.pair
      (.app (addF L.add) (.pair (.fst (.snd v0))
        (.bit (.fst (.snd (.snd (.snd v0)))) (.fst (.snd (.snd v0))))))
      (.fst v0))))

def coordF (L : Lib) (i : ℕ) : FnSig TCoord .nat :=
  exactSig i (coordBody L) (fun x => coordP x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)

theorem coord_valid {L : Lib} (hL : L.OK P) {i : ℕ} (hP : P[i]? = some (coordBody L).compile) :
    ∀ x : TCoord.den, 0 < x.1 → (coordF L i).ValidAt P x :=
  exactSig_valid hP _
    (fun x hx => by
      obtain ⟨n, a, b, c, inv⟩ := x
      simp only at hx
      cases inv <;> simp [tm_simp, coordBody, hL.add, hL.sub, hL.dm' _ hx])
    (fun x _ => by
      obtain ⟨n, a, b, c, inv⟩ := x
      cases inv <;> simp [tm_simp, coordBody, coordP])

/-- Context `[c, b1, b0, (x, y), (n, v, p)]`. -/
def mggRotBody (L : Lib) (icoord : ℕ) : Tm [.prod .nat (.prod .nat .nat)] (.prod .nat .nat) :=
  .letE (.app L.dmF (.pair (.fst (.snd v0)) (.fst v0)))
  (.letE (.app (oddF L.odd) (.snd (.snd v1)))
  (.letE (.app (oddF L.odd) (.app (div2F L.div2) (.snd (.snd v2))))
  (.letE (.app (oddF L.odd) (.app (div2F L.div2) (.app (div2F L.div2) (.snd (.snd v3)))))
    (.pair
      (.app (addF L.add) (.pair
        (.app (mulF L.mul) (.pair
          (.ite v1 (.fst v3)
            (.app (coordF L icoord) (.pair (.fst v4) (.pair (.fst v3) (.pair (.snd v3)
              (.pair v0 v2))))))
          (.fst v4)))
        (.ite v1
          (.app (coordF L icoord) (.pair (.fst v4) (.pair (.snd v3) (.pair (.fst v3)
            (.pair v0 v2)))))
          (.snd v3))))
      (.ite v2 (.app (predF L.pred) (.snd (.snd v4))) (.app (succF L.succ) (.snd (.snd v4))))))))

def mggRotF (L : Lib) (icoord i : ℕ) : FnSig (.prod .nat (.prod .nat .nat)) (.prod .nat .nat) :=
  exactSig i (mggRotBody L icoord) (fun x => mggRotP x.1 x.2.1 x.2.2)

theorem mggRot_valid {L : Lib} (hL : L.OK P) {icoord i : ℕ}
    (hc : P[icoord]? = some (coordBody L).compile) (hP : P[i]? = some (mggRotBody L icoord).compile) :
    ∀ x : (Ty.prod .nat (.prod .nat .nat)).den, 0 < x.1 → (mggRotF L icoord i).ValidAt P x :=
  exactSig_valid hP _
    (fun x hx => by
      obtain ⟨n, v, p⟩ := x
      simp only at hx
      have hcv : ∀ y : TCoord.den, y.1 = n → (coordF L icoord).ValidAt P y :=
        fun y hy => coord_valid hL hc y (hy ▸ hx)
      simp [tm_simp, mggRotBody, hL.add, hL.mul, hL.pred, hL.succ, hL.odd, hL.div2, hL.dm' _ hx,
        hcv])
    (fun x _ => by
      obtain ⟨n, v, p⟩ := x
      simp only [mggRotBody, tm_simp, Lib.dmF_den, addF_den, mulF_den, predF_den, succF_den,
        oddF_den, div2F_den, coordF, exactSig_den, mggRotP, Env.one])

def lazyRotBody (L : Lib) (irot : ℕ) (icoord : ℕ) :
    Tm [.prod .nat (.prod .nat .nat)] (.prod .nat .nat) :=
  .ite (.app (ltF L.lt) (.pair (.snd (.snd v0)) (.lit (8 : ℕ))))
    (.app (mggRotF L icoord irot) v0) (.snd v0)

def lazyRotF (L : Lib) (icoord irot i : ℕ) :
    FnSig (.prod .nat (.prod .nat .nat)) (.prod .nat .nat) :=
  exactSig i (lazyRotBody L irot icoord) (fun x => lazyRotP x.1 x.2.1 x.2.2)

theorem lazyRot_valid {L : Lib} (hL : L.OK P) {icoord irot i : ℕ}
    (hc : P[icoord]? = some (coordBody L).compile)
    (hr : P[irot]? = some (mggRotBody L icoord).compile)
    (hP : P[i]? = some (lazyRotBody L irot icoord).compile) :
    ∀ x : (Ty.prod .nat (.prod .nat .nat)).den, 0 < x.1 → (lazyRotF L icoord irot i).ValidAt P x :=
  exactSig_valid hP _
    (fun x hx => by
      obtain ⟨n, v, p⟩ := x
      have h := mggRot_valid hL hc hr (n, v, p) hx
      simp [tm_simp, lazyRotBody, hL.lt, h])
    (fun x _ => by
      obtain ⟨n, v, p⟩ := x
      simp only [lazyRotBody, tm_simp, ltF_den, mggRotF, exactSig_den, lazyRotP, Env.one]
      split_ifs <;> simp_all)

def nbrBody (L : Lib) (irot icoord : ℕ) : Tm [.prod .nat (.prod .nat .nat)] .nat :=
  .ite (.and (.app (leF L.le) (.pair (.lit (3 : ℕ)) (.fst v0)))
      (.and (.app (ltF L.lt) (.pair (.fst (.snd v0)) (.app (mulF L.mul) (.pair (.fst v0) (.fst v0)))))
        (.app (ltF L.lt) (.pair (.snd (.snd v0)) (.lit (16 : ℕ))))))
    (.ite (.app (ltF L.lt) (.pair (.snd (.snd v0)) (.lit (8 : ℕ))))
      (.fst (.app (mggRotF L icoord irot) v0)) (.fst (.snd v0)))
    .zero

/-- **The neighbour oracle** `inb : (s, v, i) ↦ gNbr actualMGG s v i`. -/
def nbrF (L : Lib) (irot icoord i : ℕ) : FnSig (.prod .nat (.prod .nat .nat)) .nat :=
  exactSig i (nbrBody L irot icoord) (fun x => nbrP x.1 x.2.1 x.2.2)

theorem nbr_valid {L : Lib} (hL : L.OK P) {icoord irot i : ℕ}
    (hc : P[icoord]? = some (coordBody L).compile)
    (hr : P[irot]? = some (mggRotBody L icoord).compile)
    (hP : P[i]? = some (nbrBody L irot icoord).compile) :
    ∀ x, (nbrF L irot icoord i).ValidAt P x := fun x =>
  exactSig_valid hP (fun _ => True)
    (fun x _ => by
      obtain ⟨(s : ℕ), (v : ℕ), (p : ℕ)⟩ := x
      by_cases hs : 3 ≤ s
      · have h := mggRot_valid hL hc hr (s, v, p) (show 0 < s by omega)
        simp [tm_simp, nbrBody, hL.lt, hL.le, hL.mul, h]
      · simp [tm_simp, nbrBody, hL.lt, hL.le, hL.mul, hs])
    (fun x _ => by
      obtain ⟨s, v, p⟩ := x
      simp only [nbrBody, tm_simp, ltF_den, leF_den, mulF_den, mggRotF, exactSig_den, nbrP,
        lazyRotP, Env.one, den_and]
      by_cases h1 : 3 ≤ s <;> by_cases h2 : v < s * s <;> by_cases h3 : p < 16 <;>
        by_cases h4 : p < 8 <;> simp [h1, h2, h3, h4]) x trivial

open UniformAdapter in
/-- The meaning of `nbrF` is the neighbour map of `actualMGG`. -/
theorem nbrF_den (L : Lib) (irot icoord i : ℕ) (x : ℕ × ℕ × ℕ) :
    (nbrF L irot icoord i).den x = gNbr actualMGG x.1 x.2.1 x.2.2 :=
  (gNbr_actual _ _ _).symm

end QecReliability.Trans.HashCallees
