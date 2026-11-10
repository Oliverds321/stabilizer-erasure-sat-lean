import FL.Lib.Nat

/-!
# FL library: lists

Element types are arbitrary `t : Ty`. Higher-order functions (`map`, `filter`, `foldr`,
`foldl`, `flatMap`) are instantiated per callee: `mapF F i` is the global function at index
`i` mapping the global function `F`. Their validity theorems are parametric in the callee's
contract and only require it on the arguments actually used.

Bounds (`n` = list length, `‖v‖` = encoded size `(t.enc v).size`, `k.size` = bit length):

| function | meaning | cost | depth |
|---|---|---|---|
| `lengthF` | `xs.length` | `30(n+1)(n.size+1)` | `2n + 2` |
| `appendF` | `xs ++ ys` | `15n + 15` | `n + 1` |
| `revAppF`, `reverseF` | `xs.reverse ++ ys`, `xs.reverse` | `15n + 25` | `n + 2` |
| `mapF F` | `xs.map F.den` | `Σ (F.cost x + 10) + 10` | `n + 1 + max F.depth` |
| `filterF F` | `xs.filter F.den` | `Σ (F.cost x + 12) + 10` | `n + 1 + max F.depth` |
| `flatMapF F` | `xs.flatMap F.den` | `Σ (F.cost x + 15‖F x‖ₗ + 30) + 10` | linear |
| `foldrF F`, `foldlF F` | folds | recursive; `foldr_bounds`/`foldl_bounds`: `(K + 12) n + 10` | `n + D + 1` |
| `rangeFromF`, `rangeF` | `List.range' k n`, `List.range n` | `60(n+1)((k+n).size+1)` | `n + (k+n).size + 2` |
| `replicateF` | `List.replicate n x` | `40(n+1)(n.size+1)` | `n + n.size + 2` |
| `getDF` | `xs.getD n d` | `50(len+1)(n.size+1)` | `len + n.size + 2` |
| `takeF`, `dropF` | `xs.take n`, `xs.drop n` | `50(len+1)(n.size+1)` | `len + n.size + 2` |

Size budgets (`msize`) are stated in terms of encoded sizes of arguments and results; see
each signature and the closed-form lemmas `Ty.sz_*`, `sz_range'_le`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.FL.Lib
open Tm NatSize

variable {P : Program}

/-! ## Maximum of a function over a list -/

def maxOf {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => max (f x) (maxOf f xs)

@[simp] theorem maxOf_nil {α : Type} (f : α → ℕ) : maxOf f [] = 0 := rfl
@[simp] theorem maxOf_cons {α : Type} (f : α → ℕ) (x : α) (xs : List α) :
    maxOf f (x :: xs) = max (f x) (maxOf f xs) := rfl

theorem le_maxOf {α : Type} (f : α → ℕ) {xs : List α} {x : α} (h : x ∈ xs) :
    f x ≤ maxOf f xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp
    · simp [ih h']

theorem maxOf_le {α : Type} (f : α → ℕ) (xs : List α) (M : ℕ) (h : ∀ x ∈ xs, f x ≤ M) :
    maxOf f xs ≤ M := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [h y (by simp), ih (fun x hx => h x (by simp [hx]))]

/-! ## Length -/

@[simps] def lengthF (t : Ty) (i : ℕ) : FnSig (.list t) .nat where
  idx := i
  den xs := xs.length
  cost xs := 30 * (xs.length + 1) * (xs.length.size + 1)
  depth xs := 2 * xs.length + 2
  msize xs := 4 * xs.length.size + 10

def lengthBody (t : Ty) (is i : ℕ) : Tm [.list t] .nat :=
  .lcase v0 .zero (.app (succF is) (.app (lengthF t i) v1))

theorem length_valid {t : Ty} {is i : ℕ} (hs : ∀ n, (succF is).ValidAt P n)
    (hP : P[i]? = some (lengthBody t is i).compile) : ∀ xs, (lengthF t i).ValidAt P xs := by
  refine FnSig.valid_of_body _ _ hP (fun xs => xs.length) ?_
  rintro (_ | ⟨x, xs⟩) ih
  · constructor <;> tm_auto [lengthBody]
  · have hih := ih xs (by simp)
    have h1 := size_mono ((show xs.length ≤ xs.length + 1 by omega))
    have h2 := size_le_self xs.length
    constructor
    · tm_auto [lengthBody, hs, hih]
    · tm_auto [lengthBody, hs, hih]
    · tm_unfold [lengthBody]
      nlinarith [Nat.mul_le_mul_left (xs.length + 1) h1]
    · tm_auto [lengthBody, hs, hih]
    · tm_auto [lengthBody, hs, hih]

/-! ## Append and reverse -/

@[simps] def appendF (t : Ty) (i : ℕ) : FnSig (.prod (.list t) (.list t)) (.list t) where
  idx := i
  den x := x.1 ++ x.2
  cost x := 15 * x.1.length + 15
  depth x := x.1.length + 1
  msize x := (Ty.enc (.prod (.list t) (.list t)) x).size

def appendBody (t : Ty) (i : ℕ) : Tm [.prod (.list t) (.list t)] (.list t) :=
  .lcase (.fst v0) (.snd v0) (.lcons v0 (.app (appendF t i) (.pair v1 (.snd v2))))

theorem append_valid {t : Ty} {i : ℕ} (hP : P[i]? = some (appendBody t i).compile) :
    ∀ x, (appendF t i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.1.length) ?_
  rintro ⟨(_ | ⟨x, xs⟩), ys⟩ ih
  · constructor <;> tm_auto [appendBody]
  · have hih := ih (xs, ys) (by simp)
    have := Ty.sz_list_append t xs ys
    constructor <;> tm_auto [appendBody, hih]

/-- `revApp (xs, acc) = xs.reverse ++ acc`. -/
@[simps] def revAppF (t : Ty) (i : ℕ) : FnSig (.prod (.list t) (.list t)) (.list t) where
  idx := i
  den x := x.1.reverse ++ x.2
  cost x := 15 * x.1.length + 15
  depth x := x.1.length + 1
  msize x := (Ty.enc (.prod (.list t) (.list t)) x).size

def revAppBody (t : Ty) (i : ℕ) : Tm [.prod (.list t) (.list t)] (.list t) :=
  .lcase (.fst v0) (.snd v0) (.app (revAppF t i) (.pair v1 (.lcons v0 (.snd v2))))

theorem revApp_valid {t : Ty} {i : ℕ} (hP : P[i]? = some (revAppBody t i).compile) :
    ∀ x, (revAppF t i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.1.length) ?_
  rintro ⟨(_ | ⟨x, xs⟩), ys⟩ ih
  · constructor <;> tm_auto [revAppBody]
  · have hih := ih (xs, x :: ys) (by simp)
    constructor <;> tm_auto [revAppBody, hih]

@[simps] def reverseF (t : Ty) (i : ℕ) : FnSig (.list t) (.list t) where
  idx := i
  den xs := xs.reverse
  cost xs := 15 * xs.length + 25
  depth xs := xs.length + 2
  msize xs := (Ty.enc (.list t) xs).size + 2

def reverseBody (t : Ty) (ir : ℕ) : Tm [.list t] (.list t) :=
  .app (revAppF t ir) (.pair v0 .lnil)

theorem reverse_valid {t : Ty} {ir i : ℕ} (hr : ∀ x, (revAppF t ir).ValidAt P x)
    (hP : P[i]? = some (reverseBody t ir).compile) : ∀ xs, (reverseF t i).ValidAt P xs := by
  refine FnSig.valid_of_body_nonrec _ _ hP fun xs => ?_
  constructor <;> tm_auto [reverseBody, hr]

/-! ## Map, filter, flatMap -/

@[simps] def mapF {a b : Ty} (F : FnSig a b) (i : ℕ) : FnSig (.list a) (.list b) where
  idx := i
  den xs := xs.map F.den
  cost xs := (xs.map (fun x => F.cost x + 10)).sum + 10
  depth xs := xs.length + 1 + maxOf F.depth xs
  msize xs := max (Ty.enc (.list b) (xs.map F.den)).size (maxOf F.msize xs)

def mapBody {a b : Ty} (F : FnSig a b) (i : ℕ) : Tm [.list a] (.list b) :=
  .lcase v0 .lnil (.lcons (.app F v0) (.app (mapF F i) v1))

theorem map_valid {a b : Ty} {F : FnSig a b} {i : ℕ}
    (hP : P[i]? = some (mapBody F i).compile) :
    ∀ xs, (∀ x ∈ xs, F.ValidAt P x) → (mapF F i).ValidAt P xs := by
  refine FnSig.valid_of_body' _ _ hP (fun (xs : List _) => xs.length) _ ?_
  rintro (_ | ⟨x, xs⟩) hF ih
  · constructor <;> tm_auto [mapBody]
  · have hih := ih xs (by simp) (fun y hy => hF y (by simp [hy]))
    have hx := hF x (by simp)
    constructor <;> tm_auto [mapBody, hih, hx]

@[simps] def filterF {a : Ty} (F : FnSig a .bool) (i : ℕ) : FnSig (.list a) (.list a) where
  idx := i
  den xs := xs.filter F.den
  cost xs := (xs.map (fun x => F.cost x + 12)).sum + 10
  depth xs := xs.length + 1 + maxOf F.depth xs
  msize xs := max (Ty.enc (.list a) xs).size (maxOf F.msize xs)

def filterBody {a : Ty} (F : FnSig a .bool) (i : ℕ) : Tm [.list a] (.list a) :=
  .lcase v0 .lnil (.letE (.app (filterF F i) v1) (.ite (.app F v1) (.lcons v1 v0) v0))

theorem filter_valid {a : Ty} {F : FnSig a .bool} {i : ℕ}
    (hP : P[i]? = some (filterBody F i).compile) :
    ∀ xs, (∀ x ∈ xs, F.ValidAt P x) → (filterF F i).ValidAt P xs := by
  refine FnSig.valid_of_body' _ _ hP (fun (xs : List _) => xs.length) _ ?_
  rintro (_ | ⟨x, xs⟩) hF ih
  · constructor <;> tm_auto [filterBody]
  · have hih := ih xs (by simp) (fun y hy => hF y (by simp [hy]))
    have hx := hF x (by simp)
    have hsub := Ty.sz_sublist a (List.filter_sublist (p := F.den) (l := xs))
    cases hfx : F.den x <;> constructor <;> tm_auto [filterBody, hih, hx, hfx, List.filter_cons]

@[simps] def flatMapF {a b : Ty} (F : FnSig a (.list b)) (i : ℕ) : FnSig (.list a) (.list b) where
  idx := i
  den xs := xs.flatMap F.den
  cost xs := (xs.map (fun x => F.cost x + 15 * (F.den x).length + 30)).sum + 10
  depth xs := xs.length + 1 + maxOf (fun x => F.depth x + (F.den x).length + 1) xs
  msize xs := max ((Ty.enc (.list b) (xs.flatMap F.den)).size + 2) (maxOf F.msize xs)

def flatMapBody {a b : Ty} (F : FnSig a (.list b)) (iapp i : ℕ) : Tm [.list a] (.list b) :=
  .lcase v0 .lnil (.app (appendF b iapp) (.pair (.app F v0) (.app (flatMapF F i) v1)))

theorem flatMap_valid {a b : Ty} {F : FnSig a (.list b)} {iapp i : ℕ}
    (happ : ∀ x, (appendF b iapp).ValidAt P x)
    (hP : P[i]? = some (flatMapBody F iapp i).compile) :
    ∀ xs, (∀ x ∈ xs, F.ValidAt P x) → (flatMapF F i).ValidAt P xs := by
  refine FnSig.valid_of_body' _ _ hP (fun (xs : List _) => xs.length) _ ?_
  rintro (_ | ⟨x, xs⟩) hF ih
  · constructor <;> tm_auto [flatMapBody]
  · have hih := ih xs (by simp) (fun y hy => hF y (by simp [hy]))
    have hx := hF x (by simp)
    have hsz := Ty.sz_list_append b (F.den x) (xs.flatMap F.den)
    have hpos := Ty.sz_pos (.list b) (F.den x)
    constructor <;> tm_auto [flatMapBody, hih, hx, happ]

/-! ## Folds -/

section Folds
variable {a b : Ty}

def foldrDen (F : FnSig (.prod a b) b) (xs : List a.den) (z : b.den) : b.den :=
  xs.foldr (fun x acc => F.den (x, acc)) z

@[simp] theorem foldrDen_nil (F : FnSig (.prod a b) b) (z : b.den) : foldrDen F [] z = z := rfl
@[simp] theorem foldrDen_cons (F : FnSig (.prod a b) b) (x : a.den) (xs : List a.den)
    (z : b.den) : foldrDen F (x :: xs) z = F.den (x, foldrDen F xs z) := rfl

def foldrCost (F : FnSig (.prod a b) b) : List a.den → b.den → ℕ
  | [], _ => 10
  | x :: xs, z => foldrCost F xs z + F.cost (x, foldrDen F xs z) + 12

def foldrDepth (F : FnSig (.prod a b) b) : List a.den → b.den → ℕ
  | [], _ => 1
  | x :: xs, z => max (foldrDepth F xs z + 1) (F.depth (x, foldrDen F xs z) + 1)

def foldrMsize (F : FnSig (.prod a b) b) : List a.den → b.den → ℕ
  | [], _ => 0
  | x :: xs, z => max (foldrMsize F xs z) (max (F.msize (x, foldrDen F xs z))
      ((Ty.enc (.prod (.list a) b) (xs, z)).size +
        (Ty.enc (.prod a b) (x, foldrDen F xs z)).size))

/-- The callee's contract at every step actually taken by `foldr`. -/
def FoldrOK (P : Program) (F : FnSig (.prod a b) b) : List a.den → b.den → Prop
  | [], _ => True
  | x :: xs, z => FoldrOK P F xs z ∧ F.ValidAt P (x, foldrDen F xs z)

attribute [simp] foldrCost foldrDepth foldrMsize FoldrOK

/-- `foldr (xs, z) = xs.foldr (fun x acc => F (x, acc)) z`. -/
@[simps] def foldrF (F : FnSig (.prod a b) b) (i : ℕ) : FnSig (.prod (.list a) b) b where
  idx := i
  den p := foldrDen F p.1 p.2
  cost p := foldrCost F p.1 p.2
  depth p := foldrDepth F p.1 p.2
  msize p := foldrMsize F p.1 p.2

def foldrBody (F : FnSig (.prod a b) b) (i : ℕ) : Tm [.prod (.list a) b] b :=
  .lcase (.fst v0) (.snd v0) (.app F (.pair v0 (.app (foldrF F i) (.pair v1 (.snd v2)))))

theorem foldr_valid {F : FnSig (.prod a b) b} {i : ℕ}
    (hP : P[i]? = some (foldrBody F i).compile) :
    ∀ p, FoldrOK P F p.1 p.2 → (foldrF F i).ValidAt P p := by
  refine FnSig.valid_of_body' _ _ hP (fun (p : List a.den × b.den) => p.1.length) _ ?_
  rintro ⟨(_ | ⟨x, xs⟩), z⟩ hok ih
  · constructor <;> tm_auto [foldrBody]
  · have hih := ih (xs, z) (by simp) hok.1
    have hx := hok.2
    constructor <;> tm_auto [foldrBody, hih, hx]

/-- Closed-form bounds for `foldr` from an invariant `S` of the accumulator. -/
theorem foldr_bounds (F : FnSig (.prod a b) b) (S : b.den → Prop) (K D M : ℕ)
    (xs : List a.den) (z : b.den) (hz : S z) (hzM : (b.enc z).size ≤ M)
    (hS : ∀ x ∈ xs, ∀ acc, S acc → (b.enc acc).size ≤ M → S (F.den (x, acc)) ∧
      (b.enc (F.den (x, acc))).size ≤ M ∧
      F.cost (x, acc) ≤ K ∧ F.depth (x, acc) ≤ D ∧ F.msize (x, acc) ≤ M) :
    S (foldrDen F xs z) ∧ (b.enc (foldrDen F xs z)).size ≤ M ∧
      foldrCost F xs z ≤ (K + 12) * xs.length + 10 ∧
      foldrDepth F xs z ≤ xs.length + D + 1 ∧
      foldrMsize F xs z ≤ 2 * (Ty.enc (.list a) xs).size + 2 * M + 2 := by
  induction xs with
  | nil => simp [hz, hzM]
  | cons x xs ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (fun y hy => hS y (by simp [hy]))
    obtain ⟨g1, g2, g3, g4, g5⟩ := hS x (by simp) _ h1 h2
    refine ⟨g1, g2, ?_, ?_, ?_⟩
    · simp only [foldrCost, List.length_cons]; nlinarith
    · simp only [foldrDepth, List.length_cons]; omega
    · simp only [foldrMsize, Ty.enc_prod, Val.size_cons, Ty.sz_list_cons, max_le_iff]
      refine ⟨by omega, by omega, ?_⟩
      have := Ty.sz_list_cons a x xs
      omega

theorem foldrOK_of_inv (F : FnSig (.prod a b) b) (S : b.den → Prop) (xs : List a.den)
    (z : b.den) (hz : S z) (hS : ∀ x ∈ xs, ∀ acc, S acc → S (F.den (x, acc)))
    (hV : ∀ x ∈ xs, ∀ acc, S acc → F.ValidAt P (x, acc)) : FoldrOK P F xs z := by
  have key : ∀ ys : List a.den, (∀ y ∈ ys, y ∈ xs) → S (foldrDen F ys z) ∧ FoldrOK P F ys z := by
    intro ys
    induction ys with
    | nil => intro _; simp [hz]
    | cons y ys ih =>
      intro hy
      obtain ⟨h1, h2⟩ := ih (fun w hw => hy w (by simp [hw]))
      exact ⟨hS y (hy y (by simp)) _ h1, h2, hV y (hy y (by simp)) _ h1⟩
  exact (key xs (fun _ h => h)).2

def foldlDen (F : FnSig (.prod b a) b) (z : b.den) (xs : List a.den) : b.den :=
  xs.foldl (fun acc x => F.den (acc, x)) z

@[simp] theorem foldlDen_nil (F : FnSig (.prod b a) b) (z : b.den) : foldlDen F z [] = z := rfl
@[simp] theorem foldlDen_cons (F : FnSig (.prod b a) b) (z : b.den) (x : a.den)
    (xs : List a.den) : foldlDen F z (x :: xs) = foldlDen F (F.den (z, x)) xs := rfl

def foldlCost (F : FnSig (.prod b a) b) : b.den → List a.den → ℕ
  | _, [] => 10
  | z, x :: xs => F.cost (z, x) + foldlCost F (F.den (z, x)) xs + 12

def foldlDepth (F : FnSig (.prod b a) b) : b.den → List a.den → ℕ
  | _, [] => 1
  | z, x :: xs => max (F.depth (z, x) + 1) (foldlDepth F (F.den (z, x)) xs + 1)

def foldlMsize (F : FnSig (.prod b a) b) : b.den → List a.den → ℕ
  | _, [] => 0
  | z, x :: xs => max (foldlMsize F (F.den (z, x)) xs) (max (F.msize (z, x))
      ((Ty.enc (.prod b a) (z, x)).size + (Ty.enc (.prod b (.list a)) (F.den (z, x), xs)).size))

/-- The callee's contract at every step actually taken by `foldl`. -/
def FoldlOK (P : Program) (F : FnSig (.prod b a) b) : b.den → List a.den → Prop
  | _, [] => True
  | z, x :: xs => F.ValidAt P (z, x) ∧ FoldlOK P F (F.den (z, x)) xs

attribute [simp] foldlCost foldlDepth foldlMsize FoldlOK

/-- `foldl (z, xs) = xs.foldl (fun acc x => F (acc, x)) z`. -/
@[simps] def foldlF (F : FnSig (.prod b a) b) (i : ℕ) : FnSig (.prod b (.list a)) b where
  idx := i
  den p := foldlDen F p.1 p.2
  cost p := foldlCost F p.1 p.2
  depth p := foldlDepth F p.1 p.2
  msize p := foldlMsize F p.1 p.2

def foldlBody (F : FnSig (.prod b a) b) (i : ℕ) : Tm [.prod b (.list a)] b :=
  .lcase (.snd v0) (.fst v0) (.app (foldlF F i) (.pair (.app F (.pair (.fst v2) v0)) v1))

theorem foldl_valid {F : FnSig (.prod b a) b} {i : ℕ}
    (hP : P[i]? = some (foldlBody F i).compile) :
    ∀ p, FoldlOK P F p.1 p.2 → (foldlF F i).ValidAt P p := by
  refine FnSig.valid_of_body' _ _ hP (fun (p : b.den × List a.den) => p.2.length) _ ?_
  rintro ⟨z, (_ | ⟨x, xs⟩)⟩ hok ih
  · constructor <;> tm_auto [foldlBody]
  · have hih := ih (F.den (z, x), xs) (by simp) hok.2
    have hx := hok.1
    constructor <;> tm_auto [foldlBody, hih, hx]

/-- Closed-form bounds for `foldl` from an invariant `S` of the accumulator. -/
theorem foldl_bounds (F : FnSig (.prod b a) b) (S : b.den → Prop) (K D M : ℕ)
    (xs : List a.den) (z : b.den) (hz : S z) (hzM : (b.enc z).size ≤ M)
    (hS : ∀ x ∈ xs, ∀ acc, S acc → (b.enc acc).size ≤ M → S (F.den (acc, x)) ∧
      (b.enc (F.den (acc, x))).size ≤ M ∧
      F.cost (acc, x) ≤ K ∧ F.depth (acc, x) ≤ D ∧ F.msize (acc, x) ≤ M) :
    S (foldlDen F z xs) ∧ (b.enc (foldlDen F z xs)).size ≤ M ∧
      foldlCost F z xs ≤ (K + 12) * xs.length + 10 ∧
      foldlDepth F z xs ≤ xs.length + D + 1 ∧
      foldlMsize F z xs ≤ 2 * (Ty.enc (.list a) xs).size + 2 * M + 2 := by
  induction xs generalizing z with
  | nil => simp [hz, hzM]
  | cons x xs ih =>
    obtain ⟨g1, g2, g3, g4, g5⟩ := hS x (by simp) z hz hzM
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (F.den (z, x)) g1 g2 (fun y hy => hS y (by simp [hy]))
    refine ⟨h1, h2, ?_, ?_, ?_⟩
    · simp only [foldlCost, List.length_cons]; nlinarith
    · simp only [foldlDepth, List.length_cons]; omega
    · simp only [foldlMsize, Ty.enc_prod, Val.size_cons, Ty.sz_list_cons, max_le_iff]
      refine ⟨by have := Ty.sz_list_cons a x xs; omega, by omega, ?_⟩
      have := Ty.sz_list_cons a x xs
      omega

theorem foldlOK_of_inv (F : FnSig (.prod b a) b) (S : b.den → Prop) (xs : List a.den)
    (z : b.den) (hz : S z) (hS : ∀ x ∈ xs, ∀ acc, S acc → S (F.den (acc, x)))
    (hV : ∀ x ∈ xs, ∀ acc, S acc → F.ValidAt P (acc, x)) : FoldlOK P F z xs := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
    exact ⟨hV x (by simp) z hz, ih _ (hS x (by simp) z hz) (fun y hy => hS y (by simp [hy]))
      (fun y hy => hV y (by simp [hy]))⟩

end Folds

/-! ## Ranges and replication -/

/-- `rangeFrom (k, n) = List.range' k n = [k, …, k + n - 1]`. -/
@[simps] def rangeFromF (i : ℕ) : FnSig (.prod .nat .nat) (.list .nat) where
  idx := i
  den x := List.range' x.1 x.2
  cost x := 60 * (x.2 + 1) * ((x.1 + x.2).size + 1)
  depth x := x.2 + (x.1 + x.2).size + 2
  msize x := (Ty.enc (.list .nat) (List.range' x.1 x.2)).size + 8 * (x.1 + x.2).size + 20

def rangeFromBody (is ip i : ℕ) : Tm [.prod .nat .nat] (.list .nat) :=
  .ncase (.snd v0) .lnil
    (.lcons (.fst v2)
      (.app (rangeFromF i) (.pair (.app (succF is) (.fst v2)) (.app (predF ip) (.snd v2)))))

theorem rangeFrom_valid {is ip i : ℕ} (hs : ∀ n, (succF is).ValidAt P n)
    (hp : ∀ n, (predF ip).ValidAt P n) (hP : P[i]? = some (rangeFromBody is ip i).compile) :
    ∀ x, (rangeFromF i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.2) ?_
  rintro ⟨(k : ℕ), (n : ℕ)⟩ ih
  by_cases hn : n = 0
  · subst hn; constructor <;> tm_auto [rangeFromBody]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hih := ih (k + 1, m) (by simp)
  have hkm : k + 1 + m = k + (m + 1) := by omega
  have h1 := size_mono (show k ≤ k + (m + 1) by omega)
  have h2 := size_mono (show m + 1 ≤ k + (m + 1) by omega)
  have h3 : 1 ≤ (k + (m + 1)).size := size_pos_of_ne (by omega)
  have h4 := size_mono (show m ≤ m + 1 by omega)
  constructor
  · tm_auto [rangeFromBody, hs, hp, hih]
  · tm_auto [rangeFromBody, hs, hp, hih, List.range'_succ]
  · tm_unfold [rangeFromBody, hkm]
    nlinarith
  · tm_auto [rangeFromBody, hs, hp, hih, hkm]
  · tm_unfold [rangeFromBody, hkm, List.range'_succ]
    size_bounds
    omega

theorem sz_range'_le (k n : ℕ) :
    (Ty.enc (.list .nat) (List.range' k n)).size ≤ n * (4 * (k + n).size + 2) + 1 := by
  have h := Ty.sz_list_le .nat (List.range' k n) (4 * (k + n).size + 1) (by
    intro (x : ℕ) hx
    rw [List.mem_range'_1] at hx
    have h1 := Ty.sz_nat_le x
    have h2 := size_mono (show x ≤ k + n by omega)
    simp only [Ty.enc_nat] at h1 ⊢
    omega)
  simpa using h

@[simps] def rangeF (i : ℕ) : FnSig .nat (.list .nat) where
  idx := i
  den n := List.range n
  cost n := 60 * (n + 1) * (n.size + 1) + 10
  depth n := n + n.size + 3
  msize n := (Ty.enc (.list .nat) (List.range n)).size + 8 * n.size + 20

def rangeBody (irf : ℕ) : Tm [.nat] (.list .nat) := .app (rangeFromF irf) (.pair .zero v0)

theorem range_valid {irf i : ℕ} (hr : ∀ x, (rangeFromF irf).ValidAt P x)
    (hP : P[i]? = some (rangeBody irf).compile) : ∀ n, (rangeF i).ValidAt P n := by
  refine FnSig.valid_of_body_nonrec _ _ hP fun (n : ℕ) => ?_
  constructor <;> tm_auto [rangeBody, hr, List.range_eq_range']

/-- `replicate (n, x) = List.replicate n x`. -/
@[simps] def replicateF (t : Ty) (i : ℕ) : FnSig (.prod .nat t) (.list t) where
  idx := i
  den x := List.replicate x.1 x.2
  cost x := 40 * (x.1 + 1) * (x.1.size + 1)
  depth x := x.1 + x.1.size + 2
  msize x := (Ty.enc (.list t) (List.replicate x.1 x.2)).size + (t.enc x.2).size +
    4 * x.1.size + 12

def replicateBody (t : Ty) (ip i : ℕ) : Tm [.prod .nat t] (.list t) :=
  .ncase (.fst v0) .lnil
    (.lcons (.snd v2) (.app (replicateF t i) (.pair (.app (predF ip) (.fst v2)) (.snd v2))))

theorem replicate_valid {t : Ty} {ip i : ℕ} (hp : ∀ n, (predF ip).ValidAt P n)
    (hP : P[i]? = some (replicateBody t ip i).compile) : ∀ x, (replicateF t i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.1) ?_
  rintro ⟨(n : ℕ), x⟩ ih
  by_cases hn : n = 0
  · subst hn; constructor <;> tm_auto [replicateBody]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hih := ih (m, x) (by simp)
  have h1 := size_mono ((show m ≤ m + 1 by omega))
  have h3 : 1 ≤ (m + 1).size := size_pos_of_ne (by omega)
  constructor
  · tm_auto [replicateBody, hp, hih]
  · tm_auto [replicateBody, hp, hih, List.replicate_succ]
  · tm_unfold [replicateBody]
    nlinarith [Nat.mul_le_mul_left (m + 1) h1]
  · tm_auto [replicateBody, hp, hih]
  · tm_unfold [replicateBody, List.replicate_succ]
    size_bounds
    omega

/-! ## Indexing, take, drop -/

/-- `getD (xs, n, d) = xs.getD n d`. -/
@[simps] def getDF (t : Ty) (i : ℕ) : FnSig (.prod (.list t) (.prod .nat t)) t where
  idx := i
  den x := x.1.getD x.2.1 x.2.2
  cost x := 50 * (x.1.length + 1) * (x.2.1.size + 1)
  depth x := x.1.length + x.2.1.size + 2
  msize x := (Ty.enc (.list t) x.1).size + (t.enc x.2.2).size + 8 * x.2.1.size + 20

def getDBody (t : Ty) (ip i : ℕ) : Tm [.prod (.list t) (.prod .nat t)] t :=
  .lcase (.fst v0) (.snd (.snd v0))
    (.ncase (.fst (.snd v2)) v0
      (.app (getDF t i) (.pair v3 (.pair (.app (predF ip) (.fst (.snd v4))) (.snd (.snd v4))))))

theorem getD_valid {t : Ty} {ip i : ℕ} (hp : ∀ n, (predF ip).ValidAt P n)
    (hP : P[i]? = some (getDBody t ip i).compile) : ∀ x, (getDF t i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.1.length) ?_
  rintro ⟨(_ | ⟨y, ys⟩), (n : ℕ), d⟩ ih
  · constructor <;> tm_auto [getDBody]
  by_cases hn : n = 0
  · subst hn; constructor <;> tm_auto [getDBody]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hih := ih (ys, m, d) (by simp)
  have h1 := size_mono ((show m ≤ m + 1 by omega))
  have h3 : 1 ≤ (m + 1).size := size_pos_of_ne (by omega)
  constructor
  · tm_auto [getDBody, hp, hih]
  · tm_auto [getDBody, hp, hih]
  · tm_unfold [getDBody]
    nlinarith [Nat.mul_le_mul_left (ys.length + 1) h1]
  · tm_auto [getDBody, hp, hih]
  · tm_auto [getDBody, hp, hih]

/-- `take (n, xs) = xs.take n`. -/
@[simps] def takeF (t : Ty) (i : ℕ) : FnSig (.prod .nat (.list t)) (.list t) where
  idx := i
  den x := x.2.take x.1
  cost x := 50 * (x.2.length + 1) * (x.1.size + 1)
  depth x := x.2.length + x.1.size + 2
  msize x := (Ty.enc (.list t) x.2).size + 8 * x.1.size + 20

def takeBody (t : Ty) (ip i : ℕ) : Tm [.prod .nat (.list t)] (.list t) :=
  .ncase (.fst v0) .lnil
    (.lcase (.snd v2) .lnil
      (.lcons v0 (.app (takeF t i) (.pair (.app (predF ip) (.fst v4)) v1))))

theorem take_valid {t : Ty} {ip i : ℕ} (hp : ∀ n, (predF ip).ValidAt P n)
    (hP : P[i]? = some (takeBody t ip i).compile) : ∀ x, (takeF t i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.2.length) ?_
  rintro ⟨(n : ℕ), (_ | ⟨y, ys⟩)⟩ ih
  · by_cases hn : n = 0
    · subst hn; constructor <;> tm_auto [takeBody]
    · constructor <;> tm_auto [takeBody, hn]
  by_cases hn : n = 0
  · subst hn; constructor <;> tm_auto [takeBody]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hih := ih (m, ys) (by simp)
  have h1 := size_mono ((show m ≤ m + 1 by omega))
  have h3 : 1 ≤ (m + 1).size := size_pos_of_ne (by omega)
  have hsub := Ty.sz_sublist t (List.take_sublist m ys)
  constructor
  · tm_auto [takeBody, hp, hih]
  · tm_auto [takeBody, hp, hih]
  · tm_unfold [takeBody]
    nlinarith [Nat.mul_le_mul_left (ys.length + 1) h1]
  · tm_auto [takeBody, hp, hih]
  · tm_auto [takeBody, hp, hih]

/-- `drop (n, xs) = xs.drop n`. -/
@[simps] def dropF (t : Ty) (i : ℕ) : FnSig (.prod .nat (.list t)) (.list t) where
  idx := i
  den x := x.2.drop x.1
  cost x := 50 * (x.2.length + 1) * (x.1.size + 1)
  depth x := x.2.length + x.1.size + 2
  msize x := (Ty.enc (.list t) x.2).size + 8 * x.1.size + 20

def dropBody (t : Ty) (ip i : ℕ) : Tm [.prod .nat (.list t)] (.list t) :=
  .ncase (.fst v0) (.snd v0)
    (.lcase (.snd v2) .lnil
      (.app (dropF t i) (.pair (.app (predF ip) (.fst v4)) v1)))

theorem drop_valid {t : Ty} {ip i : ℕ} (hp : ∀ n, (predF ip).ValidAt P n)
    (hP : P[i]? = some (dropBody t ip i).compile) : ∀ x, (dropF t i).ValidAt P x := by
  refine FnSig.valid_of_body _ _ hP (fun x => x.2.length) ?_
  rintro ⟨(n : ℕ), (_ | ⟨y, ys⟩)⟩ ih
  · by_cases hn : n = 0
    · subst hn; constructor <;> tm_auto [dropBody]
    · constructor <;> tm_auto [dropBody, hn]
  by_cases hn : n = 0
  · subst hn; constructor <;> tm_auto [dropBody]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hih := ih (m, ys) (by simp)
  have h1 := size_mono ((show m ≤ m + 1 by omega))
  have h3 : 1 ≤ (m + 1).size := size_pos_of_ne (by omega)
  have hsub := Ty.sz_sublist t (List.drop_sublist m ys)
  constructor
  · tm_auto [dropBody, hp, hih]
  · tm_auto [dropBody, hp, hih]
  · tm_unfold [dropBody]
    nlinarith [Nat.mul_le_mul_left (ys.length + 1) h1]
  · tm_auto [dropBody, hp, hih]
  · tm_auto [dropBody, hp, hih]

end QecReliability.FL.Lib
