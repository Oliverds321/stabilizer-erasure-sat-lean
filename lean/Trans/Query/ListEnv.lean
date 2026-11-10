import FL.Lib.List

/-!
# Trans.Query.ListEnv: list combinators with a constant environment

`FL/Lib/List.lean` provides `mapF`/`flatMapF` for closed callees. The query transcription
needs the same combinators where the callee also reads a constant environment `c` (a shift,
a word width, …). These are generic and could move to `FL/Lib` later.

* `mapEnvF F i : FnSig (c × list a) (list b)`, `(e, xs) ↦ xs.map (fun x => F (e, x))`;
* `flatMapEnvF F iapp i`, `(e, xs) ↦ xs.flatMap (fun x => F (e, x))`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Query
open QecReliability.FL QecReliability.FL.Lib Tm NatSize

variable {P : Program}

/-! ## map with environment -/

def mapEnvCost {c a b : Ty} (F : FnSig (.prod c a) b) (e : c.den) (xs : List a.den) : ℕ :=
  (xs.map (fun x => F.cost (e, x) + 20)).sum + 10

def mapEnvDepth {c a b : Ty} (F : FnSig (.prod c a) b) (e : c.den) (xs : List a.den) : ℕ :=
  xs.length + 1 + maxOf (fun x => F.depth (e, x)) xs

def mapEnvMsize {c a b : Ty} (F : FnSig (.prod c a) b) (e : c.den) (xs : List a.den) : ℕ :=
  max (max (Ty.enc (.list b) (xs.map (fun x => F.den (e, x)))).size
    (Ty.enc (.prod c (.list a)) (e, xs)).size) (maxOf (fun x => F.msize (e, x)) xs)

@[simp] theorem mapEnvCost_nil {c a b : Ty} (F : FnSig (.prod c a) b) (e : c.den) :
    mapEnvCost F e [] = 10 := rfl
@[simp] theorem mapEnvCost_cons {c a b : Ty} (F : FnSig (.prod c a) b) (e : c.den) (x : a.den)
    (xs : List a.den) : mapEnvCost F e (x :: xs) = F.cost (e, x) + 20 + mapEnvCost F e xs := by
  simp only [mapEnvCost, List.map_cons, List.sum_cons]; omega

@[simps] def mapEnvF {c a b : Ty} (F : FnSig (.prod c a) b) (i : ℕ) :
    FnSig (.prod c (.list a)) (.list b) where
  idx := i
  den p := p.2.map (fun x => F.den (p.1, x))
  cost p := mapEnvCost F p.1 p.2
  depth p := mapEnvDepth F p.1 p.2
  msize p := mapEnvMsize F p.1 p.2

def mapEnvBody {c a b : Ty} (F : FnSig (.prod c a) b) (i : ℕ) : Tm [.prod c (.list a)] (.list b) :=
  .lcase (.snd v0) .lnil
    (.lcons (.app F (.pair (.fst v2) v0)) (.app (mapEnvF F i) (.pair (.fst v2) v1)))

theorem mapEnv_valid {c a b : Ty} {F : FnSig (.prod c a) b} {i : ℕ}
    (hP : P[i]? = some (mapEnvBody F i).compile) :
    ∀ p : (Ty.prod c (.list a)).den, (∀ x ∈ p.2, F.ValidAt P (p.1, x)) →
      (mapEnvF F i).ValidAt P p := by
  refine FnSig.valid_of_body' _ _ hP (fun (p : (Ty.prod c (.list a)).den) => p.2.length) _ ?_
  rintro ⟨e, (_ | ⟨x, xs⟩)⟩ hF ih
  · constructor <;> tm_auto [mapEnvBody, mapEnvMsize, mapEnvDepth]
  · have hih := ih (e, xs) (by simp) (fun y hy => hF y (by simp [hy]))
    have hx := hF x (by simp)
    constructor <;> tm_auto [mapEnvBody, hih, hx, mapEnvMsize, mapEnvDepth]

/-! ## flatMap with environment -/

def flatMapEnvCost {c a b : Ty} (F : FnSig (.prod c a) (.list b)) (e : c.den) (xs : List a.den) : ℕ :=
  (xs.map (fun x => F.cost (e, x) + 15 * (F.den (e, x)).length + 40)).sum + 10

def flatMapEnvDepth {c a b : Ty} (F : FnSig (.prod c a) (.list b)) (e : c.den) (xs : List a.den) : ℕ :=
  xs.length + 1 + maxOf (fun x => F.depth (e, x) + (F.den (e, x)).length + 1) xs

def flatMapEnvMsize {c a b : Ty} (F : FnSig (.prod c a) (.list b)) (e : c.den) (xs : List a.den) : ℕ :=
  max (max ((Ty.enc (.list b) (xs.flatMap (fun x => F.den (e, x)))).size + 2)
    (Ty.enc (.prod c (.list a)) (e, xs)).size) (maxOf (fun x => F.msize (e, x)) xs)

@[simp] theorem flatMapEnvCost_nil {c a b : Ty} (F : FnSig (.prod c a) (.list b)) (e : c.den) :
    flatMapEnvCost F e [] = 10 := rfl
@[simp] theorem flatMapEnvCost_cons {c a b : Ty} (F : FnSig (.prod c a) (.list b)) (e : c.den)
    (x : a.den) (xs : List a.den) :
    flatMapEnvCost F e (x :: xs) =
      F.cost (e, x) + 15 * (F.den (e, x)).length + 40 + flatMapEnvCost F e xs := by
  simp only [flatMapEnvCost, List.map_cons, List.sum_cons]; omega

@[simps] def flatMapEnvF {c a b : Ty} (F : FnSig (.prod c a) (.list b)) (i : ℕ) :
    FnSig (.prod c (.list a)) (.list b) where
  idx := i
  den p := p.2.flatMap (fun x => F.den (p.1, x))
  cost p := flatMapEnvCost F p.1 p.2
  depth p := flatMapEnvDepth F p.1 p.2
  msize p := flatMapEnvMsize F p.1 p.2

def flatMapEnvBody {c a b : Ty} (F : FnSig (.prod c a) (.list b)) (iapp i : ℕ) :
    Tm [.prod c (.list a)] (.list b) :=
  .lcase (.snd v0) .lnil
    (.app (appendF b iapp) (.pair (.app F (.pair (.fst v2) v0))
      (.app (flatMapEnvF F i) (.pair (.fst v2) v1))))

theorem flatMapEnv_valid {c a b : Ty} {F : FnSig (.prod c a) (.list b)} {iapp i : ℕ}
    (happ : ∀ x, (appendF b iapp).ValidAt P x)
    (hP : P[i]? = some (flatMapEnvBody F iapp i).compile) :
    ∀ p : (Ty.prod c (.list a)).den, (∀ x ∈ p.2, F.ValidAt P (p.1, x)) →
      (flatMapEnvF F i).ValidAt P p := by
  refine FnSig.valid_of_body' _ _ hP (fun (p : (Ty.prod c (.list a)).den) => p.2.length) _ ?_
  rintro ⟨e, (_ | ⟨x, xs⟩)⟩ hF ih
  · constructor <;> tm_auto [flatMapEnvBody, flatMapEnvMsize, flatMapEnvDepth]
  · have hih := ih (e, xs) (by simp) (fun y hy => hF y (by simp [hy]))
    have hx := hF x (by simp)
    have hsz := Ty.sz_list_append b (F.den (e, x)) (xs.flatMap (fun y => F.den (e, y)))
    have hpos := Ty.sz_pos (.list b) (F.den (e, x))
    constructor <;> tm_auto [flatMapEnvBody, hih, hx, happ, flatMapEnvMsize, flatMapEnvDepth]

end QecReliability.Trans.Query
