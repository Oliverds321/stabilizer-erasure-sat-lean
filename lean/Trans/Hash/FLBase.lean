import Trans.Hash.Plain
import FL.Lib.List

/-!
# Trans.Hash.FLBase: types, exact signatures, map with an environment

* Type abbreviations of the plain representation: `TGate`, `TProg`, `TTab` (a `tableWire`
  environment `(table, k, base)`), `TRow` (a seed row).
* `exactSig i body den`: a non-recursive function whose bounds are exactly those of its body
  (`cost = body.cost + 2`, …); `exactSig_valid` reduces its contract to the calls and the
  meaning. Closed-form bounds are separate lemmas.
* `mapEnvF F i`: `(c, xs) ↦ xs.map (fun x => F (c, x))` (map with a shared environment `c`),
  `mapEnv_valid`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Hash
open QecReliability.FL QecReliability.FL.Lib Tm NatSize

abbrev TGate : Ty := .prod .bool (.prod .bool (.prod .nat .nat))
abbrev TProg : Ty := .prod (.list TGate) (.list .nat)
abbrev TTab : Ty := .prod (.list .nat) (.prod .nat .nat)
abbrev TRow : Ty := .prod (.list .bool) .bool

/-! ## Exact signatures -/

/-- A non-recursive function with the exact bounds of its body. -/
def exactSig {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den) : FnSig a b where
  idx := i
  den := den
  cost x := body.cost (Env.one x) + 2
  depth x := body.depth (Env.one x) + 1
  msize x := body.msize (Env.one x)

@[simp] theorem exactSig_idx {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den) :
    (exactSig i body den).idx = i := rfl
@[simp] theorem exactSig_den {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den)
    (x : a.den) : (exactSig i body den).den x = den x := rfl
theorem exactSig_cost {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den) (x : a.den) :
    (exactSig i body den).cost x = body.cost (Env.one x) + 2 := rfl
theorem exactSig_depth {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den) (x : a.den) :
    (exactSig i body den).depth x = body.depth (Env.one x) + 1 := rfl
theorem exactSig_msize {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den) (x : a.den) :
    (exactSig i body den).msize x = body.msize (Env.one x) := rfl

theorem exactSig_valid {a b : Ty} {P : Program} {i : ℕ} {body : Tm [a] b}
    {den : a.den → b.den} (hP : P[i]? = some body.compile) (Q : a.den → Prop)
    (hcalls : ∀ x, Q x → body.CallsOK P (Env.one x))
    (hden : ∀ x, Q x → body.den (Env.one x) = den x) :
    ∀ x, Q x → (exactSig i body den).ValidAt P x := fun x hx =>
  FnSig.validAt_of_bodyOK hP ⟨hcalls x hx, hden x hx, le_refl _, le_refl _, le_refl _⟩

/-! ## Map with an environment -/

variable {P : Program}

@[simps] def mapEnvF {e a b : Ty} (F : FnSig (.prod e a) b) (i : ℕ) :
    FnSig (.prod e (.list a)) (.list b) where
  idx := i
  den p := p.2.map (fun x => F.den (p.1, x))
  cost p := (p.2.map (fun x => F.cost (p.1, x) + 16)).sum + 10
  depth p := p.2.length + 1 + maxOf (fun x => F.depth (p.1, x)) p.2
  msize p := max (max (Ty.enc (.list b) (p.2.map (fun x => F.den (p.1, x)))).size
    (maxOf (fun x => F.msize (p.1, x)) p.2)) (Ty.enc (.prod e (.list a)) p).size

def mapEnvBody {e a b : Ty} (F : FnSig (.prod e a) b) (i : ℕ) :
    Tm [.prod e (.list a)] (.list b) :=
  .lcase (.snd v0) .lnil
    (.lcons (.app F (.pair (.fst v2) v0)) (.app (mapEnvF F i) (.pair (.fst v2) v1)))

theorem mapEnv_valid {e a b : Ty} {F : FnSig (.prod e a) b} {i : ℕ}
    (hP : P[i]? = some (mapEnvBody F i).compile) :
    ∀ p : (Ty.prod e (.list a)).den, (∀ x ∈ p.2, F.ValidAt P (p.1, x)) →
      (mapEnvF F i).ValidAt P p := by
  refine FnSig.valid_of_body' _ _ hP (fun (p : (Ty.prod e (.list a)).den) => p.2.length) _ ?_
  rintro ⟨c, (_ | ⟨x, xs⟩)⟩ hF ih
  · constructor <;> tm_auto [mapEnvBody]
  · have hih := ih (c, xs) (by simp) (fun y hy => hF y (by simp [hy]))
    have hx := hF x (by simp)
    have s1 := Ty.sz_pos e c
    have s2 := Ty.sz_pos a x
    constructor
    · tm_auto [mapEnvBody, hih, hx]
    · tm_auto [mapEnvBody, hih, hx]
    · tm_auto [mapEnvBody, hih, hx]
    · tm_auto [mapEnvBody, hih, hx]
    · tm_lean [mapEnvBody, hih, hx, mapEnvF_msize, mapEnvF_den, Ty.enc_list_cons, List.map_cons,
        maxOf_cons, Ty.enc_prod]

end QecReliability.Trans.Hash
