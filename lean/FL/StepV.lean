import FL.Encode

/-!
# The CEK step on encoded states

`stepV Pv st` performs one CEK transition directly on the tree encoding of a state, given the
encoded program `Pv = Program.enc P`. `stepV_enc` shows it commutes with the encoding. The
register-level interpreter only has to implement `stepV` (a fixed tree-to-tree function built
from head/tail/cons and unary-tag tests), which is what makes its correctness proof local.
-/

set_option autoImplicit false

namespace QecReliability.FL

/-- Unary tags as values. -/
abbrev u0 : Val := .nil
abbrev u1 : Val := .cons .nil u0
abbrev u2 : Val := .cons .nil u1
abbrev u3 : Val := .cons .nil u2
abbrev u4 : Val := .cons .nil u3
abbrev u5 : Val := .cons .nil u4
abbrev u6 : Val := .cons .nil u5
abbrev u7 : Val := .cons .nil u6
abbrev u8 : Val := .cons .nil u7

/-- Index an encoded list with a unary index. -/
def nthV : Val → Val → Option Val
  | .cons h _, .nil => some h
  | .cons _ t, .cons _ i => nthV t i
  | .nil, _ => none

theorem nthV_list {α : Type} (f : α → Val) (xs : List α) (i : ℕ) :
    nthV (Enc.list f xs) (Enc.unary i) = (xs[i]?).map f := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp [Enc.list, Enc.unary, nthV, ih]

/-- `ret v k` and `eval e env k` as encoded states. -/
abbrev retV (v k : Val) : Val := .cons u1 (.cons v k)
abbrev evalV (e env k : Val) : Val := .cons u0 (.cons e (.cons env k))
abbrev frameV (j : Val) (x : Val) : Val := .cons j x

/-- One CEK transition on encodings. -/
def stepV (Pv : Val) : Val → Option Val
  -- eval mode
  | .cons .nil (.cons e (.cons env k)) =>
    match e with
    | .cons .nil i => (nthV env i).map (fun v => retV v k)                          -- var
    | .cons (.cons .nil .nil) _ => some (retV .nil k)                               -- nil
    | .cons (.cons .nil (.cons .nil .nil)) (.cons a b) =>                           -- cons
        some (evalV a env (.cons (frameV u0 (.cons b env)) k))
    | .cons (.cons .nil (.cons .nil (.cons .nil .nil))) (.cons s (.cons e₁ e₂)) =>  -- case
        some (evalV s env (.cons (frameV u2 (.cons e₁ (.cons e₂ env))) k))
    | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil)))) (.cons f a) => -- call
        some (evalV a env (.cons (frameV u3 f) k))
    | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil))))) (.cons a b) =>
        some (evalV a env (.cons (frameV u4 (.cons b env)) k))                      -- letE
    | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil))))))
        (.cons s (.cons e₁ e₂)) =>                                                   -- cond
        some (evalV s env (.cons (frameV u5 (.cons e₁ (.cons e₂ env))) k))
    | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil
        (.cons .nil .nil))))))) a =>                                                 -- fst
        some (evalV a env (.cons (frameV u6 .nil) k))
    | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil
        (.cons .nil (.cons .nil .nil)))))))) a =>                                    -- snd
        some (evalV a env (.cons (frameV u7 .nil) k))
    | _ => none
  -- ret mode
  | .cons (.cons .nil .nil) (.cons v k) =>
    match k with
    | .nil => none
    | .cons fr k' =>
      match fr, v with
      | .cons .nil (.cons b env), va => some (evalV b env (.cons (frameV u1 va) k'))  -- consL
      | .cons (.cons .nil .nil) va, vb => some (retV (.cons va vb) k')               -- consR
      | .cons (.cons .nil (.cons .nil .nil)) (.cons e₁ (.cons _ env)), .nil =>        -- caseK nil
          some (evalV e₁ env k')
      | .cons (.cons .nil (.cons .nil .nil)) (.cons _ (.cons e₂ env)), .cons h tl =>  -- caseK cons
          some (evalV e₂ (.cons h (.cons tl env)) k')
      | .cons (.cons .nil (.cons .nil (.cons .nil .nil))) f, va =>                    -- callK
          (nthV Pv f).map (fun body => evalV body (.cons va .nil) k')
      | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil)))) (.cons b env), va =>
          some (evalV b (.cons va env) k')                                           -- letK
      | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil)))))
          (.cons e₁ (.cons _ env)), .nil => some (evalV e₁ env k')                    -- condK nil
      | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil)))))
          (.cons _ (.cons e₂ env)), .cons _ _ => some (evalV e₂ env k')               -- condK cons
      | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil))))))
          _, .cons a _ => some (retV a k')                                           -- fstK
      | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil
          (.cons .nil .nil))))))) _, .cons _ b => some (retV b k')                    -- sndK
      | _, _ => none
  | _ => none

theorem stepV_enc (P : Program) (s : State) :
    stepV (Program.enc P) s.enc = (step P s).map State.enc := by
  rcases s with ⟨e, env, k⟩ | ⟨v, k⟩
  · cases e <;>
      simp [State.enc, Expr.enc, tagged, Enc.unary, stepV, step, envEnc, stackEnc, Enc.list,
        Frame.enc, nthV_list, Option.map_map, Function.comp_def]
  · cases k with
    | nil => simp [State.enc, tagged, Enc.unary, stepV, step, stackEnc, Enc.list]
    | cons fr k =>
      cases fr <;> cases v <;>
        simp [State.enc, Frame.enc, tagged, Enc.unary, stepV, step, envEnc, stackEnc, Enc.list,
          Program.enc, nthV_list, Option.map_map, Function.comp_def]

end QecReliability.FL
