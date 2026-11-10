import Trans.Control.StepP
import Trans.Bounds.SizeCfg

/-!
# Trans.BoundsStep.Base: shared helpers for the per-phase closed forms

All per-phase bounds are stated at an ARBITRARY argument `a : (TArg TX').den` in terms of its
encoded size `S = (Ty.enc (TArg TX') a).size` (bit lengths of every number of `a` are `≤ S`).
Proof recipe: destructure `a` (context `((q,r,B,m),X)`, configuration groups `g0 … g6`, and the
groups/lists a phase reads), `rw [sz_arg7]` and the group shape lemmas, `simp only` the
compositional bound of the body, then `omega` (nested `max` are split with `max_le_iff` first:
`omega` on nested `max` is exponential).
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsStep
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (TR TEnt TKey TPre TOp TG0 TG1 TG2 TG3 TG4 TG5 TG6 TCfg TCtx
  TArg bodySig bodySig_cost bodySig_depth bodySig_msize)
open QecReliability.Trans.Bounds (shape2 shape4 shape5 shape6 shape7 shape8)

/-- The argument size splits into context fields and the seven configuration groups. -/
theorem sz_arg7 {TX' : Ty} (q r B m : ℕ) (X : TX'.den) (g0 : TG0.den) (g1 : TG1.den)
    (g2 : TG2.den) (g3 : TG3.den) (g4 : TG4.den) (g5 : TG5.den) (g6 : TG6.den) :
    (Ty.enc (TArg TX') (((q, r, B, m), X), (g0, g1, g2, g3, g4, g5, g6))).size =
      (Enc.nat q).size + (Enc.nat r).size + (Enc.nat B).size + (Enc.nat m).size +
      (Ty.enc TX' X).size + (Ty.enc TG0 g0).size + (Ty.enc TG1 g1).size +
      (Ty.enc TG2 g2).size + (Ty.enc TG3 g3).size + (Ty.enc TG4 g4).size +
      (Ty.enc TG5 g5).size + (Ty.enc TG6 g6).size + 11 := by
  rw [shape2, shape2, shape4, shape7]
  simp only [Ty.enc_nat]
  omega

/-- Literals below `32`. -/
theorem lit_sz (k : ℕ) (hk : k < 32) : k.size ≤ 5 ∧ (Enc.nat k).size ≤ 21 :=
  ⟨Nat.size_le.mpr (by omega), Trans.Bounds.sz_lt_pow k 5 (by omega)⟩

theorem enc_bitNat_le (b : Bool) (n : ℕ) : (Enc.nat (bitNat b n)).size ≤ (Enc.nat n).size + 4 := by
  rw [Enc.nat_bitNat]
  by_cases hn : n = 0
  · subst hn
    cases b <;> simp [Enc.nat_zero]
  · rw [if_neg hn]
    have := Enc.bool_size b
    simp only [Val.size_cons]
    omega

/-- Bit length is at most the encoded size (restated). -/
theorem bl (n : ℕ) : n.size ≤ (Enc.nat n).size := Control.size_le_enc n

theorem enc_pos (n : ℕ) : 1 ≤ (Enc.nat n).size := Val.size_pos _

/-- Size of a pair of naturals. -/
theorem sz_nn (u v : ℕ) : (Ty.enc (.prod .nat .nat) (u, v)).size =
    (Enc.nat u).size + (Enc.nat v).size + 1 := by
  rw [shape2]; simp only [Ty.enc_nat]

/-- Finish a bound goal after `dsimp`: split `if`s, split `max ≤ _`, then `omega`. -/
macro "fin_le" : tactic => `(tactic| (strip_mdata <;> (try split_ifs) <;>
  (try simp only [max_le_iff, max_self, Enc.nat_one_size, Enc.nat_zero_size, Val.size_cons,
    Nat.zero_le, true_and, and_true]) <;> (try strip_mdata) <;> (repeat' apply And.intro) <;>
    omega))

/-- Normalisation of encoded sizes into the sizes of the leaves (numbers, Booleans, lists, opaque
`X`); all lemmas are `rfl`, so this is a `dsimp`. The `_nat2/_nat/_bool` list lemmas are needed
because `List.nil`/`List.cons` at `ℕ × ℕ` do not match the generic `Ty.enc_list_*`; the
abbreviations `TEnt`/`TR` are unfolded so that `omega` sees one spelling of each atom. -/
syntax "sz_norm" (ppSpace Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sz_norm $[$loc]?) => `(tactic| dsimp only [Ty.enc_prod, Ty.enc_nat, Ty.enc_bool,
      Ty.enc_list_nil, Ty.enc_list_nil_nat2, Ty.enc_list_nil_nat, Ty.enc_list_nil_bool,
      Ty.enc_list_cons, Ty.enc_list_cons_nat2, Ty.enc_list_cons_nat, Ty.enc_list_cons_bool,
      Val.size_cons, Val.size_nil, Enc.bool_false_size, Enc.bool_true_size, Control.TEnt,
      Control.TR] $[$loc]?)

/-- `Ty.enc_prod` restricted to explicit pairs (variables of product type stay atoms). -/
theorem enc_prod_mk (a b : Ty) (u : a.den) (v : b.den) :
    Ty.enc (.prod a b) (u, v) = .cons (a.enc u) (b.enc v) := rfl

/-- Like `sz_norm`, but only explicit tuples are split (`enc_prod_mk`), so group variables
`g1 : TG1.den` keep the single atom `(Ty.enc TG1 g1).size` (far fewer `omega` atoms). -/
syntax "sz_mk" (ppSpace Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| sz_mk $[$loc]?) => `(tactic| dsimp only [enc_prod_mk, Ty.enc_nat, Ty.enc_bool,
      Ty.enc_list_nil, Ty.enc_list_nil_nat2, Ty.enc_list_nil_nat, Ty.enc_list_nil_bool,
      Ty.enc_list_cons, Ty.enc_list_cons_nat2, Ty.enc_list_cons_nat, Ty.enc_list_cons_bool,
      Val.size_cons, Val.size_nil, Enc.bool_false_size, Enc.bool_true_size, Control.TEnt,
      Control.TR] $[$loc]?)

theorem lin_sq (S K K' : ℕ) : K * S + K' ≤ (K + K') * (S + 1) ^ 2 := by
  have h1 : S + 1 ≤ (S + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h2 : 1 ≤ (S + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

end QecReliability.Trans.BoundsStep
