import LatentGateParserFL
import Trans.BoundsRest.InitParse

/-! Measured cost/depth/maximum-value-size of the actual FL gate parser.
These are compiler-facing FL measures, not yet all-tape visited-cell bounds.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ParserFL
open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)
open Trans.BoundsRest

private theorem gateParser_get_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl

private theorem gateParser_get_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

theorem gate_bounds (L : Lib) (h : HIx) (idx : ℕ) {Q : ℕ}
    (bs : List Bool) (hQ : bs.length ≤ Q) :
    (gateF L h idx).cost bs ≤ 2000 * (Q+2)^2 ∧
    (gateF L h idx).depth bs ≤ 30*Q+100 ∧
    (gateF L h idx).msize bs ≤ 500*Q+500 := by
  have hsq : 1 ≤ (Q+2)^2 := by nlinarith
  cases bs with
  | nil =>
    simp [gateF, bodySig_cost, bodySig_depth, bodySig_msize, gateBody,
      defaultGate, gateTm, tm_simp] <;> omega
  | cons u bs =>
    cases bs with
    | nil =>
      simp [gateF, bodySig_cost, bodySig_depth, bodySig_msize, gateBody,
        defaultGate, gateTm, tm_simp] <;> omega
    | cons s bs =>
      have hlen : bs.length ≤ Q := by simp only [List.length_cons] at hQ; omega
      have hs1 := (hdr_suffix bs).length_le
      have hs2 := (hdr_suffix (hdr bs).2).length_le
      obtain ⟨c1,d1,m1⟩ := hdr_le L h (Q:=Q) bs hlen
      obtain ⟨c2,d2,m2⟩ := hdr_le L h (Q:=Q) (hdr bs).2 (by omega)
      have v1 := hdr_val_sz bs
      have v2 := hdr_val_sz (hdr bs).2
      have z1 := sz_bools (hdr bs).2
      have z2 := sz_bools (hdr (hdr bs).2).2
      have z0 := sz_bools ([] : List Bool)
      have n0 := nat_sz_le_self 0
      have n1 := nat_sz_le_self 1
      have bt := Ty.sz_bool_le true
      have bf := Ty.sz_bool_le false
      cases u with
      | false =>
        cases s <;> (
          refine ⟨?_, ?_, ?_⟩
          · dsimp only [gateF, bodySig_cost, gateBody, gateTm, defaultGate, Tm.cost, Tm.den, Env.one, gateParser_get_zero, gateParser_get_succ]
            try simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            rw [hdrF_den]
            simp only [Nat.add_assoc]
            omega
          · dsimp only [gateF, bodySig_depth, gateBody, gateTm, defaultGate, Tm.depth, Tm.den, Env.one, gateParser_get_zero, gateParser_get_succ]
            try simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            rw [hdrF_den]
            omega
          · dsimp only [gateF, bodySig_msize, gateBody, gateTm, defaultGate, Tm.msize, Tm.den, Env.one, gateParser_get_zero, gateParser_get_succ]
            try simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            simp only [hdrF_den, Ty.sz_prod, max_le_iff]
            repeat' apply And.intro
            all_goals omega)
      | true =>
        cases s with
        | false =>
          refine ⟨?_, ?_, ?_⟩
          · dsimp only [gateF, bodySig_cost, gateBody, gateTm, defaultGate, Tm.cost, Tm.den, Env.one, gateParser_get_zero, gateParser_get_succ]
            try simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            simp only [Nat.add_assoc]
            omega
          · dsimp only [gateF, bodySig_depth, gateBody, gateTm, defaultGate, Tm.depth, Tm.den, Env.one, gateParser_get_zero, gateParser_get_succ]
            try simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            omega
          · dsimp only [gateF, bodySig_msize, gateBody, gateTm, defaultGate, Tm.msize, Tm.den, Env.one, gateParser_get_zero, gateParser_get_succ]
            try simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
            simp only [hdrF_den, Ty.sz_prod, max_le_iff]
            repeat' apply And.intro
            all_goals omega
        | true =>
          cases bs with
          | nil =>
            simp [gateF, bodySig_cost, bodySig_depth, bodySig_msize, gateBody,
              defaultGate, gateTm, tm_simp] <;> omega
          | cons b rest =>
            have zr := sz_bools rest
            have hl : rest.length ≤ Q := by simp only [List.length_cons] at hlen; omega
            cases b <;> (
              refine ⟨?_, ?_, ?_⟩
              · dsimp only [gateF, bodySig_cost, gateBody, gateTm, defaultGate, Tm.cost, Tm.den, Env.one, gateParser_get_zero, gateParser_get_succ]
                try simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                simp only [Nat.add_assoc]
                omega
              · dsimp only [gateF, bodySig_depth, gateBody, gateTm, defaultGate, Tm.depth, Tm.den, Env.one, gateParser_get_zero, gateParser_get_succ]
                try simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                omega
              · dsimp only [gateF, bodySig_msize, gateBody, gateTm, defaultGate, Tm.msize, Tm.den, Env.one, gateParser_get_zero, gateParser_get_succ]
                try simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
                simp only [Ty.sz_prod, max_le_iff]
                repeat' apply And.intro
                all_goals omega)

end QecReliability.LatentMachine.ParserFL
