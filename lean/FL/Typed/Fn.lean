import FL.Typed.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# FL.Typed.Fn: global functions defined by typed bodies

A global function `F : FnSig a b` is *implemented* by a body `body : Tm [a] b` stored at
`P[F.idx]`. `FnSig.BodyOK P F body x` collects what has to be checked at one argument `x`:
the calls made by the body are valid, the body means `F.den x`, and its bounds fit `F`'s
bounds (a call costs the body cost `+ 2` and adds `1` to the depth).

* `FnSig.validAt_of_bodyOK`: one argument.
* `FnSig.valid_of_body'`: recursive functions, by strong induction on a measure
  `μ : a.den → ℕ`, restricted to arguments satisfying an invariant `Q` (needed when a
  callee is only valid on some arguments, e.g. `map F` with `F` valid on the list's
  elements).
* `FnSig.valid_of_body`: `Q = True`; `FnSig.valid_of_body_nonrec`: no self-calls.

Note on the argument size: `Eval.var` imposes no size condition, so `ValidAt` does not need
`(a.enc x).size ≤ m` and neither do these theorems. The register-level interpreter wants
every value, the argument included, to fit in `m` (`FL.Computes`); `FnSig.ValidAt.computes`
gives that when `(a.enc x).size ≤ F.msize x`, which all library signatures satisfy
(`*_arg_le_msize` lemmas) or which the caller can add with `max`.
-/

set_option autoImplicit false

/-- Simp set unfolding the typed-term semantics (`Tm.den/cost/depth/msize/CallsOK`,
`Env.get`); used as `simp [tm_simp, body, F, …]` in the library proofs. -/
register_simp_attr tm_simp

namespace QecReliability.FL

/-- The one-variable environment of a function body. -/
abbrev Env.one {a : Ty} (x : a.den) : Env [a] := .cons x .nil

@[simp] theorem Env.one_enc {a : Ty} (x : a.den) : (Env.one x).enc = [a.enc x] := rfl

namespace FnSig

variable {a b : Ty} {P : Program}

/-- `body` implements `F` at the argument `x`, assuming the calls it makes are valid. -/
structure BodyOK (P : Program) (F : FnSig a b) (body : Tm [a] b) (x : a.den) : Prop where
  calls : body.CallsOK P (Env.one x)
  den : body.den (Env.one x) = F.den x
  cost : body.cost (Env.one x) + 2 ≤ F.cost x
  depth : body.depth (Env.one x) + 1 ≤ F.depth x
  msize : body.msize (Env.one x) ≤ F.msize x

theorem validAt_of_bodyOK {F : FnSig a b} {body : Tm [a] b}
    (hP : P[F.idx]? = some body.compile) {x : a.den} (h : F.BodyOK P body x) :
    F.ValidAt P x := by
  intro m hm
  obtain ⟨c, d, hc, hd, e⟩ := body.eval (Env.one x) m h.calls (h.msize.trans hm)
  rw [h.den] at e
  refine ⟨c + 2, d + 1, ?_, ?_, EvalCall.intro hP e⟩
  · have := h.cost; omega
  · have := h.depth; omega

/-- Recursive functions: strong induction on a measure `μ`, for arguments satisfying `Q`.
The body may call `F` itself on arguments `y` with `μ y < μ x` and `Q y`. -/
theorem valid_of_body' (F : FnSig a b) (body : Tm [a] b)
    (hP : P[F.idx]? = some body.compile) (μ : a.den → ℕ) (Q : a.den → Prop)
    (h : ∀ x, Q x → (∀ y, μ y < μ x → Q y → F.ValidAt P y) → F.BodyOK P body x) :
    ∀ x, Q x → F.ValidAt P x := by
  intro x
  induction hx : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hq
    subst hx
    exact validAt_of_bodyOK hP (h x hq (fun y hy hqy => ih (μ y) hy y rfl hqy))

/-- Recursive functions, all arguments. -/
theorem valid_of_body (F : FnSig a b) (body : Tm [a] b)
    (hP : P[F.idx]? = some body.compile) (μ : a.den → ℕ)
    (h : ∀ x, (∀ y, μ y < μ x → F.ValidAt P y) → F.BodyOK P body x) :
    ∀ x, F.ValidAt P x := fun x =>
  valid_of_body' F body hP μ (fun _ => True)
    (fun x _ ih => h x (fun y hy => ih y hy trivial)) x trivial

/-- Non-recursive functions. -/
theorem valid_of_body_nonrec (F : FnSig a b) (body : Tm [a] b)
    (hP : P[F.idx]? = some body.compile) (h : ∀ x, F.BodyOK P body x) :
    ∀ x, F.ValidAt P x := fun x => validAt_of_bodyOK hP (h x)

/-- Monotonicity of the contract in the bounds. -/
theorem ValidAt.mono {F G : FnSig a b} {x : a.den} (hF : F.ValidAt P x) (hidx : G.idx = F.idx)
    (hden : G.den x = F.den x) (hc : F.cost x ≤ G.cost x) (hd : F.depth x ≤ G.depth x)
    (hm : F.msize x ≤ G.msize x) : G.ValidAt P x := by
  intro m hm'
  obtain ⟨t, d, ht, hd', e⟩ := hF m (hm.trans hm')
  exact ⟨t, d, ht.trans hc, hd'.trans hd, by rw [hidx, hden]; exact e⟩

/-- The contract in the form consumed by the machine level (`FL.Computes`), which also
asks the argument itself to fit in the budget. -/
theorem ValidAt.computes {F : FnSig a b} {x : a.den} (h : F.ValidAt P x) {m : ℕ}
    (hm : F.msize x ≤ m) (harg : (a.enc x).size ≤ m) :
    Computes P F.idx (a.enc x) (b.enc (F.den x)) m (F.cost x) (F.depth x) := by
  obtain ⟨t, d, ht, hd, e⟩ := h m hm
  exact ⟨harg, t, d, ht, hd, e⟩

end FnSig

/-! ## Encoded sizes -/

namespace Ty

/-- Size of the encoding of a typed value. -/
abbrev sz (t : Ty) (x : t.den) : ℕ := (t.enc x).size

@[simp] theorem enc_val (v : Val) : Ty.enc .val v = v := rfl
@[simp] theorem enc_unit (u : Unit) : Ty.enc .unit u = .nil := rfl
@[simp] theorem enc_bool (b : Bool) : Ty.enc .bool b = Enc.bool b := rfl
@[simp] theorem enc_nat (n : ℕ) : Ty.enc .nat n = Enc.nat n := rfl
@[simp] theorem enc_list_nil (t : Ty) : Ty.enc (.list t) [] = .nil := rfl
@[simp] theorem enc_list_cons (t : Ty) (x : t.den) (xs : List t.den) :
    Ty.enc (.list t) (x :: xs) = .cons (t.enc x) (Ty.enc (.list t) xs) := rfl
@[simp] theorem enc_prod (a b : Ty) (p : (Ty.prod a b).den) :
    Ty.enc (.prod a b) p = .cons (a.enc p.1) (b.enc p.2) := rfl

/-! Concrete element types: `List.cons` at `ℕ`/`Bool`/`ℕ × ℕ` (rather than at `Ty.den t`)
does not unify with `enc_list_cons`, so these instances are stated separately. -/
@[simp] theorem enc_list_cons_nat (x : ℕ) (xs : List ℕ) :
    Ty.enc (.list .nat) (@List.cons ℕ x xs) = .cons (Enc.nat x) (Ty.enc (.list .nat) xs) := rfl
@[simp] theorem enc_list_cons_bool (x : Bool) (xs : List Bool) :
    Ty.enc (.list .bool) (@List.cons Bool x xs) = .cons (Enc.bool x) (Ty.enc (.list .bool) xs) :=
  rfl
@[simp] theorem enc_list_cons_nat2 (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) :
    Ty.enc (.list (.prod .nat .nat)) (@List.cons (ℕ × ℕ) x xs) =
      .cons (.cons (Enc.nat x.1) (Enc.nat x.2)) (Ty.enc (.list (.prod .nat .nat)) xs) := rfl
@[simp] theorem enc_list_nil_nat : Ty.enc (.list .nat) (@List.nil ℕ) = .nil := rfl
@[simp] theorem enc_list_nil_bool : Ty.enc (.list .bool) (@List.nil Bool) = .nil := rfl
@[simp] theorem enc_list_nil_nat2 : Ty.enc (.list (.prod .nat .nat)) (@List.nil (ℕ × ℕ)) = .nil :=
  rfl
@[simp] theorem enc_prod_nat2 (x y : ℕ) :
    Ty.enc (.prod .nat .nat) (@Prod.mk ℕ ℕ x y) = .cons (Enc.nat x) (Enc.nat y) := rfl

theorem enc_list (t : Ty) (xs : List t.den) : Ty.enc (.list t) xs = Enc.list (Ty.enc t) xs := rfl

/-! Size lemmas are stated for `(t.enc x).size` (the simp normal form; `Ty.sz` is unfolded
by `tm_simp`), so that `omega` sees the same atoms. -/

theorem sz_pos (t : Ty) (x : t.den) : 1 ≤ (t.enc x).size := Val.size_pos _

theorem sz_list_nil (t : Ty) : (Ty.enc (.list t) []).size = 1 := rfl
theorem sz_list_cons (t : Ty) (x : t.den) (xs : List t.den) :
    (Ty.enc (.list t) (x :: xs)).size = 1 + (t.enc x).size + (Ty.enc (.list t) xs).size := rfl
theorem sz_prod (a b : Ty) (p : (Ty.prod a b).den) :
    (Ty.enc (.prod a b) p).size = 1 + (a.enc p.1).size + (b.enc p.2).size := rfl

theorem sz_bool_le (b : Bool) : (Ty.enc .bool b).size ≤ 3 := Enc.bool_size b

theorem sz_nat_le (n : ℕ) : (Ty.enc .nat n).size ≤ 4 * n.size + 1 := Enc.nat_size_le n

theorem sz_list_append (t : Ty) (xs ys : List t.den) :
    (Ty.enc (.list t) (xs ++ ys)).size + 1 =
      (Ty.enc (.list t) xs).size + (Ty.enc (.list t) ys).size := by
  induction xs with
  | nil => simp; omega
  | cons x xs ih => simp only [List.cons_append, sz_list_cons]; omega

theorem sz_list_eq (t : Ty) (xs : List t.den) :
    (Ty.enc (.list t) xs).size = 1 + (xs.map (fun x => (t.enc x).size + 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [sz_list_cons, ih, List.map_cons, List.sum_cons]; omega

theorem sz_list_le (t : Ty) (xs : List t.den) (M : ℕ) (h : ∀ x ∈ xs, (t.enc x).size ≤ M) :
    (Ty.enc (.list t) xs).size ≤ xs.length * (M + 1) + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    simp only [sz_list_cons, List.length_cons, Nat.succ_mul]
    omega

theorem length_le_sz (t : Ty) (xs : List t.den) : xs.length + 1 ≤ (Ty.enc (.list t) xs).size := by
  induction xs with
  | nil => simp
  | cons x xs ih => have := sz_pos t x; simp only [sz_list_cons, List.length_cons]; omega

theorem sz_mem_le (t : Ty) {xs : List t.den} {x : t.den} (h : x ∈ xs) :
    (t.enc x).size + 2 ≤ (Ty.enc (.list t) xs).size := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [sz_list_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · have := sz_pos (.list t) ys; omega
    · have := ih h'; omega

theorem sz_sublist (t : Ty) {xs ys : List t.den} (h : xs.Sublist ys) :
    (Ty.enc (.list t) xs).size ≤ (Ty.enc (.list t) ys).size := by
  induction h with
  | slnil => exact le_rfl
  | cons a _ ih => simp only [sz_list_cons]; omega
  | cons_cons a _ ih => simp only [sz_list_cons]; omega

theorem sz_replicate (t : Ty) (n : ℕ) (x : t.den) :
    (Ty.enc (.list t) (List.replicate n x)).size = n * ((t.enc x).size + 1) + 1 := by
  induction n with
  | zero => simp [sz_list_nil]
  | succ n ih => simp only [List.replicate_succ, sz_list_cons, ih, Nat.succ_mul]; omega

end Ty

/-! ## Bit lengths -/

namespace NatSize

theorem size_half {n : ℕ} (hn : n ≠ 0) : (n / 2).size + 1 = n.size := by
  have h1 := Nat.size_bit (b := n.bodd) (n := n.div2) (by rw [Nat.bit_bodd_div2]; exact hn)
  rw [Nat.bit_bodd_div2, Nat.div2_val] at h1
  omega

theorem size_half_le (n : ℕ) : (n / 2).size ≤ n.size := by
  by_cases hn : n = 0
  · subst hn; simp
  · have := size_half hn; omega

theorem size_mono {m n : ℕ} (h : m ≤ n) : m.size ≤ n.size := Nat.size_le_size h

theorem size_le_self (n : ℕ) : n.size ≤ n := by
  rw [Nat.size_le]
  exact Nat.lt_two_pow_self

theorem size_pos_of_ne {n : ℕ} (hn : n ≠ 0) : 1 ≤ n.size := by
  have := size_half hn; omega

theorem size_eq_zero {n : ℕ} : n.size = 0 ↔ n = 0 := by
  constructor
  · intro h; by_contra hn; have := size_pos_of_ne hn; omega
  · rintro rfl; simp

theorem lt_pow_size (n : ℕ) : n < 2 ^ n.size := Nat.lt_size_self n

theorem size_add_le (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le]
  have ha := lt_pow_size a
  have hb := lt_pow_size b
  have h1 : 2 ^ a.size ≤ 2 ^ max a.size b.size := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h2 : 2 ^ b.size ≤ 2 ^ max a.size b.size := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  rw [pow_succ]
  omega

theorem size_succ_le (n : ℕ) : (n + 1).size ≤ n.size + 1 := by
  have := size_add_le n 1
  have h1 : (1 : ℕ).size ≤ 1 := size_le_self 1
  by_cases hn : n = 0
  · subst hn; simp
  · have := size_pos_of_ne hn; omega

theorem size_add_succ_le (a b : ℕ) : (a + b + 1).size ≤ a.size + b.size + 1 := by
  rw [Nat.size_le]
  have ha := lt_pow_size a
  have hb := lt_pow_size b
  have h1 : 2 ^ a.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ b.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_succ]
  omega

theorem size_add_le' (a b : ℕ) : (a + b).size ≤ a.size + b.size + 1 :=
  (size_mono (by omega)).trans (size_add_succ_le a b)

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le, pow_add]
  have ha := lt_pow_size a
  have hb := lt_pow_size b
  calc a * b ≤ a * 2 ^ b.size := Nat.mul_le_mul_left _ hb.le
    _ < 2 ^ a.size * 2 ^ b.size := by
      have : 0 < 2 ^ b.size := Nat.two_pow_pos _
      exact Nat.mul_lt_mul_of_pos_right ha this

theorem size_double_le (n : ℕ) : (2 * n).size ≤ n.size + 1 := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [Nat.size_le, pow_succ]
    have := lt_pow_size n
    omega

theorem size_bitNat_le (b : Bool) (n : ℕ) : (bitNat b n).size ≤ n.size + 1 := by
  rw [Nat.size_le, pow_succ]
  have := lt_pow_size n
  unfold bitNat; split <;> omega

theorem size_bit1_le (n : ℕ) : (2 * n + 1).size ≤ n.size + 1 := by
  have := size_bitNat_le true n; simpa [bitNat] using this

theorem size_div_le (a b : ℕ) : (a / b).size ≤ a.size := size_mono (Nat.div_le_self a b)

theorem size_sub_le (a b : ℕ) : (a - b).size ≤ a.size := size_mono (Nat.sub_le a b)

theorem size_max_le (a b : ℕ) : (max a b).size ≤ a.size + b.size := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

theorem size_min_le (a b : ℕ) : (min a b).size ≤ a.size :=
  size_mono (min_le_left a b)

end NatSize

end QecReliability.FL
