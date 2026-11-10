import FL.CEK
import Mathlib.Data.Nat.Size

/-!
# Encodings of data as FL trees

* `Bool`: `false ↦ nil`, `true ↦ cons nil nil`.
* `ℕ` (data): little-endian binary digits as a list of booleans, no trailing zero digit
  (`0 ↦ nil`). Size `≤ 3 * n.size + 1`.
* lists: `[] ↦ nil`, `x :: xs ↦ cons (enc x) (enc xs)`; pairs: `cons`.
* FL syntax (`Expr`, `Frame`, `State`) is encoded with unary tags and indices, so the CEK
  machine's states are themselves FL values (`State.enc`), which is what the register
  interpreter manipulates.
-/

set_option autoImplicit false

namespace QecReliability.FL

/-- Types with a canonical injective tree encoding. -/
class Encodable (α : Type) where
  enc : α → Val
  enc_injective : Function.Injective enc

export Encodable (enc)

namespace Enc

def bool : Bool → Val
  | false => .nil
  | true => .cons .nil .nil

theorem bool_injective : Function.Injective bool := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

@[simp] theorem bool_size (b : Bool) : (bool b).size ≤ 3 := by cases b <;> simp [bool]

/-- Little-endian binary digits; `0 ↦ nil`. -/
def nat (n : ℕ) : Val :=
  if h : n = 0 then .nil else .cons (bool (n % 2 = 1)) (nat (n / 2))
termination_by n
decreasing_by omega

theorem nat_zero : nat 0 = .nil := by rw [nat]; simp

theorem nat_pos {n : ℕ} (h : n ≠ 0) : nat n = .cons (bool (n % 2 = 1)) (nat (n / 2)) := by
  rw [nat]; simp [h]

theorem nat_injective : Function.Injective nat := by
  intro a b h
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · exact hb.symm
      · rw [nat_zero, nat_pos hb] at h; cases h
    · by_cases hb : b = 0
      · subst hb; rw [nat_zero, nat_pos ha] at h; cases h
      · rw [nat_pos ha, nat_pos hb] at h
        injection h with h1 h2
        have hbit : (a % 2 = 1) = (b % 2 = 1) := by
          have := bool_injective h1; simpa using this
        have hdiv := ih (a / 2) (by omega) h2
        have hb2 : a % 2 = b % 2 := by
          rcases Nat.mod_two_eq_zero_or_one a with h' | h' <;>
          rcases Nat.mod_two_eq_zero_or_one b with h'' | h'' <;> simp_all
        omega

theorem nat_size_le (n : ℕ) : (nat n).size ≤ 4 * n.size + 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [nat_zero]
    · rw [nat_pos hn]
      have h := ih (n / 2) (by omega)
      have hs : (n / 2).size + 1 = n.size := by
        have h1 := Nat.size_bit (b := n.bodd) (n := n.div2) (by rw [Nat.bit_bodd_div2]; exact hn)
        rw [Nat.bit_bodd_div2, Nat.div2_val] at h1
        omega
      simp only [Val.size_cons]
      have := bool_size (n % 2 = 1)
      omega

def list {α : Type} (f : α → Val) : List α → Val
  | [] => .nil
  | x :: xs => .cons (f x) (list f xs)

theorem list_injective {α : Type} {f : α → Val} (hf : Function.Injective f) :
    Function.Injective (list f) := by
  intro a b h
  induction a generalizing b with
  | nil => cases b with | nil => rfl | cons _ _ => cases h
  | cons x xs ih =>
    cases b with
    | nil => cases h
    | cons y ys =>
      injection h with h1 h2
      rw [hf h1, ih h2]

theorem list_size {α : Type} (f : α → Val) (xs : List α) :
    (list f xs).size = 1 + (xs.map (fun x => (f x).size + 1)).sum := by
  induction xs with
  | nil => simp [list]
  | cons x xs ih => simp [list, ih]; omega

def pair {α β : Type} (f : α → Val) (g : β → Val) (p : α × β) : Val := .cons (f p.1) (g p.2)

/-- Unary numerals (`n` conses of `nil`), used for syntax tags and indices: the interpreter
walks them one node at a time. -/
def unary : ℕ → Val
  | 0 => .nil
  | n + 1 => .cons .nil (unary n)

theorem unary_injective : Function.Injective unary := by
  intro a b h
  induction a generalizing b with
  | zero => cases b with | zero => rfl | succ _ => cases h
  | succ a ih =>
    cases b with
    | zero => cases h
    | succ b => injection h with _ h2; rw [ih h2]

@[simp] theorem unary_size (n : ℕ) : (unary n).size = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unary, ih]; omega

end Enc

instance : Encodable Bool := ⟨Enc.bool, Enc.bool_injective⟩
instance : Encodable ℕ := ⟨Enc.nat, Enc.nat_injective⟩
instance {α : Type} [Encodable α] : Encodable (List α) :=
  ⟨Enc.list enc, Enc.list_injective Encodable.enc_injective⟩
instance {α β : Type} [Encodable α] [Encodable β] : Encodable (α × β) :=
  ⟨Enc.pair enc enc, by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    injection h with h1 h2
    exact Prod.ext (Encodable.enc_injective h1) (Encodable.enc_injective h2)⟩
instance : Encodable Val := ⟨id, Function.injective_id⟩

/-! ## FL syntax as data -/

/-- Unary tag `j` followed by a payload. -/
def tagged (j : ℕ) (payload : Val) : Val := .cons (Enc.unary j) payload

def Expr.enc : Expr → Val
  | .var i => tagged 0 (Enc.unary i)
  | .nil => tagged 1 .nil
  | .cons a b => tagged 2 (.cons a.enc b.enc)
  | .case s e₁ e₂ => tagged 3 (.cons s.enc (.cons e₁.enc e₂.enc))
  | .call f a => tagged 4 (.cons (Enc.unary f) a.enc)
  | .letE a b => tagged 5 (.cons a.enc b.enc)
  | .cond s e₁ e₂ => tagged 6 (.cons s.enc (.cons e₁.enc e₂.enc))
  | .fst a => tagged 7 a.enc
  | .snd a => tagged 8 a.enc

def envEnc (env : List Val) : Val := Enc.list id env

def Frame.enc : Frame → Val
  | .consL b env => tagged 0 (.cons b.enc (envEnc env))
  | .consR va => tagged 1 va
  | .caseK e₁ e₂ env => tagged 2 (.cons e₁.enc (.cons e₂.enc (envEnc env)))
  | .callK f => tagged 3 (Enc.unary f)
  | .letK b env => tagged 4 (.cons b.enc (envEnc env))
  | .condK e₁ e₂ env => tagged 5 (.cons e₁.enc (.cons e₂.enc (envEnc env)))
  | .fstK => tagged 6 .nil
  | .sndK => tagged 7 .nil

def stackEnc (k : List Frame) : Val := Enc.list Frame.enc k

def State.enc : State → Val
  | .eval e env k => tagged 0 (.cons e.enc (.cons (envEnc env) (stackEnc k)))
  | .ret v k => tagged 1 (.cons v (stackEnc k))

def Program.enc (P : Program) : Val := Enc.list Expr.enc P

theorem tagged_injective {i j : ℕ} {a b : Val} (h : tagged i a = tagged j b) : i = j ∧ a = b := by
  injection h with h1 h2
  exact ⟨Enc.unary_injective h1, h2⟩

theorem Expr.enc_injective : Function.Injective Expr.enc := by
  intro e f h
  induction e generalizing f with
  | var i =>
    cases f <;> obtain ⟨h1, h2⟩ := tagged_injective h <;> try omega
    rw [Enc.unary_injective h2]
  | nil => cases f <;> obtain ⟨h1, h2⟩ := tagged_injective h <;> first | omega | rfl
  | cons a b iha ihb =>
    cases f <;> obtain ⟨h1, h2⟩ := tagged_injective h <;> try omega
    injection h2 with h3 h4; rw [iha h3, ihb h4]
  | case s a b ihs iha ihb =>
    cases f <;> obtain ⟨h1, h2⟩ := tagged_injective h <;> try omega
    injection h2 with h3 h4; injection h4 with h5 h6; rw [ihs h3, iha h5, ihb h6]
  | call g a iha =>
    cases f <;> obtain ⟨h1, h2⟩ := tagged_injective h <;> try omega
    injection h2 with h3 h4; rw [Enc.unary_injective h3, iha h4]
  | letE a b iha ihb =>
    cases f <;> obtain ⟨h1, h2⟩ := tagged_injective h <;> try omega
    injection h2 with h3 h4; rw [iha h3, ihb h4]
  | cond s a b ihs iha ihb =>
    cases f <;> obtain ⟨h1, h2⟩ := tagged_injective h <;> try omega
    injection h2 with h3 h4; injection h4 with h5 h6; rw [ihs h3, iha h5, ihb h6]
  | fst a iha =>
    cases f <;> obtain ⟨h1, h2⟩ := tagged_injective h <;> try omega
    rw [iha h2]
  | snd a iha =>
    cases f <;> obtain ⟨h1, h2⟩ := tagged_injective h <;> try omega
    rw [iha h2]

end QecReliability.FL
