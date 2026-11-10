import OracleCost.FixedSlotExchangeTrace
import OracleCost.QueryCodec

/-! Explicit padded fixed-slot encoding. The original logical field lengths
are retained in a word; padding is not reinterpreted as additional list data.
This is an adapter, not a replacement of the existing configFields encoding. -/
namespace QecReliability.OracleCost.MultiTape.FixedSlot
open Turing Displacement

def encode (width : ℕ) (xs : List ℕ) : List Bool := xs.flatMap (QueryCodec.word width)

def readWords (width : ℕ) : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0,bits => some ([],bits)
  | count+1,bits => do
      let (x,rest) ← QueryCodec.readWord width bits
      let (xs,tail) ← readWords width count rest
      pure (x::xs,tail)

@[simp] theorem encode_length (width : ℕ) (xs : List ℕ) :
    (encode width xs).length=xs.length*width := by
  induction xs <;> simp_all [encode,Nat.add_mul,Nat.add_comm]

@[simp] theorem encode_append (width : ℕ) (xs ys : List ℕ) :
    encode width (xs++ys)=encode width xs++encode width ys := by simp [encode]

theorem readWords_encode (width : ℕ) (xs : List ℕ) (suffix : List Bool)
    (hfit : ∀ x∈xs,x<2^width) :
    readWords width xs.length (encode width xs++suffix)=some (xs,suffix) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hfit x (by simp)
    have ht := ih (fun y hy => hfit y (by simp [hy]))
    simp only [encode,List.flatMap_cons,List.length_cons,List.append_assoc,readWords,
      QueryCodec.readWord_word width x _ hx,Option.bind_eq_bind,Option.bind_some]
    change (readWords width xs.length (encode width xs++suffix)).bind _=_
    rw [ht]
    rfl

def pad (capacity : ℕ) (xs : List ℕ) : List ℕ := xs++List.replicate (capacity-xs.length) 0

def fieldWords (capacity : ℕ) (xs : List ℕ) : List ℕ := xs.length::pad capacity xs

def fieldBits (width capacity : ℕ) (xs : List ℕ) := encode width (fieldWords capacity xs)

def readField (width capacity : ℕ) (bits : List Bool) : Option (List ℕ × List Bool) := do
  let (n,rest) ← QueryCodec.readWord width bits
  let (xs,tail) ← readWords width capacity rest
  if n≤capacity then pure (xs.take n,tail) else none

@[simp] theorem pad_length (capacity : ℕ) (xs : List ℕ) (hcap : xs.length≤capacity) :
    (pad capacity xs).length=capacity := by simp [pad]; omega

@[simp] theorem fieldBits_length (width capacity : ℕ) (xs : List ℕ) (hcap : xs.length≤capacity) :
    (fieldBits width capacity xs).length=(capacity+1)*width := by
  simp [fieldBits,fieldWords,hcap]

theorem pad_fits (width capacity : ℕ) (xs : List ℕ) (hfit : ∀ x∈xs,x<2^width) :
    ∀ x∈pad capacity xs,x<2^width := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact hfit x hx
  · have : x=0 := List.eq_of_mem_replicate hx
    subst x; exact pow_pos (by decide) _

theorem readField_fieldBits (width capacity : ℕ) (xs : List ℕ) (suffix : List Bool)
    (hcap : xs.length≤capacity) (hlen : xs.length<2^width) (hfit : ∀ x∈xs,x<2^width) :
    readField width capacity (fieldBits width capacity xs++suffix)=some (xs,suffix) := by
  have hp := readWords_encode width (pad capacity xs) suffix (pad_fits width capacity xs hfit)
  rw [pad_length _ _ hcap] at hp
  simp only [readField,fieldBits,fieldWords,encode,List.flatMap_cons,List.append_assoc,
    QueryCodec.readWord_word width xs.length _ hlen,Option.bind_eq_bind,Option.bind_some]
  change (readWords width capacity (encode width (pad capacity xs)++suffix)).bind _=_
  rw [hp]
  simp [hcap,pad]

/-- An actual cursor-local word replacement and old-value return. Prefix and
suffix are logical slot lists; the SAME table handles every runtime value. -/
theorem exchange_encoded_slot {k : ℕ} {Λ : Type} [Fintype Λ]
    (M : Machine k (Option Bool) Λ) (array guide register : Fin (k+1))
    (hsep : array≠guide ∧ array≠register ∧ guide≠register)
    (others : Fin (k+1) → Tape (Option Bool))
    (width old new : ℕ) (before after : List ℕ) (guideBits : List Bool)
    (hguide : guideBits.length=width) :
    Run (FixedSlotExchange.attach M array guide register)
      (FixedSlotExchange.scanning array guide register others (encode width before).reverse
        (QueryCodec.word width old++encode width after) [] guideBits [] (QueryCodec.word width new))
      (2*width+2) (fun j => if j=array then (width:ℤ) else 0)
      (FixedSlotExchange.finished M array guide register others
        (QueryCopy.tape (encode width (before++[new])).reverse (encode width after))
        guideBits (QueryCodec.word width old)) := by
  simpa [encode,List.reverse_append] using
    FixedSlotExchange.slot_run M array guide register hsep others
      (QueryCodec.word width old) (QueryCodec.word width new) guideBits
      (encode width before).reverse (encode width after) (by simp) (by simpa using hguide)

end QecReliability.OracleCost.MultiTape.FixedSlot
