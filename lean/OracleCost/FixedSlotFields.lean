import OracleCost.FixedSlotEncoding

namespace QecReliability.OracleCost.MultiTape.FixedSlot

def fieldsBits (width capacity : ℕ) (fields : List (List ℕ)) : List Bool :=
  fields.flatMap (fieldBits width capacity)

def readFields (width capacity : ℕ) : ℕ → List Bool → Option (List (List ℕ) × List Bool)
  | 0,bits => some ([],bits)
  | count+1,bits => do
      let (xs,rest) ← readField width capacity bits
      let (fields,tail) ← readFields width capacity count rest
      pure (xs::fields,tail)

structure Fits (width capacity : ℕ) (fields : List (List ℕ)) : Prop where
  lengths : ∀ xs∈fields,xs.length≤capacity
  lengthWords : ∀ xs∈fields,xs.length<2^width
  values : ∀ xs∈fields,∀ x∈xs,x<2^width

theorem fieldsBits_length (width capacity : ℕ) (fields : List (List ℕ))
    (h : ∀ xs∈fields,xs.length≤capacity) :
    (fieldsBits width capacity fields).length=fields.length*((capacity+1)*width) := by
  induction fields with
  | nil => simp [fieldsBits,readFields]
  | cons xs fields ih =>
    have hx := h xs (by simp)
    have ht := ih (fun ys hy => h ys (by simp [hy]))
    simp only [fieldsBits,List.flatMap_cons,List.length_append,List.length_cons] at ht ⊢
    rw [fieldBits_length _ _ _ hx,ht]
    simp [Nat.add_mul,Nat.add_comm]

theorem readFields_fieldsBits (width capacity : ℕ) (fields : List (List ℕ))
    (suffix : List Bool) (h : Fits width capacity fields) :
    readFields width capacity fields.length (fieldsBits width capacity fields++suffix)=some (fields,suffix) := by
  induction fields with
  | nil => simp [fieldsBits,readFields]
  | cons xs fields ih =>
    have hx := readField_fieldBits width capacity xs
      (fieldsBits width capacity fields++suffix) (h.lengths xs (by simp))
      (h.lengthWords xs (by simp)) (h.values xs (by simp))
    have ht := ih ⟨fun ys hy => h.lengths ys (by simp [hy]),
      fun ys hy => h.lengthWords ys (by simp [hy]),fun ys hy => h.values ys (by simp [hy])⟩
    simp only [fieldsBits,List.flatMap_cons,List.length_cons,List.append_assoc,readFields]
    change (readField width capacity (fieldBits width capacity xs++(fieldsBits width capacity fields++suffix))).bind _=_
    rw [hx]
    simp only [Option.bind_some]
    rw [ht]
    rfl

end QecReliability.OracleCost.MultiTape.FixedSlot
