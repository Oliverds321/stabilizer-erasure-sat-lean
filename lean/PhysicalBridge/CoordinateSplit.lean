import PhysicalBridge.PauliTrace

/-! Exact computational-basis coordinates for survivors and erased qubits.
An empty coordinate set has its usual one-element function-space basis. -/
noncomputable section
namespace QecPhysical.BinaryPauli
open scoped BigOperators
open QecReliability.Binary
variable {n : ℕ} (E : Finset (Fin n))

abbrev SurvivorWord := {i : Fin n // i ∉ E} → Bit
abbrev ErasedWord := Word (Fintype.card E)

def erasedPart (w : Word n) : ErasedWord E :=
  fun j => w ((Fintype.equivFin E).symm j).val

def survivorPart (w : Word n) : SurvivorWord E := fun i => w i.val

def joinWord (p : SurvivorWord E × ErasedWord E) : Word n :=
  fun i => if hi : i ∈ E then p.2 ((Fintype.equivFin E) ⟨i,hi⟩) else p.1 ⟨i,hi⟩

@[simp] theorem erasedPart_join (p : SurvivorWord E × ErasedWord E) :
    erasedPart E (joinWord E p) = p.2 := by
  funext j
  simp [erasedPart, joinWord]

@[simp] theorem survivorPart_join (p : SurvivorWord E × ErasedWord E) :
    survivorPart E (joinWord E p) = p.1 := by
  funext i
  simp [survivorPart, joinWord, i.property]

def wordSplit : Word n ≃ SurvivorWord E × ErasedWord E where
  toFun w := (survivorPart E w, erasedPart E w)
  invFun := joinWord E
  left_inv w := by
    funext i
    by_cases hi : i∈E <;> simp [joinWord, survivorPart, erasedPart, hi]
  right_inv p := Prod.ext (survivorPart_join E p) (erasedPart_join E p)

def extendErased (w : ErasedWord E) : Word n := joinWord E (0,w)

@[simp] theorem erasedPart_extend (w : ErasedWord E) :
    erasedPart E (extendErased E w) = w := erasedPart_join E (0,w)

@[simp] theorem survivorPart_extend (w : ErasedWord E) :
    survivorPart E (extendErased E w) = 0 := survivorPart_join E (0,w)

theorem wordSplit_add_extend (w : Word n) (x : ErasedWord E) :
    wordSplit E (w+extendErased E x) = (survivorPart E w, erasedPart E w+x) := by
  apply Prod.ext
  · funext i
    simp [wordSplit, survivorPart, extendErased, joinWord, i.property]
  · funext j
    simp [wordSplit, erasedPart, extendErased, joinWord]

theorem wordDot_extend (z : ErasedWord E) (w : Word n) :
    wordDot (extendErased E z) w = wordDot z (erasedPart E w) := by
  rw [wordDot, ← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i∈E)]
  have hz : (∑ i : {i : Fin n // ¬i∈E}, extendErased E z i.val * w i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [extendErased, joinWord, i.property]
  rw [hz, add_zero]
  rw [Subsingleton.elim (Subtype.fintype (fun i : Fin n => i∈E)) (Finset.Subtype.fintype E)]
  change (∑ i : E, extendErased E z i.val * w i.val) =
    ∑ j : Fin (Fintype.card E), z j * erasedPart E w j
  apply Fintype.sum_equiv (Fintype.equivFin E)
  intro i
  simp [extendErased, joinWord, i.property, erasedPart]

def supportedLabelEquiv : Pauli (Fintype.card E) ≃ supported E where
  toFun u := ⟨(extendErased E u.1, extendErased E u.2), by
    intro i hi
    simp [extendErased, joinWord, hi]⟩
  invFun u := (erasedPart E u.val.1, erasedPart E u.val.2)
  left_inv u := Prod.ext (erasedPart_extend E u.1) (erasedPart_extend E u.2)
  right_inv u := by
    apply Subtype.ext
    apply Prod.ext <;> funext i
    · by_cases hi : i∈E
      · simp [extendErased, joinWord, erasedPart, hi]
      · simp [extendErased, joinWord, hi, (u.property i hi).1]
    · by_cases hi : i∈E
      · simp [extendErased, joinWord, erasedPart, hi]
      · simp [extendErased, joinWord, hi, (u.property i hi).2]

end QecPhysical.BinaryPauli
