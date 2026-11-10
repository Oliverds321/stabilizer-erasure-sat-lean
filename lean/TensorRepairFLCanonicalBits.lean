import QecReliability.TensorLayers
import TensorMachineGrid
import PhysicalBridge.RationalTensorRepair

/-! The executable canonical assignment used to compute exact tensor anchors.
Its blocks are ordered exactly like TensorLatent.flattenCauses. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open TensorBernstein TensorLatent

/-- First `k` causes in a class of size `r`, in increasing cause-index order. -/
def canonicalBlock (r k : ℕ) : List Bool := (List.range r).map (fun i => decide (i < k))

/-- Missing coordinates truncate this total reader. Typed grid inputs always
supply exactly one coordinate per class. -/
def canonicalBits : List ℕ → List ℕ → List Bool
  | r :: ds, k :: ks => canonicalBlock r k ++ canonicalBits ds ks
  | _, _ => []

theorem canonicalBlock_ofFn (r k : ℕ) :
    canonicalBlock r k = List.ofFn (fun i : Fin r => decide (i.val < k)) := by
  apply List.ext_getElem
  · simp [canonicalBlock]
  · intro i hi hi'
    simp [canonicalBlock]

theorem canonicalBlock_length (r k : ℕ) : (canonicalBlock r k).length = r := by
  simp [canonicalBlock]

theorem canonicalBits_length (ds : List ℕ) (j : Grid ds) :
    (canonicalBits ds (TensorMachine.indexList ds j)).length = ds.sum := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    simp only [canonicalBits, TensorMachine.indexList, List.length_append,
      canonicalBlock_length, ih, List.sum_cons]

private theorem ofFn_append {r s : ℕ} (a : Fin r → Bool) (b : Fin s → Bool) :
    List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b := by
  rw [List.ofFn_add]
  congr 1 <;> apply congrArg List.ofFn <;> funext i <;> simp

/-- The raw machine word is exactly the canonical tuple's flattened membership
assignment, with the head class first. -/
theorem canonicalBits_causesBits (ds : List ℕ) (j : Grid ds) :
    canonicalBits ds (TensorMachine.indexList ds j) =
      List.ofFn (TensorLatent.causesBits ds (canonicalCauses ds j)) := by
  induction ds with
  | nil => simp [canonicalBits, TensorMachine.indexList]
  | cons r ds ih =>
    change canonicalBlock r j.1.val ++ canonicalBits ds (TensorMachine.indexList ds j.2) =
      List.ofFn (Fin.append
        (Binary.causeBits r (Finset.univ.filter (fun i : Fin r => i.val < j.1.val)))
        (TensorLatent.causesBits ds (canonicalCauses ds j.2)))
    rw [ofFn_append, ih, canonicalBlock_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    simp [Binary.causeBits]

/-- Exact connection to the latent cause set used by the counting model. -/
theorem canonicalBits_flattenCauses (ds : List ℕ) (j : Grid ds) :
    canonicalBits ds (TensorMachine.indexList ds j) =
      List.ofFn (Binary.causeBits ds.sum (flattenCauses ds (canonicalCauses ds j))) := by
  rw [canonicalBits_causesBits]
  congr 1
  exact ((Binary.causeBits ds.sum).apply_symm_apply
    (TensorLatent.causesBits ds (canonicalCauses ds j))).symm

end QecReliability.TensorMachine.RepairFL
