import TensorMachineGridFL
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Structural bounds for the actual list representation of the tensor table.
The table size remains explicit when the class count varies. -/

namespace QecReliability.TensorMachine

open FL

theorem grid_nodup (ds : List ℕ) : (grid ds).Nodup := by
  induction ds with
  | nil => simp [grid]
  | cons r ds ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro j hj
      exact ih.map (fun a b h => (List.cons.inj h).2)
    · exact (List.nodup_range).imp fun {a b} hab xs ha hb => by
        rcases List.mem_map.mp ha with ⟨ys, _, rfl⟩
        rcases List.mem_map.mp hb with ⟨zs, _, h⟩
        exact hab (List.cons.inj h).1.symm

theorem validIndex_entry_le_sum {ds js : List ℕ} (h : ValidIndex ds js) :
    ∀ j ∈ js, j ≤ ds.sum := by
  induction ds generalizing js with
  | nil => cases js <;> simp_all [ValidIndex]
  | cons r ds ih =>
    cases js with
    | nil => simp
    | cons k ks =>
      rcases h with ⟨hk, hks⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · simp only [List.sum_cons]; omega
      · have ht := ih hks j hj
        simp only [List.sum_cons]; omega

/-- The exponent is the number of classes; it is fixed only in fixed-class corollaries. -/
theorem slots_le_pow (ds : List ℕ) : slots ds ≤ (ds.sum + 1) ^ ds.length := by
  have h := List.prod_le_pow_card (ds.map (fun r => r + 1)) (ds.sum + 1) (by
    intro x hx
    rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
    have hr' : r ≤ ds.sum := List.single_le_sum (fun _ _ => Nat.zero_le _) r hr
    omega)
  simpa only [slots, List.length_map] using h

/-- Every coordinate list has a concrete polynomial encoding-size bound. -/
theorem grid_row_size {ds js : List ℕ} (h : js ∈ grid ds) :
    ((Ty.list Ty.nat).enc js).size ≤ ds.length * (4 * ds.sum + 2) + 1 := by
  have hv := (mem_grid_iff ds js).mp h
  have hs := Ty.sz_list_le .nat js (4 * ds.sum + 1) (by
    intro j hj
    have hj' := validIndex_entry_le_sum hv j hj
    have hb := Ty.sz_nat_le j
    have hn := NatSize.size_le_self j
    omega)
  simpa only [validIndex_length hv, Nat.add_assoc] using hs

/-- Actual table storage is polynomial in structural input size and table cardinality. -/
theorem grid_encoding_size (ds : List ℕ) :
    (GridFL.Table.enc (grid ds)).size ≤
      slots ds * (ds.length * (4 * ds.sum + 2) + 2) + 1 := by
  have h := Ty.sz_list_le (.list .nat) (grid ds)
    (ds.length * (4 * ds.sum + 2) + 1) (fun _ h => grid_row_size h)
  simpa only [grid_length, Nat.add_assoc] using h

end QecReliability.TensorMachine
