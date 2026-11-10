import TensorRepairFLAnchors
import Trans.BoundsRest.EndPoly

/-! Structural polynomial bounds for canonical latent words and masks. No
large ratio numerator or denominator enters these magnitude-based bounds. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib Trans.Wire
open Trans.Query.Bound Trans.BoundsQH Trans.BoundsRest

variable (L : Lib) (ci : CanonicalIndices) (y : Trans.Control.IxR) (ai : AnchorIndices)

theorem canonicalBit_poly : PolyB (canonicalBitF L ci) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,canonicalBitBody,polyB])

theorem block_poly : PolyB (blockF L ci) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,blockBody,polyB,mapEnvH_P,canonicalBit_poly])

theorem bitsStep_poly : PolyB (bitsStepF L ci y.append) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,bitsStepBody,polyB,block_poly])

private theorem bitsStep_key_mag (ks : Key) (acc : List Bool) (r : ℕ) :
    mag TKey (bitsStepR (ks,acc) r).1 ≤ mag TKey ks := by
  cases ks with
  | nil => exact le_rfl
  | cons k ks =>
    change mag TKey ks ≤ k+1+mag TKey ks
    omega

private theorem bitsStep_length (ks : Key) (acc : List Bool) (r : ℕ) :
    (bitsStepR (ks,acc) r).2.length ≤ acc.length+r := by
  cases ks <;> simp [bitsStepR,canonicalBlock,List.length_map,List.length_range]

theorem bitsFold_poly : PolyB (foldlF (bitsStepF L ci y.append) ci.bitsFold) := by
  refine foldl_polyB_idx (bitsStepF L ci y.append) ci.bitsFold (bitsStep_poly L ci y)
    (kR := 2) (cR := 10) (fun z xs => ⟨fun n acc =>
      mag TKey acc.1 ≤ mag TKey z.1 ∧ acc.2.length ≤ z.2.length+n*mag TKey xs,
      ⟨le_rfl,by simp⟩,?_,?_⟩)
  · intro r hr n hn acc hacc
    rcases acc with ⟨ks,bs⟩
    simp only [Prod.fst,Prod.snd] at hacc
    rw [bitsStepF_den]
    have hk := bitsStep_key_mag ks bs r
    have hl := bitsStep_length ks bs r
    have hm : r ≤ mag TKey xs := by
      have hmem : r+2 ≤ mag TKey xs := mag_mem Ty.nat hr
      exact (Nat.le_add_right r 2).trans hmem
    refine ⟨hk.trans hacc.1,?_⟩
    calc
      (bitsStepR (ks,bs) r).2.length ≤ bs.length+r := hl
      _ ≤ (z.2.length+n*mag TKey xs)+mag TKey xs := Nat.add_le_add hacc.2 hm
      _ = z.2.length+(n+1)*mag TKey xs := by simp only [Nat.add_mul,Nat.one_mul,Nat.add_assoc]
  · intro n hn acc hacc
    have hl : xs.length+1 ≤ mag TKey xs := mag_list_len Ty.nat xs
    have hb : mag TBits acc.2 = 2*acc.2.length+1 := mag_bools_eq acc.2
    have hz : mag TBits z.2 = 2*z.2.length+1 := mag_bools_eq z.2
    have hq := quad_le 10 (mag (.prod (.prod TKey TBits) (.list Ty.nat)) (z,xs))
    simp only [mag_prod] at hq ⊢
    have hnM : n ≤ mag TKey xs := hn.trans ((Nat.le_add_right xs.length 1).trans hl)
    have hh := hacc.1
    have hh' := hacc.2
    have hm : n*mag TKey xs ≤ (mag TKey xs)*(mag TKey xs) := Nat.mul_le_mul_right _ hnM
    simp only [TKey,TBits] at *
    nlinarith

theorem bits_poly : PolyB (bitsF L ci y.append) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,bitsBody,bitsFold_poly])

theorem cornerStep_poly : PolyB (cornerStepF L ci) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,cornerStepBody,polyB])

private theorem cornerStep_key_mag (ks : Key) (b : Bool) (r : ℕ) :
    mag TKey (cornerStepR (ks,b) r).1 ≤ mag TKey ks := by
  cases ks with
  | nil => exact le_rfl
  | cons k ks =>
    change mag TKey ks ≤ k+1+mag TKey ks
    omega

theorem cornerFold_poly : PolyB (foldlF (cornerStepF L ci) ci.cornerFold) := by
  refine foldl_polyB (cornerStepF L ci) ci.cornerFold (cornerStep_poly L ci) (kR := 0) (cR := 2)
    (fun z xs => ⟨fun acc => mag TKey acc.1 ≤ mag TKey z.1,le_rfl,?_,?_⟩)
  · intro r hr acc hacc
    rcases acc with ⟨ks,b⟩
    rw [cornerStepF_den]
    exact (cornerStep_key_mag ks b r).trans hacc
  · intro acc hacc
    rw [G_zero]
    simp only [mag_prod,mag_bool]
    omega

theorem corner_poly : PolyB (cornerF L ci) :=
  polyB_bodySig _ _ (by simp [Tm.CallsP,cornerBody,cornerFold_poly])

theorem maskFromBits_poly : PolyB (maskFromBitsF y ai) :=
  polyB_bodySig _ _ (by
    simp [Tm.CallsP,maskFromBitsBody,runF_P,mapEnvH_P,lookF_P])

end QecReliability.TensorMachine.RepairFL
