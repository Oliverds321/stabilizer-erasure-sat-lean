import TensorRepairFLFullBounds
import TensorRepairFLFullInstalled
import TensorMachineArgumentEnvelope

/-! A single polynomial envelope for the installed repair callback at every
reachable counting state, including the encoded size of the repaired output. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.TensorMachine.RepairResources
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Control
open Trans.Query.Bound Trans.BoundsQH Trans.BoundsRest
open RepairFL OracleCost OracleCost.WholeWrapperCandidate

private theorem ratio_bits_of_size (x : RawRatio) (B : ℕ)
    (h : (TR.enc x).size ≤ B) : RB B x := by
  have h1 := size_le_enc x.1
  have h2 := size_le_enc x.2
  change 1+(Enc.nat x.1).size+(Enc.nat x.2).size ≤ B at h
  exact ⟨by omega,by omega⟩

theorem countList_of_encoded {B : ℕ} {xs : List RawRatio}
    (h : (Ty.enc (.list TR) xs).size ≤ B) : CountListBound B xs := by
  intro x hx
  have hs := Ty.sz_mem_le TR hx
  apply ratio_bits_of_size x B
  exact (Nat.le_add_right _ 2).trans (hs.trans h)

private theorem encoded_snd_le (a b : Ty) (x : (a.prod b).den) :
    (b.enc x.2).size ≤ ((a.prod b).enc x).size := by
  rw [Ty.sz_prod]
  omega

private theorem encoded_fst_le (a b : Ty) (x : (a.prod b).den) :
    (a.enc x.1).size ≤ ((a.prod b).enc x).size := by
  rw [Ty.sz_prod]
  omega

private theorem encoded_callback_le (TX : Ty) (X : TX.den) (gs bs : List RawRatio) (S : ℕ)
    (hx : (TX.enc X).size ≤ S) (hg : ((Ty.list TRatio).enc gs).size ≤ S)
    (hb : ((Ty.list TRatio).enc bs).size ≤ S) :
    ((Ty.prod TX (.prod (.list TRatio) (.list TRatio))).enc (X,gs,bs)).size ≤ 3*S+10 := by
  rw [Ty.sz_prod,Ty.sz_prod]
  simp only [Prod.fst,Prod.snd]
  omega

theorem callback_input_parts (q r cell reps : ℕ) (X : ContextFL.TX.den) (s : Config) (S : ℕ)
    (h : (Ty.enc (TArg ContextFL.TX) (encCtx q r cell reps X,encCfg s)).size ≤ S) :
    CountListBound S s.goodTable ∧ CountListBound S s.badTable ∧
    s.goodTable.length ≤ S ∧ s.badTable.length ≤ S ∧
    (TFullArg.enc (X,s.goodTable,s.badTable)).size ≤ 3*S+10 := by
  have hflat := h
  simp only [encCtx,encCfg,Ty.sz_prod,TEnt,TR] at hflat
  have hg : (Ty.enc (.list TR) s.goodTable).size ≤ S := by
    simp only [TR]
    omega
  have hb : (Ty.enc (.list TR) s.badTable).size ≤ S := by
    simp only [TR]
    omega
  have hctx := (encoded_fst_le (TCtx ContextFL.TX) TCfg
    (encCtx q r cell reps X,encCfg s)).trans h
  have hX : (Ty.enc ContextFL.TX X).size ≤ S :=
    (encoded_snd_le (.prod .nat (.prod .nat (.prod .nat .nat))) ContextFL.TX
      (encCtx q r cell reps X)).trans hctx
  have hg' : (Ty.enc (.list TRatio) s.goodTable).size ≤ S := hg
  have hb' : (Ty.enc (.list TRatio) s.badTable).size ≤ S := hb
  have hgl := Ty.length_le_sz TR s.goodTable
  have hbl := Ty.length_le_sz TR s.badTable
  refine ⟨countList_of_encoded hg,countList_of_encoded hb,by omega,by omega,?_⟩
  exact encoded_callback_le TTensorX X s.goodTable s.badTable S hX hg' hb'

theorem callback_structural_parts (X : ContextFL.TX.den) (M : ℕ)
    (hX : mag ContextFL.TX X ≤ M) :
    mag TAnchorCtx (externalAnchorCtx X) ≤ M ∧
    (∀ key ∈ X.2.1, mag RepairFL.TKey key ≤ M) ∧ X.2.1.length ≤ M := by
  have hx : mag TTensorX X ≤ M := hX
  have hg : mag (.list RepairFL.TKey) X.2.1 ≤ M := by
    simp only [TTensorX,mag_prod] at hx
    omega
  constructor
  · simp only [TTensorX,TAnchorCtx,externalAnchorCtx,Trans.Wire.TX,
      Trans.Wire.TRowsW,Trans.Wire.TCoordW,Trans.Control.TRowsP,Trans.Control.TCoord,
      Trans.Control.TGateP,mag_prod,mag_nat] at hx ⊢
    omega
  constructor
  · intro key hkey
    have hm : mag RepairFL.TKey key+2 ≤ mag (.list RepairFL.TKey) X.2.1 := mag_mem RepairFL.TKey hkey
    exact ((Nat.le_add_right _ 2).trans hm).trans hg
  · have hl : X.2.1.length+1 ≤ mag (.list RepairFL.TKey) X.2.1 := mag_list_len RepairFL.TKey X.2.1
    exact ((Nat.le_add_right _ 1).trans hl).trans hg

end QecReliability.TensorMachine.RepairResources
