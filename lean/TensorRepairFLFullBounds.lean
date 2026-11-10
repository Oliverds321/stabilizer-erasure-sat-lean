import TensorRepairFLCountAllocationBounds
import TensorRepairFLAnchorTableBounds

/-! Resource envelope for the complete installed tensor repair callback. This
composes the actual count builder, exact physical anchors, and rational repair;
no hypothetical callback or numerical denominator magnitude is assumed. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)

variable (L : Lib) (ri : Indices) (ci : CanonicalIndices)
  (y : Trans.Control.IxR) (ai : AnchorIndices) (wi : WrapperIndices)

def fullCombinedBudget (D B N S C A R : ℕ) : ℕ :=
  C+A+R+100*S+100*(5*D+8*B+6)*(N+1)+1000

private def fullBodyExpanded : FL.Tm [TFullArg] TOutput :=
  .letE (.app (countDataF L wi)
    (.pair (.fst (.snd (.fst FL.Tm.v0))) (.snd FL.Tm.v0))) <|
  .letE (.app (anchorDataF L ci y ai)
    (.pair
      (.pair (.fst (.fst FL.Tm.v1))
        (.pair (.fst (.snd (.snd (.fst FL.Tm.v1))))
          (.pair (.fst (.snd (.snd (.snd (.fst FL.Tm.v1)))))
            (.fst (.snd (.snd (.snd (.snd (.fst FL.Tm.v1)))))))))
      (.fst (.snd (.fst FL.Tm.v1))))) <|
    .app (repairF L ri) (.pair FL.Tm.v1 FL.Tm.v0)

private theorem fullBody_expanded : fullBody L ri ci y ai wi =
    fullBodyExpanded L ri ci y ai wi := rfl

set_option maxHeartbeats 1000000 in
theorem full_resources_of_callees (D B N S C A R : ℕ)
    (x : TTensorX.den) (gs bs : List RawRatio)
    (hinput : (TFullArg.enc (x,gs,bs)).size ≤ S)
    (hdata : TableBound D B (countDataR x.2.1 gs bs))
    (hanchors : TableBound D B (anchorDataR (externalAnchorCtx x) x.2.1))
    (hdn : (countDataR x.2.1 gs bs).length ≤ N)
    (han : (anchorDataR (externalAnchorCtx x) x.2.1).length ≤ N)
    (hC : ResBound (countDataF L wi) (x.2.1,gs,bs) C)
    (hA : ResBound (anchorDataF L ci y ai) (externalAnchorCtx x,x.2.1) A)
    (hR : ResBound (repairF L ri)
      (countDataR x.2.1 gs bs,anchorDataR (externalAnchorCtx x) x.2.1) R) :
    ResBound (fullF L ri ci y ai wi) (x,gs,bs) (fullCombinedBudget D B N S C A R) := by
  have sd := table_encoded_size hdata
  have sa := table_encoded_size hanchors
  have sdN : (TTable.enc (countDataR x.2.1 gs bs)).size ≤ (5*D+8*B+6)*N+1 :=
    sd.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) hdn])
  have saN : (TTable.enc (anchorDataR (externalAnchorCtx x) x.2.1)).size ≤ (5*D+8*B+6)*N+1 :=
    sa.trans (by nlinarith [Nat.mul_le_mul_left (5*D+8*B+6) han])
  have sdN' : ((Ty.list TEntry).enc (countDataR x.2.1 gs bs)).size ≤ (5*D+8*B+6)*N+1 := sdN
  have saN' : ((Ty.list TEntry).enc (anchorDataR (externalAnchorCtx x) x.2.1)).size ≤ (5*D+8*B+6)*N+1 := saN
  rcases hC with ⟨cc,cd,cm⟩
  rcases hA with ⟨ac,ad,am⟩
  rcases hR with ⟨rc,rd,rm⟩
  simp only [ResBound,fullF,bodySig_cost,bodySig_depth,bodySig_msize,fullBody_expanded,fullBodyExpanded,tm_simp]
  repeat first | rw [countDataF_den] | rw [anchorDataF_den]
  simp only [TFullArg,TTensorX,Trans.Wire.TX,TAnchorCtx,externalAnchorCtx,
    Ty.enc_prod,Val.size_cons,max_le_iff] at *
  have hbudget : fullCombinedBudget D B N S C A R =
      C+A+R+100*S+100*((5*D+8*B+6)*N)+100*(5*D+8*B+6)+1000 := by
    unfold fullCombinedBudget
    ring
  simp only [hbudget,Trans.Wire.TRowsW,Trans.Wire.TCoordW,
    Trans.Control.TRowsP,Trans.Control.TCoord,Trans.Control.TGateP] at *
  simp only [Nat.mul_add,Nat.mul_one] at *
  omega

theorem tableBound_mono {D B E C : ℕ} {xs : RawTable}
    (h : TableBound D B xs) (hD : D ≤ E) (hB : B ≤ C) : TableBound E C xs := by
  intro x hx
  have hh := h x hx
  exact ⟨hh.1.trans hD,hh.2.1.trans hB,hh.2.2.trans hB⟩

def fullRatioBits (kd cd M B : ℕ) : ℕ := max (2*B+1) (G kd cd (2*M+1)+1)
def fullAnchorCost (kd cd kc cc M Q : ℕ) : ℕ :=
  anchorTableBudget M (G kd cd (2*M+1)+1)
    (dyadicBudget kd cd (2*M+1)+G kc cc (2*M+1)) Q

def fullUniformBudget (kd cd kc cc kr cr M B N S Q : ℕ) : ℕ :=
  fullCombinedBudget M (fullRatioBits kd cd M B) N S
    (countDataBudget M B N) (fullAnchorCost kd cd kc cc M Q)
    (repairBudget M (fullRatioBits kd cd M B) (G kr cr (2*M+1)) N)

/-- A fixed polynomial envelope for the COMPLETE compiled callback. M bounds
only structural input/key magnitudes; B bounds cached binary counters, N bounds
list lengths, and S bounds the actual encoded callback argument. All constants
are independent of runtime data, degrees, and the number of tensor classes. -/
theorem full_resources : ∃ kd cd kc cc kr cr, ∀ (M B N S : ℕ)
    (x : TTensorX.den) (gs bs : List RawRatio),
    mag TAnchorCtx (externalAnchorCtx x) ≤ M →
    (∀ key ∈ x.2.1, mag TKey key ≤ M) →
    CountListBound B gs → CountListBound B bs →
    x.2.1.length ≤ N → gs.length ≤ N → bs.length ≤ N →
    (TFullArg.enc (x,gs,bs)).size ≤ S →
    ResBound (fullF L ri ci y ai wi) (x,gs,bs)
      (fullUniformBudget kd cd kc cc kr cr M B N S x.2.1.length) := by
  obtain ⟨kd,cd,kc,cc,ha⟩ := anchorData_uniform L ci y ai
  obtain ⟨kr,cr,hkeys⟩ := key_resources L ri
  refine ⟨kd,cd,kc,cc,kr,cr,?_⟩
  intro M B N S x gs bs hctx hk hg hb hkn hgn hbn hsize
  obtain ⟨hanc,hancBits⟩ := ha M (externalAnchorCtx x) x.2.1 hctx hk
  have hdata := countDataR_bound M B x.2.1 gs bs hk hg hb
  have hdata' := tableBound_mono hdata le_rfl (Nat.le_max_left _ (G kd cd (2*M+1)+1))
  have hanc' := tableBound_mono hancBits le_rfl (Nat.le_max_right (2*B+1) _)
  have hBpos : 1 ≤ fullRatioBits kd cd M B := by
    unfold fullRatioBits
    omega
  have hdn : (countDataR x.2.1 gs bs).length ≤ N := by
    rw [countDataR_length]
    exact hkn
  have han := (anchorDataR_length (externalAnchorCtx x) x.2.1).trans hkn
  have hcmp : KeyResources L ri M (G kr cr (2*M+1)) := hkeys M
  have hrep := repair_resources L ri M (fullRatioBits kd cd M B) (G kr cr (2*M+1)) N
    hBpos hcmp (countDataR x.2.1 gs bs) (anchorDataR (externalAnchorCtx x) x.2.1)
    hdata' hanc' hdn han
  exact full_resources_of_callees L ri ci y ai wi M (fullRatioBits kd cd M B) N S _ _ _
    x gs bs hsize hdata' hanc' hdn han
    (countData_resources L wi M B N x.2.1 gs bs hk hg hb hkn hgn hbn) hanc hrep

end QecReliability.TensorMachine.RepairFL
