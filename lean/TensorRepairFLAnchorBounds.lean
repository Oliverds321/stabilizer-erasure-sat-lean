import TensorRepairFLCanonicalBounds
import TensorRepairFLBitBounds

/-! Polynomial bit-resource bounds for exact dyadic physical anchors. The
power-of-two denominator is bounded by binary length, never by its magnitude. -/
set_option autoImplicit false
namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Tm FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH Trans.BoundsRest Trans.Control

variable (L : Lib) (ci : CanonicalIndices) (y : IxR) (ai : AnchorIndices)

/-- The part preceding the final dyadic denominator construction. -/
def dyadicHeadBody : Tm [.prod TAnchorCtx TKey] .nat :=
  .letE (.app (bitsF L ci y.append) (.pair (.fst (.fst v0)) (.snd v0))) <|
  .letE (.app (maskFromBitsF y ai) (.pair v0 (.snd (.snd (.snd (.fst v1)))))) <|
  .app (ambF y)
    (.pair (.fst (.snd (.fst v2))) (.pair (.fst (.snd (.snd (.fst v2)))) v0))

def dyadicPowerBody {Γ : List Ty} : Tm (.nat::Γ) TRatio :=
  .pair (.lit (1 : ℕ))
    (.app (foldlF (dblF y) y.dblFold) (.pair (.lit (1 : ℕ)) (.app (rangeF y.range) v0)))

theorem dyadicHead_poly : PolyB (bodySig 0 (dyadicHeadBody L ci y ai)) :=
  polyB_bodySig _ _ (by
    simp [Tm.CallsP,dyadicHeadBody,bits_poly,maskFromBits_poly,ambF_P])

theorem dyadicPower_bounds {Γ : List Ty} (a : ℕ) (ρ : Env Γ) :
    (dyadicPowerBody y).cost (.cons a ρ) ≤ 100*((a+1)*(a+1))+100 ∧
    (dyadicPowerBody y).depth (.cons a ρ) ≤ 3*a+10 ∧
    (dyadicPowerBody y).msize (.cons a ρ) ≤ 30*((a+1)*(a+1))+100 := by
  have h := restT_bounds y a (Env.one (((0,0,[],([],[])),false) : TEArg.den))
  simpa only [dyadicPowerBody,restT,tm_simp] using h

theorem dyadic_cost_split (x : (Ty.prod TAnchorCtx TKey).den) :
    (dyadicF L ci y ai).cost x =
      (dyadicHeadBody L ci y ai).cost (Env.one x) +
      (dyadicPowerBody y).cost (.cons ((dyadicHeadBody L ci y ai).den (Env.one x)) (Env.one x))+3 := by
  simp only [dyadicF,bodySig_cost,dyadicBody,dyadicHeadBody,dyadicPowerBody,tm_simp,Nat.add_assoc]
  omega

theorem dyadic_depth_split (x : (Ty.prod TAnchorCtx TKey).den) :
    (dyadicF L ci y ai).depth x =
      max ((dyadicHeadBody L ci y ai).depth (Env.one x))
      ((dyadicPowerBody y).depth (.cons ((dyadicHeadBody L ci y ai).den (Env.one x)) (Env.one x)))+1 := by
  simp only [dyadicF,bodySig_depth,dyadicBody,dyadicHeadBody,dyadicPowerBody,tm_simp,max_assoc]

theorem dyadic_msize_split (x : (Ty.prod TAnchorCtx TKey).den) :
    (dyadicF L ci y ai).msize x =
      max ((dyadicHeadBody L ci y ai).msize (Env.one x))
      ((dyadicPowerBody y).msize (.cons ((dyadicHeadBody L ci y ai).den (Env.one x)) (Env.one x))) := by
  simp only [dyadicF,bodySig_msize,dyadicBody,dyadicHeadBody,dyadicPowerBody,tm_simp,max_assoc]

theorem dyadicHead_den (ctx : AnchorCtx) (key : Key) :
    (dyadicHeadBody L ci y ai).den (Env.one (ctx,key)) =
      Trans.Control.RankP.ambP ctx.2.1 ctx.2.2.1
        (maskFromBitsR (canonicalBits ctx.1 key) ctx.2.2.2) := by
  simp only [dyadicHeadBody,tm_simp]
  rw [bitsF_den,maskFromBitsF_den,amb_den]

def dyadicBudget (k c m : ℕ) : ℕ := 200*((G k c m+1)*(G k c m+1))+200

/-- Uniform compiled cost/depth/space and denominator BIT length. -/
theorem dyadic_resources : ∃ k c, ∀ (ctx : AnchorCtx) (key : Key),
    ResBound (dyadicF L ci y ai) (ctx,key)
      (dyadicBudget k c (mag (.prod TAnchorCtx TKey) (ctx,key))) ∧
    RB (G k c (mag (.prod TAnchorCtx TKey) (ctx,key))+1) (dyadicR ctx key) := by
  obtain ⟨k,c,h⟩ := dyadicHead_poly L ci y ai
  refine ⟨k,c,?_⟩
  intro ctx key
  obtain ⟨hcost,hdepth,hspace,hvalue⟩ := h (ctx,key)
  let a := (dyadicHeadBody L ci y ai).den (Env.one (ctx,key))
  have hv : a ≤ G k c (mag (.prod TAnchorCtx TKey) (ctx,key)) := hvalue
  obtain ⟨r1,r2,r3⟩ := dyadicPower_bounds (Γ := [.prod TAnchorCtx TKey]) y a (Env.one (ctx,key))
  have hb := endpoint_arith hcost hdepth hspace hv r1 r2 r3
  constructor
  · rw [ResBound,dyadic_cost_split,dyadic_depth_split,dyadic_msize_split]
    dsimp [dyadicBudget]
    dsimp [a] at hb
    exact ⟨by simpa only [Nat.add_assoc] using hb.1,
      hb.2.1.trans (by nlinarith),hb.2.2⟩
  · have ha : (2^a).size ≤ a+1 := by
      rw [Nat.size_le]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hd : dyadicR ctx key = (1,2^a) := by
      dsimp [a]
      rw [dyadicHead_den]
      rfl
    rw [hd]
    simp only [RB,Nat.size_one]
    exact ⟨Nat.succ_le_succ (Nat.zero_le _),ha.trans (Nat.add_le_add_right hv 1)⟩

end QecReliability.TensorMachine.RepairFL
