import TensorMachineInput
import LatentInputParserBounds

/-! Measured bounds for the runtime degree-list reader and full tensor parser.
The extent N includes both input bits and the explicit degree/grid size. -/

set_option autoImplicit false
namespace QecReliability.TensorMachine.ParserFL
open FL FL.Lib FL.Tm Trans.Wire SharedCircuit OracleCost
open Trans.Query Trans.Query.Bound Trans.BoundsRest
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize bodySig_den)

private theorem lookup_zero {Γ : List Ty} {t : Ty} (v : t.den) (ρ : Env Γ) :
    (Env.cons (t := t) v ρ).get Idx.zero = v := rfl
private theorem lookup_succ {Γ : List Ty} {t u : Ty} (v : u.den) (ρ : Env Γ)
    (i : Idx Γ t) : (Env.cons (t := u) v ρ).get (Idx.succ i) = ρ.get i := rfl

theorem degrees_bounds (L : Lib) (h : HIx) (p : LatentMachine.ParserFL.Indices)
    (idx : ℕ) (ds : List ℕ) (rest : List Bool) {N : ℕ}
    (hN : (degreesBits ds ++ rest).length ≤ N) (hlen : ds.length ≤ N)
    (hval : ∀ r ∈ ds, r ≤ N) :
    (degreesF L h p idx).cost (degreesBits ds ++ rest) ≤ 2000*(N+2)^3 ∧
    (degreesF L h p idx).depth (degreesBits ds ++ rest) ≤ 30*N+100 ∧
    (degreesF L h p idx).msize (degreesBits ds ++ rest) ≤ 2000*(N+2)^2 := by
  have htail : (ds.flatMap QueryCodec.natHeader ++ rest).length ≤ N := by
    simp only [degreesBits,List.length_append] at hN ⊢
    omega
  have eh : (hdrF L h).den (degreesBits ds ++ rest) =
      (ds.length,ds.flatMap QueryCodec.natHeader ++ rest) := by
    rw [hdrF_den]
    simp only [degreesBits,List.append_assoc,hdr_natHeader]
  obtain ⟨hc,hd,hm⟩ := hdr_le L h (Q:=N) _ hN
  obtain ⟨oc,od,om⟩ := LatentMachine.ParserFL.outputs_bounds L h p ds rest htail hlen hval
  have hpow : (N+2)^2 ≤ (N+2)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨?_,?_,?_⟩
  · dsimp only [degreesF,bodySig_cost,degreesBody,Tm.cost,Tm.den,Env.one,lookup_zero]
    rw [eh]
    nlinarith
  · dsimp only [degreesF,bodySig_depth,degreesBody,Tm.depth,Tm.den,Env.one,lookup_zero]
    rw [eh]
    try dsimp only
    omega
  · dsimp only [degreesF,bodySig_msize,degreesBody,Tm.msize,Tm.den,Env.one,lookup_zero]
    rw [eh]
    simp only [max_le_iff]
    (repeat' apply And.intro) <;> nlinarith

private theorem legacy_result_size (L : Lib) (h : HIx) (wp : PIx)
    (p : LatentMachine.ParserFL.Indices) (bs : List Bool) :
    (Ty.enc LatentMachine.ParserFL.ParsedTy ((LatentMachine.ParserFL.parseF L h wp p).den bs)).size ≤
      (LatentMachine.ParserFL.parseF L h wp p).msize bs := by
  dsimp only [LatentMachine.ParserFL.ParsedTy,LatentMachine.ParserFL.parseF,bodySig_den,bodySig_msize,
    LatentMachine.ParserFL.parseBody,Tm.msize,Tm.den,Env.one,lookup_zero,lookup_succ]
  omega

theorem parse_composition (L : Lib) (h : HIx) (wp : PIx)
    (p : LatentMachine.ParserFL.Indices) (di pi : ℕ) (ds : List ℕ) (rest : List Bool) :
    let F := degreesF L h p di
    let G := LatentMachine.ParserFL.parseF L h wp p
    let bs := degreesBits ds ++ rest
    (parseF L h wp p di pi).cost bs ≤ F.cost bs + G.cost rest + 20 ∧
    (parseF L h wp p di pi).depth bs ≤ F.depth bs + G.depth rest + 10 ∧
    (parseF L h wp p di pi).msize bs ≤ F.msize bs + 2*G.msize rest +
      (Ty.enc (.list .nat) ds).size + (Ty.enc (.list .bool) rest).size + 10 := by
  dsimp only
  have eh : (degreesF L h p di).den (degreesBits ds ++ rest) = (ds,rest) := by
    rw [degreesF_den,degreesR_degreesBits]
  have hz := legacy_result_size L h wp p rest
  refine ⟨?_,?_,?_⟩
  · dsimp only [parseF,bodySig_cost,parseBody,Tm.cost,Tm.den,Env.one,lookup_zero,lookup_succ]
    rw [eh]
    try dsimp only
    omega
  · dsimp only [parseF,bodySig_depth,parseBody,Tm.depth,Tm.den,Env.one,lookup_zero,lookup_succ]
    rw [eh]
    try dsimp only
    omega
  · dsimp only [parseF,bodySig_msize,parseBody,Tm.msize,Tm.den,Env.one,lookup_zero,lookup_succ]
    rw [eh]
    dsimp only
    simp only [LatentMachine.ParserFL.ParsedTy,Ty.sz_prod] at hz
    simp only [Ty.sz_prod,max_le_iff]
    (repeat' apply And.intro) <;> omega

end QecReliability.TensorMachine.ParserFL
