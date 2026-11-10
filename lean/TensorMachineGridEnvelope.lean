import TensorMachineGridCost
import TensorMachineGridSpace
import LatentEndpointInputBudget
import Trans.BoundsRest.Compile

/-! One fixed polynomial bounds the actual Cartesian-grid constructor when the
input extent charges class count, total causes and explicit grid cardinality. -/

set_option autoImplicit false
namespace QecReliability.TensorMachine.GridFL
open FL FL.Lib Trans.Wire Trans.Query.Bound Trans.BoundsQH Trans.BoundsRest

def gridBudget (k c N : ℕ) : ℕ := G k c (100*(N+2)^3)+10000*(N+2)^3

theorem gridBudget_polynomial (k c : ℕ) : Assembly.PolyBounded (gridBudget k c) := by
  have h := G_comp_pb k c (show Assembly.PolyBounded (fun N => 100*(N+2)^3) by poly_bounded)
  unfold gridBudget
  poly_bounded

set_option maxHeartbeats 1000000 in
theorem grid_resources (L : Lib) (i : Indices) : ∃ k c, ∀ (ds : List ℕ) (N : ℕ),
    ds.sum ≤ N → ds.length ≤ N → slots ds ≤ N →
    (gridF L i).cost ds ≤ gridBudget k c N ∧
    (gridF L i).depth ds ≤ gridBudget k c N ∧
    (gridF L i).msize ds ≤ gridBudget k c N ∧
    (Ty.enc Table (grid ds)).size ≤ gridBudget k c N := by
  obtain ⟨k,c,hms⟩ := grid_msize_bound L i
  refine ⟨k,c,?_⟩
  intro ds N hsum hlen hslots
  have hc := grid_cost_bound L i ds
  have hd := grid_depth_bound L i ds
  have hm := hms ds
  have hs := grid_encoding_size ds
  have hR : tableMagnitudeBound ds.sum ds.length (slots ds) ≤ N*(N*(N+1)+2)+1 := by
    unfold tableMagnitudeBound
    gcongr
  have hR' : N*(N*(N+1)+2)+1 ≤ 10*(N+2)^3 := by nlinarith
  have harg : ds.sum+tableMagnitudeBound ds.sum ds.length (slots ds)+1 ≤ 100*(N+2)^3 := by
    have hsmall : N+1 ≤ (N+2)^3 := by nlinarith
    omega
  have hg := G_mono (k:=k) (c:=c) le_rfl le_rfl harg
  have hcost : ds.length*(1000*(ds.sum+slots ds+2)^2+12) ≤ N*(1000*(2*N+2)^2+12) := by
    gcongr
    omega
  have hsize : slots ds*(ds.length*(4*ds.sum+2)+2) ≤ N*(N*(4*N+2)+2) := by
    gcongr
  have hpoly : N*(1000*(2*N+2)^2+12)+17+100*N+100*(N*(N+1)+2)+100 ≤
      10000*(N+2)^3 := by nlinarith
  unfold gridBudget
  refine ⟨?_,?_,?_,?_⟩
  · omega
  · have hg0 := Nat.zero_le (G k c (100*(N+2)^3)); nlinarith
  · have hrest : 10*ds.sum+5*ds.length+5*tableMagnitudeBound ds.sum ds.length (slots ds)+100 ≤
        10000*(N+2)^3 := by nlinarith
    omega
  · have hg0 := Nat.zero_le (G k c (100*(N+2)^3)); nlinarith

end QecReliability.TensorMachine.GridFL
