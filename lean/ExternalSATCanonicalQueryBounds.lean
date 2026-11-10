import ExternalSATTraversalBudgetHierarchy
import ExternalSATQueryCanonicalController
import ExternalSATRawQueryBounds

/-! Polynomial time for the SAME complete binary-query-to-canonical-bytes
controller. The final reversal is charged using the proved exact byte endpoint,
not an assumed output bound. Output size is not substituted for visited space. -/
namespace QecReliability.ExternalSATBridge.CanonicalQueryBounds
open QecReliability.OracleCost
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open TraversalBudgetHierarchy

theorem canonical_length_le (q : SATRequest) :
    (Encoding.encodeCNF (FormulaBridge.formula q.formula)).length ≤
      64 * (RawQueryBounds.extent q + 1) ^ 2 := by
  obtain ⟨hv, _, _, hm⟩ := RawQueryBounds.query_sizes q
  have hc := FormulaBridge.formula_card_le q.formula
  have he := Encoding.formulaBitLength_upper (FormulaBridge.formula q.formula)
    (FormulaBridge.formula_width q.formula q.width)
  have hp := Nat.mul_le_mul
    (show 4 + (8 * q.varCount + 8) * 3 ≤ 24 * RawQueryBounds.extent q + 28 from by omega)
    (hc.trans hm)
  change (Encoding.encodeCNF (FormulaBridge.formula q.formula)).length ≤ _ at he
  nlinarith

theorem accumulator_length_le (q : SATRequest) :
    (CanonicalRawController.accumulator q.varCount (CanonicalBytes.rawClauses q.formula)).length ≤
      64 * (RawQueryBounds.extent q + 1) ^ 2 := by
  have hlen := congrArg List.length (CanonicalBytes.output_eq q.formula q.width)
  simp only [CanonicalRawController.output, List.length_append, List.length_reverse,
    List.length_singleton] at hlen
  have hb := canonical_length_le q
  omega

theorem square_le_fifth (R : ℕ) : (R + 1) ^ 2 ≤ (R + 1) ^ 5 := by
  calc
    (R + 1) ^ 2 = (R + 1) ^ 2 * 1 := by omega
    _ ≤ (R + 1) ^ 2 * (R + 1) ^ 3 := Nat.mul_le_mul_left _ (one_le_power R 3)
    _ = (R + 1) ^ 5 := by ring

theorem cube_le_fifth (R : ℕ) : (R + 1) ^ 3 ≤ (R + 1) ^ 5 := by
  calc
    (R + 1) ^ 3 = (R + 1) ^ 3 * 1 := by omega
    _ ≤ (R + 1) ^ 3 * (R + 1) ^ 2 := Nat.mul_le_mul_left _ (one_le_power R 2)
    _ = (R + 1) ^ 5 := by ring

theorem raw_controller_time_le (q : SATRequest) :
    CanonicalRawController.timeBound q.varCount (CanonicalBytes.rawClauses q.formula) ≤
      262144 * (RawQueryBounds.extent q + 1) ^ 5 := by
  obtain ⟨hv, hs, _, hm⟩ := RawQueryBounds.query_sizes q
  have hmr : (CanonicalBytes.rawClauses q.formula).length ≤ RawQueryBounds.extent q := by
    simpa only [CanonicalBytes.rawClauses, List.length_map] using hm
  have hh := header_le q.varCount (RawQueryBounds.extent q) hv hs
  have hb := boundCost_le q.varCount (RawQueryBounds.extent q) hv hs
  have hr := root_visit_le q.varCount (RawQueryBounds.extent q) (CanonicalBytes.rawClauses q.formula)
    hv hmr (QueryCanonicalController.raw_width q)
    (fun c hc n hn => (QueryCanonicalController.raw_code_bound q c hc n hn).le)
  have ho := outer_range_le q.varCount (RawQueryBounds.extent q) (CanonicalBytes.rawClauses q.formula) hv hmr
  have hclear := clear_final_code_le q.varCount (RawQueryBounds.extent q) hv
  have ha := accumulator_length_le q
  have h2 := square_le_fifth (RawQueryBounds.extent q)
  have h1 := one_le_power (RawQueryBounds.extent q) 5
  have hlin := base_le_power (RawQueryBounds.extent q) 4
  norm_num only at hlin
  dsimp only [CanonicalRawController.timeBound, CanonicalRawController.boundCost]
  omega

/-- R is dimension plus actual native binary input length. The engine is not
called: this is the concrete, canonical, whole-query frontend alone. -/
theorem timeBound_le (q : SATRequest) :
    QueryCanonicalController.timeBound q ≤ 524288 * (RawQueryBounds.extent q + 1) ^ 5 := by
  have hf := RawQueryBounds.timeBound_polynomial q
  have hc := raw_controller_time_le q
  obtain ⟨_, hv, hm, _⟩ := RawQueryBounds.query_sizes q
  have h3 := cube_le_fifth (RawQueryBounds.extent q)
  have h1 := one_le_power (RawQueryBounds.extent q) 5
  have hlin := base_le_power (RawQueryBounds.extent q) 4
  norm_num only at hlin
  dsimp only [QueryCanonicalController.timeBound]
  omega

theorem source_query (q : SATRequest) :
    BitProgram.RunsIn QueryCanonicalController.program
      (524288 * (RawQueryBounds.extent q + 1) ^ 5)
      (BitProgram.initial QueryCanonicalController.program (QueryCodec.encode q))
      ((QueryCanonicalController.ready q).withPC none) := by
  obtain ⟨n, hn, ht⟩ := QueryCanonicalController.source_query q
  exact ⟨n, hn.trans (timeBound_le q), ht⟩

theorem primitive_query (q : SATRequest) :
    ∃ steps final,
      Computation.Trace QueryCanonicalController.primitive.step steps
        (QueryCanonicalController.primitive.init (QueryCodec.encode q)) final ∧
      steps ≤ 7 * (524288 * (RawQueryBounds.extent q + 1) ^ 5) ∧
      (∀ i : Fin 20, final.tapes i =
        Turing.Tape.mk₁ (((QueryCanonicalController.ready q).stacks i).map some)) := by
  obtain ⟨n, final, ht, hn, hout⟩ := QueryCanonicalController.primitive_query q
  exact ⟨n, final, ht, hn.trans (Nat.mul_le_mul_left 7 (timeBound_le q)), hout⟩

end QecReliability.ExternalSATBridge.CanonicalQueryBounds
#print axioms QecReliability.ExternalSATBridge.CanonicalQueryBounds.accumulator_length_le
#print axioms QecReliability.ExternalSATBridge.CanonicalQueryBounds.timeBound_le
#print axioms QecReliability.ExternalSATBridge.CanonicalQueryBounds.primitive_query
