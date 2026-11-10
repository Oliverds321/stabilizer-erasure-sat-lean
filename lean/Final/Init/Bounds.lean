import Final.Init.Top
import Install.Callees

/-!
# Final.Init.Bounds: the init budget of the installed program

**`initBounds : Install.InitBounds hD hd A`**: one polynomial envelope `P` (in `L = paperL`)
bounds cost, depth and msize of `theInit = initTopF wL wH wP wA yI paramsFn base den` at every
machine input (positive instances and `n = 0`), and the input's encoded size.

From `top_le` with `Q = L + coinPoly sc L` (`coinBits_le_paperL`, `paperLength_components`,
`budget_parameters`); the callee bounds are `seedB_on` with `BoundsQH.paramsF_on` and
`initF_P`; `initPoly` is `PolyBounded` (`G_comp_pb`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Final.Init
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH (G FnBAt PolyB)
open QecReliability.Trans.Bounds (coinPoly)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Install

/-- The init envelope as a function of `L`. -/
def initPoly (Ks Cs Ki Ci sc L : ℕ) : ℕ := topB Ks Cs Ki Ci (L + coinPoly sc L)

theorem initPoly_pb (Ks Cs Ki Ci sc : ℕ) : Assembly.PolyBounded (initPoly Ks Cs Ki Ci sc) := by
  have hQ : Assembly.PolyBounded (fun L => L + coinPoly sc L) := by
    have : Assembly.PolyBounded (fun L => L + (6 * L + 5) * (sc * (2 * L))) := by poly_bounded
    exact this
  have g1 : Assembly.PolyBounded (fun L => G Ks Cs (3 * (L + coinPoly sc L))) :=
    Trans.BoundsRest.G_comp_pb Ks Cs (by poly_bounded)
  have g2 : Assembly.PolyBounded (fun L => G Ki Ci (7 * (L + coinPoly sc L) + 5)) :=
    Trans.BoundsRest.G_comp_pb Ki Ci (by poly_bounded)
  show Assembly.PolyBounded (fun L => 7000 * (L + coinPoly sc L + 2) ^ 4 +
    4000 * ((2 * (L + coinPoly sc L) + 10) * (2 * (L + coinPoly sc L) + 10)) +
    20 * G Ks Cs (3 * (L + coinPoly sc L)) + 20 * G Ki Ci (7 * (L + coinPoly sc L) + 5) +
    10 * zc + 1000)
  poly_bounded

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t) (A : CertifiedParity (512*t) (64*t) t)

theorem seed_inst : ∃ K C, ∀ q, FnBAt (G K C)
    (Trans.Wire.seedBF wL wA paramsFn (data hD hd A).base (data hD hd A).den) q := by
  obtain ⟨kp, cp, hp⟩ := Trans.BoundsQH.paramsF_on hL.range hL.mul hL.le hL.succ hL.mul I.dyS
    I.dyF hL.le hL.succ hL.mul ampI.cs ampI.csf hL.mul I.pwS I.pwF I.params
    (data hD hd A).base (data hD hd A).den
  exact seedB_on wL wA paramsFn _ _ hp

theorem paper_facts {n : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ) (ha : 0 < a)
    (hc : 0 < c) :
    (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d).length ≤
        paperL rows a b c d ∧ n ≤ paperL rows a b c d ∧
      rows.length + rowIncidences rows ≤ paperL rows a b c d ∧
      a.size + b.size + c.size + d.size ≤ paperL rows a b c d ∧
      rationalRepetitionBudget (2 * (n + 1)) c d ≤ 3 * paperL rows a b c d + 3 := by
  obtain ⟨h1, -, h3, -, h5⟩ := InputEncoding.paperLength_components rows
    (ZeroLengthDispatch.iidProgram n) a b c d
  obtain ⟨-, -, -, h4, -⟩ := InputEncoding.budget_parameters rows
    (ZeroLengthDispatch.iidProgram n) a b c d ha hc
  have e : paperL rows a b c d =
      n + n + (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d).length :=
    rfl
  have e' : InputEncoding.paperLength rows (ZeroLengthDispatch.iidProgram n) a b c d =
      paperL rows a b c d := rfl
  rw [e'] at h1 h3 h4 h5
  refine ⟨by omega, h1, h3, h5, by omega⟩

/-- **The init budget of the installed program.** -/
theorem initBounds : InitBounds hD hd A := by
  obtain ⟨Ks, Cs, hs⟩ := seed_inst hD hd A
  obtain ⟨Ki, Ci, hi⟩ := initF_P yI
  obtain ⟨P, hP⟩ := (initPoly_pb Ks Cs Ki Ci (seedConstant hD hd A)).envelope
  refine ⟨P, P, P, ?_, ?_⟩
  · intro a b c d k rows coins ha _ hc _
    obtain ⟨f1, f2, f3, f4, f5⟩ := paper_facts rows a b c d ha hc
    have hcoin : coinBits hD hd A c d (k + 1) ≤
        coinPoly (seedConstant hD hd A) (paperL rows a b c d) :=
      coinBits_le_paperL hD hd A rows a b c d ha hc
    have hlen : (machineInput rows a b c d (List.ofFn coins)).length =
        (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram (k + 1)) a b c d).length +
          coinBits hD hd A c d (k + 1) := by
      simp only [machineInput, List.length_append, List.length_ofFn]
    obtain ⟨k1, k2, k3, k4⟩ := top_le wL wH wP wA yI paramsFn (data hD hd A).base
      (data hD hd A).den hs hi (Q := paperL rows a b c d +
        coinPoly (seedConstant hD hd A) (paperL rows a b c d)) rows a b c d (List.ofFn coins)
      (machineInput rows a b c d (List.ofFn coins)) rfl (by omega) (by omega) (by omega)
      (by omega) (by omega)
    have hb := hP (paperL rows a b c d)
    exact ⟨k1.trans hb, k2.trans hb, k3.trans hb, k4.trans hb⟩
  · intro rows a b c d ha _ hc _
    obtain ⟨f1, f2, f3, f4, f5⟩ := paper_facts rows a b c d ha hc
    have hlen : (machineInput rows a b c d []).length =
        (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram 0) a b c d).length := by
      simp only [machineInput, List.length_append, List.length_nil, Nat.add_zero]
    obtain ⟨k1, k2, k3, k4⟩ := top_le wL wH wP wA yI paramsFn (data hD hd A).base
      (data hD hd A).den hs hi (Q := paperL rows a b c d +
        coinPoly (seedConstant hD hd A) (paperL rows a b c d)) rows a b c d []
      (machineInput rows a b c d []) rfl (by omega) (by omega) (by omega) (by omega) (by omega)
    have hb := hP (paperL rows a b c d)
    exact ⟨k1.trans hb, k2.trans hb, k3.trans hb, k4.trans hb⟩

end QecReliability.Final.Init
