import Trans.Bounds.Output
import Trans.Bounds.SizeCfg

/-!
# Trans.Bounds.Size: the size bridge

At every reachable state of an instance, the encoded loop state
`instEnc … s = (TArg TX).enc (ictx …, encCfg s)` has size at most a polynomial in
`L = paperL rows a b c d` (**`instEnc_size_le`**):

`(instEnc … s).size ≤ statePoly G density sc L`, with `G = gateConstant hD hd A`,
`sc = seedConstant hD hd A` (constants of the fixed certificate) and

* `statePoly G density sc L = ctxPoly sc L + 10 · retainedPolynomial G density L + 401`;
* `ctxPoly sc L = 300 (L+1)^3 + 8 · coinPoly sc L + 100`, `coinPoly sc L = (6L+5)(sc · 2L)`.

The configuration part is `SizeCfg.sz_encCfg_le` + the macro bound on `representedBits`
(`Assembly.instReachable_bounds`); the context part (`sz_ictx_le`) uses the input-length
accounting `budget_parameters`/`paperLength_components` and `coinBits_le_paperL`.
The cell budget `B = rationalCellBudget a b` enters only through its bit length
(`B.size ≤ 2L + 8`), never through its value.

`statePoly_mono`: the bound is monotone in `L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Bounds
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Control (TR encCfg encCtx TArg TCfg TCtx)
open QecReliability.Trans.Wire (TX instX instEnc wireX TRowsW WProg seedB)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

/-! ## Polynomials -/

def coinPoly (sc L : ℕ) : ℕ := (6 * L + 5) * (sc * (2 * L))

def ctxPoly (sc L : ℕ) : ℕ := 300 * (L + 1) ^ 3 + 8 * coinPoly sc L + 100

def statePoly (G density sc L : ℕ) : ℕ :=
  ctxPoly sc L + 10 * InputEncoding.retainedPolynomial G density L + 401

theorem coinPoly_mono (sc : ℕ) : Monotone (coinPoly sc) := by
  intro x y h
  unfold coinPoly
  exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))

theorem ctxPoly_mono (sc : ℕ) : Monotone (ctxPoly sc) := by
  intro x y h
  unfold ctxPoly
  have h1 := Nat.pow_le_pow_left (show x + 1 ≤ y + 1 by omega) 3
  have h2 := coinPoly_mono sc h
  omega

theorem retained_mono (G density : ℕ) : Monotone (InputEncoding.retainedPolynomial G density) := by
  intro x y h
  rw [InputEncoding.retainedPolynomial_expansion, InputEncoding.retainedPolynomial_expansion]
  gcongr

theorem statePoly_mono (G density sc : ℕ) : Monotone (statePoly G density sc) := by
  intro x y h
  unfold statePoly
  have h1 := ctxPoly_mono sc h
  have h2 := retained_mono G density h
  omega

theorem cube_lin (L : ℕ) : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) (L + 1)

theorem sq_le_cube (L : ℕ) : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)

theorem cube_quad (L : ℕ) : (L + 1) * (6 * (L + 1)) ≤ 10 * (L + 1) ^ 3 := by
  have h := sq_le_cube L
  have e : (L + 1) * (6 * (L + 1)) = 6 * (L + 1) ^ 2 := by ring
  omega

theorem cube_rows (L : ℕ) : (L + 1) * ((L + 1) * (10 * (L + 1)) + 2 * (L + 1)) ≤ 30 * (L + 1) ^ 3 := by
  have h := sq_le_cube L
  have e : (L + 1) * ((L + 1) * (10 * (L + 1)) + 2 * (L + 1)) = 10 * (L + 1) ^ 3 + 2 * (L + 1) ^ 2 := by
    ring
  omega

/-! ## Pieces of the context -/

theorem sz_nat_le_self (n : ℕ) : (Ty.enc .nat n).size ≤ 4 * n + 1 := by
  have h1 := Ty.sz_nat_le n
  have h2 := NatSize.size_le_self n
  omega

theorem sz_range_le (n : ℕ) : (Ty.enc (.list .nat) (List.range n)).size ≤ n * (4 * n + 2) + 1 := by
  have := Ty.sz_list_le .nat (List.range n) (4 * n + 1) (fun i hi => by
    have h1 := sz_nat_le_self i
    have h2 := List.mem_range.mp hi
    omega)
  simpa using this

theorem sz_coord_le {n : ℕ} (x : PauliCoord n) :
    (Ty.enc Wire.TCoordW (Query.encCoord x)).size ≤ 4 * n + 5 := by
  rcases x with i | i <;>
  · have h1 := sz_nat_le_self i.val
    have h2 := i.isLt
    have h3 := Ty.sz_bool_le false
    have h4 := Ty.sz_bool_le true
    simp only [Query.encCoord]
    rw [shape2]
    omega

theorem sz_row_le {n : ℕ} (row : List (PauliCoord n)) (M : ℕ) (hM : row.length ≤ M) :
    (Ty.enc (.list Wire.TCoordW) (row.map Query.encCoord)).size ≤ M * (4 * n + 6) + 1 := by
  have h := Ty.sz_list_le Wire.TCoordW (row.map Query.encCoord) (4 * n + 5) (fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
    exact sz_coord_le x)
  rw [List.length_map, show 4 * n + 5 + 1 = 4 * n + 6 by omega] at h
  have := Nat.mul_le_mul_right (4 * n + 6) hM
  omega

theorem length_le_rowIncidences {n : ℕ} {rows : List (List (PauliCoord n))}
    {row : List (PauliCoord n)} (h : row ∈ rows) : row.length ≤ rowIncidences rows := by
  unfold rowIncidences
  exact List.le_sum_of_mem (List.mem_map_of_mem h)

theorem sz_rows_le {n : ℕ} (rows : List (List (PauliCoord n))) :
    (Ty.enc TRowsW (Query.encRows rows)).size ≤
      rows.length * (rowIncidences rows * (4 * n + 6) + 2) + 1 := by
  have h := Ty.sz_list_le (.list Wire.TCoordW) (Query.encRows rows)
    (rowIncidences rows * (4 * n + 6) + 1) (fun y hy => by
      obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hy
      exact sz_row_le row _ (length_le_rowIncidences hr))
  simp only [Query.encRows, List.length_map] at h
  exact h

/-! ## The context -/

/-- Shape of the encoded context (generic in the hash constants `base den`). -/
theorem sz_ctx_split (base den q r B m : ℕ) {n : ℕ} (rows : List (List (PauliCoord n)))
    (coins : List Bool) :
    (Ty.enc (TCtx TX) (encCtx q r B m (wireX base den rows coins))).size =
      ((Ty.enc .nat q).size + (Ty.enc .nat r).size + (Ty.enc .nat B).size +
        (Ty.enc .nat m).size + 3) +
      ((Ty.enc .nat n).size + (Ty.enc TRowsW (Query.encRows rows)).size +
        (Ty.enc WProg (Query.encProg (ZeroLengthDispatch.iidProgram n))).size +
        (Ty.enc .nat (keySize n n)).size + (Ty.enc .nat (seedB base den (keySize n n))).size +
        (Ty.enc (.list .bool) coins).size + 5) + 1 := by
  simp only [encCtx, wireX]
  rw [shape2, shape4, shape6]

theorem sz_prog_iid (n : ℕ) :
    (Ty.enc WProg (Query.encProg (ZeroLengthDispatch.iidProgram n))).size =
      (Ty.enc (.list .nat) (List.range n)).size + 2 := by
  rw [Wire.encProg_iid, shape2, Ty.sz_list_nil]
  omega

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : CertifiedParity (512*t) (64*t) t)

theorem seedB_le_coinBits (c d k : ℕ) :
    seedB (data hD hd A).base (data hD hd A).den (keySize (k+1) (k+1)) ≤
      coinBits hD hd A c d (k+1) := by
  rw [Wire.seedB_positive]
  have e : coinBits hD hd A c d (k+1) = (2 * macroM c d k + 1) *
      CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k) := rfl
  rw [e]
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- **Size bridge, context part.** -/
theorem sz_ictx_le {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (ha : 0 < a) (hc : 0 < c) :
    (Ty.enc (TCtx TX) (ictx hD hd A a b c d k rows coins)).size ≤
      ctxPoly (seedConstant hD hd A) (paperL rows a b c d) := by
  obtain ⟨hn, hq, hr, hm, hB⟩ := InputEncoding.budget_parameters rows
    (ZeroLengthDispatch.iidProgram (k+1)) a b c d ha hc
  obtain ⟨-, -, hrows, -, -⟩ := InputEncoding.paperLength_components rows
    (ZeroLengthDispatch.iidProgram (k+1)) a b c d
  have hcoin := coinBits_le_paperL hD hd A rows a b c d ha hc
  have hSB := seedB_le_coinBits hD hd A c d k
  generalize hL : paperL rows a b c d = L at hcoin ⊢
  have hLdef : InputEncoding.paperLength rows (ZeroLengthDispatch.iidProgram (k+1)) a b c d = L :=
    hL
  rw [hLdef] at hn hq hr hm hB hrows
  have hcoin' : coinBits hD hd A c d (k+1) ≤ coinPoly (seedConstant hD hd A) L := hcoin
  -- pieces
  have p1 := sz_nat_le_self (keySize (k+1) (k+1))
  have p2 := sz_nat_le_self (k+1)
  have p3 := Ty.sz_nat_le (rationalCellBudget a b)
  have p4 := sz_nat_le_self (macroM c d k)
  have p5 := sz_rows_le rows
  have p6 := sz_range_le (k+1)
  have p7 := sz_nat_le_self (seedB (data hD hd A).base (data hD hd A).den (keySize (k+1) (k+1)))
  have p8 := sz_boolList (List.ofFn coins)
  rw [List.length_ofFn] at p8
  have e1 : macroM c d k = rationalRepetitionBudget (2 * ((k+1) + 1)) c d := rfl
  rw [← e1] at hm
  have hprog := sz_prog_iid (k+1)
  -- the polynomial pieces
  have hrw : rows.length * (rowIncidences rows * (4 * (k+1) + 6) + 2) ≤ 30 * (L + 1) ^ 3 := by
    have h1 : rows.length ≤ L + 1 := by omega
    have h2 : rowIncidences rows ≤ L + 1 := by omega
    have h3 : 4 * (k+1) + 6 ≤ 10 * (L + 1) := by omega
    calc rows.length * (rowIncidences rows * (4 * (k+1) + 6) + 2)
        ≤ (L + 1) * ((L + 1) * (10 * (L + 1)) + 2 * (L + 1)) := by
          apply Nat.mul_le_mul h1
          have := Nat.mul_le_mul h2 h3
          omega
      _ ≤ 30 * (L + 1) ^ 3 := cube_rows L
  have hrg : (k+1) * (4 * (k+1) + 2) ≤ 10 * (L + 1) ^ 3 := by
    have h1 : k + 1 ≤ L + 1 := by omega
    have h2 : (k+1) * (4 * (k+1) + 2) ≤ (L + 1) * (6 * (L + 1)) :=
      Nat.mul_le_mul h1 (by omega)
    have h3 := cube_quad L
    omega
  have hlin := cube_lin L
  -- assemble
  have hsz : (Ty.enc (TCtx TX) (ictx hD hd A a b c d k rows coins)).size =
      ((Ty.enc .nat (keySize (k+1) (k+1))).size + (Ty.enc .nat (k+1)).size +
        (Ty.enc .nat (rationalCellBudget a b)).size + (Ty.enc .nat (macroM c d k)).size + 3) +
      ((Ty.enc .nat (k+1)).size + (Ty.enc TRowsW (Query.encRows rows)).size +
        (Ty.enc WProg (Query.encProg (ZeroLengthDispatch.iidProgram (k+1)))).size +
        (Ty.enc .nat (keySize (k+1) (k+1))).size +
        (Ty.enc .nat (seedB (data hD hd A).base (data hD hd A).den (keySize (k+1) (k+1)))).size +
        (Ty.enc (.list .bool) (List.ofFn coins)).size + 5) + 1 :=
    sz_ctx_split _ _ _ _ _ _ rows (List.ofFn coins)
  rw [hsz, hprog]
  unfold ctxPoly
  omega

/-! ## The bridge -/

section Bridge
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : MultiTape.Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT E density PtE PsE T)

/-- The encoded size of `(ctx, encCfg s)` splits into context and configuration. -/
theorem instEnc_size (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (s : Config) :
    (instEnc hD hd A a b c d k rows coins s).size =
      (Ty.enc (TCtx TX) (ictx hD hd A a b c d k rows coins)).size +
        (Ty.enc TCfg (encCfg s)).size + 1 := by
  rw [instEnc_eq, shape2]

/-- **Size bridge.** At every reachable state the encoded loop state is polynomial in `L`. -/
theorem instEnc_size_le (hT : Monotone T) {a b c d k : ℕ}
    (rows : List (List (PauliCoord (k+1)))) (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd' : 0 < d) {s : Config}
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) :
    (instEnc hD hd A a b c d k rows coins s).size ≤
      statePoly (gateConstant hD hd A) density (seedConstant hD hd A) (paperL rows a b c d) := by
  have h1 := sz_ictx_le hD hd A (b := b) rows coins ha hc
  have h2 := sz_encCfg_le s
  have h3 := (Assembly.instReachable_bounds hD hd A spec hT rows coins ha hab hc hd' hs).2.1
  rw [instEnc_size]
  unfold statePoly
  omega

/-- The configuration alone (the measure used by the per-function bounds). -/
theorem encCfg_size_le (hT : Monotone T) {a b c d k : ℕ}
    (rows : List (List (PauliCoord (k+1)))) (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd' : 0 < d) {s : Config}
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) :
    (Ty.enc TCfg (encCfg s)).size ≤
      10 * InputEncoding.retainedPolynomial (gateConstant hD hd A) density (paperL rows a b c d)
        + 400 := by
  have h2 := sz_encCfg_le s
  have h3 := (Assembly.instReachable_bounds hD hd A spec hT rows coins ha hab hc hd' hs).2.1
  omega

end Bridge

end QecReliability.Trans.Bounds
