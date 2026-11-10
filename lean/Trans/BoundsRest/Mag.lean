import Trans.Bounds.Size
import Trans.BoundsQH.Compile
import Assembly.Poly

/-!
# Trans.BoundsRest.Mag: magnitudes of the instance data

The controller's external data `X = instX … = (n, rows, C, q, SB, coins)` and every valid
request key have polynomial *magnitude* (`Trans/Query/Bounds.lean`'s `mag`: value of a
natural, `Σ (mag + 1) + 1` for a list) in `L = paperL rows a b c d`:

* `instX_mag_le : mag TX (instX …) ≤ magX sc L` (`magX sc L = 3 (L+2)² + 3 coinPoly sc L + 10`);
* `key_mag_le : ValidKey q r m key → mag TKey (encKey key) ≤ r + 2m + 3q + 8`;
* **`arg_mag_le`**: `mag (X, encKey key) ≤ magK sc L` for every valid key of the instance
  (`magK sc L = magX sc L + 20 L + 20`), in particular at every reachable state
  (`reach_arg_mag_le`, via `reachable_request_invariant`).

These feed the `mag`-based bounds of BoundsQH (`compile_poly`) and the endpoint bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.BoundsRest
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH (mag_list_le)
open QecReliability.Trans.Control (TKey encKey)
open QecReliability.Trans.Wire (TX instX wireX TRowsW TCoordW WProg seedB)
open QecReliability.Trans.Bounds (coinPoly)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

/-! ## Polynomials -/

def magX (sc L : ℕ) : ℕ := 3 * ((L + 2) * (L + 2)) + 3 * coinPoly sc L + 10

def magK (sc L : ℕ) : ℕ := magX sc L + 20 * L + 20

theorem magX_mono (sc : ℕ) : Monotone (magX sc) := by
  intro x y h
  unfold magX
  have h1 := Nat.mul_le_mul (show x + 2 ≤ y + 2 by omega) (show x + 2 ≤ y + 2 by omega)
  have h2 := Bounds.coinPoly_mono sc h
  omega

theorem magK_mono (sc : ℕ) : Monotone (magK sc) := by
  intro x y h
  unfold magK
  have := magX_mono sc h
  omega

theorem magK_pb (sc : ℕ) : Assembly.PolyBounded (magK sc) := by
  have e : magK sc = fun L => 3 * ((L + 2) * (L + 2)) + 3 * ((6 * L + 5) * (sc * (2 * L))) + 10 +
      20 * L + 20 := by
    funext L; rfl
  rw [e]
  poly_bounded

/-! ## Pieces -/

theorem mag_coord_le {n : ℕ} (x : PauliCoord n) : mag TCoordW (Query.encCoord x) ≤ n + 1 := by
  rcases x with i | i
  · have := i.isLt
    show 1 + i.val + 1 ≤ n + 1
    omega
  · have := i.isLt
    show 1 + i.val + 1 ≤ n + 1
    omega

theorem mag_row_le {n : ℕ} (row : List (PauliCoord n)) :
    mag (.list TCoordW) (row.map Query.encCoord) ≤ row.length * (n + 2) + 1 := by
  have := mag_list_le TCoordW (row.map Query.encCoord) (n + 1) (fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
    exact mag_coord_le x)
  simpa using this

theorem mag_rows_le {n : ℕ} (rows : List (List (PauliCoord n))) :
    mag TRowsW (Query.encRows rows) ≤ rowIncidences rows * (n + 2) + 2 * rows.length + 1 := by
  induction rows with
  | nil => show 1 ≤ _; omega
  | cons row rows ih =>
    have h1 := mag_row_le row
    have e2 : rowIncidences (row :: rows) = row.length + rowIncidences rows := by
      simp [rowIncidences]
    show mag (.list TCoordW) (row.map Query.encCoord) + 1 + mag TRowsW (Query.encRows rows) ≤ _
    rw [e2, List.length_cons]
    have : (row.length + rowIncidences rows) * (n + 2) =
        row.length * (n + 2) + rowIncidences rows * (n + 2) := by ring
    omega

theorem mag_range_le (n : ℕ) : mag (.list .nat) (List.range n) ≤ n * (n + 1) + 1 := by
  have h := mag_list_le .nat (List.range n) n (fun i hi => (List.mem_range.mp hi).le)
  simpa using h

theorem mag_iid_le (n : ℕ) :
    mag WProg (Query.encProg (ZeroLengthDispatch.iidProgram n)) ≤ n * (n + 1) + 3 := by
  rw [Wire.encProg_iid]
  have := mag_range_le n
  show 1 + mag (.list .nat) (List.range n) + 1 ≤ _
  omega

theorem mag_bools_le (bs : List Bool) : mag (.list .bool) bs ≤ 2 * bs.length + 1 := by
  have := mag_list_le .bool bs 1 (fun _ _ => le_refl _)
  omega

/-- `mag` of the context data, split into components. -/
theorem mag_wireX (base den : ℕ) {n : ℕ} (rows : List (List (PauliCoord n))) (coins : List Bool) :
    mag TX (wireX base den rows coins) =
      n + mag TRowsW (Query.encRows rows) +
        mag WProg (Query.encProg (ZeroLengthDispatch.iidProgram n)) + keySize n n +
        seedB base den (keySize n n) + mag (.list .bool) coins + 5 := by
  show n + (mag TRowsW (Query.encRows rows) +
        (mag WProg (Query.encProg (ZeroLengthDispatch.iidProgram n)) + (keySize n n +
        (seedB base den (keySize n n) + mag (.list .bool) coins + 1) + 1) + 1) + 1) + 1 = _
  omega

theorem key_mag_le {q r m : ℕ} {key : RequestKey} (h : ValidKey q r m key) :
    mag TKey (encKey key) ≤ r + 2 * m + 3 * q + 8 := by
  cases key with
  | base g j rep =>
    obtain ⟨h1, h2⟩ := h
    show 1 + (1 + (j + (rep + (0 + 1 + 1) + 1) + 1) + 1) + 1 ≤ _
    omega
  | cell g j rep scale pre =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    have := mag_bools_le pre
    show 1 + (1 + (j + (rep + (scale + mag (.list .bool) pre + 1) + 1) + 1) + 1) + 1 ≤ _
    omega

/-! ## The instance -/

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : CertifiedParity (512*t) (64*t) t)

/-- **Magnitude of the context data** of an instance. -/
theorem instX_mag_le {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (ha : 0 < a) (hc : 0 < c) :
    mag TX (instX hD hd A c d k rows coins) ≤ magX (seedConstant hD hd A) (paperL rows a b c d) := by
  obtain ⟨hn, hq, -, -, -⟩ := InputEncoding.budget_parameters rows
    (ZeroLengthDispatch.iidProgram (k+1)) a b c d ha hc
  obtain ⟨-, -, hrows, -, -⟩ := InputEncoding.paperLength_components rows
    (ZeroLengthDispatch.iidProgram (k+1)) a b c d
  have hcoin := coinBits_le_paperL hD hd A rows a b c d ha hc
  have hSB := Bounds.seedB_le_coinBits hD hd A c d k
  have h1 := mag_rows_le rows
  have h2 := mag_iid_le (k+1)
  have h3 := mag_bools_le (List.ofFn coins)
  rw [List.length_ofFn] at h3
  have e := mag_wireX (data hD hd A).base (data hD hd A).den rows (List.ofFn coins)
  have e' : mag TX (instX hD hd A c d k rows coins) =
      mag TX (wireX (data hD hd A).base (data hD hd A).den rows (List.ofFn coins)) := rfl
  rw [e', e]
  clear e e'
  have hn' : k + 1 ≤ paperL rows a b c d := hn
  have hrows' : rows.length + rowIncidences rows ≤ paperL rows a b c d := hrows
  have hcoin' : coinBits hD hd A c d (k+1) ≤ coinPoly (seedConstant hD hd A) (paperL rows a b c d) :=
    hcoin
  clear hn hq hrows hcoin
  generalize paperL rows a b c d = L at hn' hrows' hcoin' ⊢
  have m1 : rowIncidences rows * (k + 1 + 2) ≤ L * (L + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have m2 : (k + 1) * (k + 1 + 1) ≤ L * (L + 2) := Nat.mul_le_mul (by omega) (by omega)
  have m3 : (L + 2) * (L + 2) = L * (L + 2) + 2 * (L + 2) := by ring
  have hk : keySize (k+1) (k+1) = 3 * (k + 1) := by unfold keySize; omega
  rw [hk] at hSB ⊢
  unfold magX
  omega

/-- **Magnitude of the compile argument** at every valid key of the instance. -/
theorem arg_mag_le {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (ha : 0 < a) (hc : 0 < c)
    {key : RequestKey} (hkey : ValidKey (keySize (k+1) (k+1)) (k+1) (macroM c d k) key) :
    mag (.prod TX TKey) (instX hD hd A c d k rows coins, encKey key) ≤
      magK (seedConstant hD hd A) (paperL rows a b c d) := by
  obtain ⟨hn, hq, -, hm, -⟩ := InputEncoding.budget_parameters rows
    (ZeroLengthDispatch.iidProgram (k+1)) a b c d ha hc
  have h1 := instX_mag_le hD hd A rows coins (b := b) ha hc
  have h2 := key_mag_le hkey
  have e1 : macroM c d k = rationalRepetitionBudget (2 * ((k+1) + 1)) c d := rfl
  rw [← e1] at hm
  have e : mag (.prod TX TKey) (instX hD hd A c d k rows coins, encKey key) =
      mag TX (instX hD hd A c d k rows coins) + mag TKey (encKey key) + 1 := rfl
  rw [e]
  have hn' : k + 1 ≤ paperL rows a b c d := hn
  have hq' : keySize (k+1) (k+1) ≤ 2 * paperL rows a b c d := hq
  have hm' : 2 * macroM c d k + 1 ≤ 6 * paperL rows a b c d + 5 := hm
  clear hn hq hm
  generalize paperL rows a b c d = L at h1 hn' hq' hm' ⊢
  unfold magK
  omega

section Reach
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : MultiTape.Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT E density PtE PsE T)

/-- The same at the request of every reachable state. -/
theorem reach_arg_mag_le {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (ha : 0 < a) (hc : 0 < c) {s : Config}
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) :
    mag (.prod TX TKey) (instX hD hd A c d k rows coins, encKey s.request) ≤
      magK (seedConstant hD hd A) (paperL rows a b c d) :=
  arg_mag_le hD hd A rows coins ha hc (reachable_request_invariant hs).request

end Reach

end QecReliability.Trans.BoundsRest
