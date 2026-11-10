import Trans.HashCallees.MGG

/-!
# Trans.HashCallees.EncoderPlain: the recursive dyadic encoder on plain data

The encoder family `(concreteDyadicData hD hd A).shift.program ell` is the XOR program
`exactEncoder base R₁ R₂ (ell + 1)` (`SerializedEncoderWiringCandidateReviewed.lean`) built from
* the base program `eightBaseProgram` (one row-major emitter for the certificate's local matrix
  `matrixEntry A`, eight blocks),
* the amplifiers `R₁ ell`, `R₂ ell` (`amplifierProgram` over the 384-step power of the lazy MGG
  graph on `squareSide (T / D)²` vertices, the same local matrix),
* the one-copy recursion `oneCopy R₁ H R₂`.

Constants are the triple `E = (D, K, code)`: the degree `D = 16 ^ K`, the walk power `K = 384`
and the certificate's base code `code = A.code.val` (coefficient `(r, j)` is
`code.testBit (r * (D + D) + j)`). Nothing about them is evaluated.

* `emitP n m c ref`: `emitKeepZero` (one zero gate, then `m` rows of `c` XOR gates, gate `g`
  reading `ref (g / c) (g % c)`), indexed by the global gate number `g`;
* `baseP`, `powRotP` (rotation of the power graph), `ampP`, `oneCopyP`, `encP`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.HashCallees
open QecReliability.Trans.Query.Plain QecReliability.Trans.Hash

/-! ## The row emitter -/

/-- Coefficient `(r, j)` of the local matrix with `k` columns. -/
def coeffP (code k r j : ℕ) : Bool := code.testBit (r * k + j)

/-- Gate number `g` of the row emitter on `n` inputs (zero wire `n`, rows of `c` gates). -/
def gateP (n c : ℕ) (ref : ℕ → ℕ → ℕ) (g : ℕ) : GateP :=
  (false, true, if g % c = 0 then n else n + g, ref (g / c) (g % c))

/-- `emitKeepZero n m c refs` on plain data. -/
def emitP (n m c : ℕ) (ref : ℕ → ℕ → ℕ) : ProgP :=
  (constGate false :: (List.range (m * c)).map (gateP n c ref),
    n :: (List.range m).map (fun i => n + (i + 1) * c))

/-! ## Base program -/

/-- References of the base emitter: `k` columns, `h` rows per block, `n = 8 k` inputs. -/
def baseRef (code k h n : ℕ) (i j : ℕ) : ℕ :=
  if coeffP code k (i % h) j then j + k * (i / h) else n

/-- `baseProgram` (eight blocks of the local matrix, `46 D` zero outputs). -/
def baseP (D code : ℕ) : ProgP :=
  ((emitP (8 * (D + D)) (8 * (D / 4)) (D + D) (baseRef code (D + D) (D / 4) (8 * (D + D)))).1,
    List.range (8 * (D + D)) ++
      (List.range (8 * (D / 4))).map (fun i => 8 * (D + D) + (i + 1) * (D + D)) ++
      List.replicate (46 * D) (8 * (D + D)))

/-! ## Rotation of the power graph -/

/-- One step of the port-word walk: state `(s, v, w, acc)` (side, vertex, remaining port
digits, reversed port word so far). -/
def powStep (st : ℕ × ℕ × ℕ × ℕ) (_ : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (st.1, (lazyRotP st.1 st.2.1 (st.2.2.1 % 16)).1, st.2.2.1 / 16,
    st.2.2.2 * 16 + (lazyRotP st.1 st.2.1 (st.2.2.1 % 16)).2)

/-- The rotation of the `K`-th port power of `lazyMGGPortGraph s` on values:
`(end vertex, reversed port word)`. -/
def powRotP (s K v i : ℕ) : ℕ × ℕ :=
  (((List.range K).foldl powStep (s, v, i, 0)).2.1, ((List.range K).foldl powStep (s, v, i, 0)).2.2.2)

/-! ## Amplifier -/

/-- `paddedReference`: index `i` of the padded input, `T` (the zero wire) beyond `T`. -/
def padRef (T i : ℕ) : ℕ := if i < T then i else T

/-- `portReferences`: column `j < D` reads the outgoing slot of `v`, column `D + j'` the
incoming slot `rotation (v, j')`. -/
def portRef (D K T s v j : ℕ) : ℕ :=
  if j < D then padRef T (j + D * v)
  else padRef T ((powRotP s K v (j - D)).2 + D * (powRotP s K v (j - D)).1)

/-- References of the amplifier emitter (`h = D / 4` rows per vertex). -/
def ampRef (D K code T s : ℕ) (i j : ℕ) : ℕ :=
  if coeffP code (D + D) (i % (D / 4)) j then portRef D K T s (i / (D / 4)) j else T

/-- `amplifierProgram` on `T` inputs over the `K`-power of the lazy MGG graph of side
`s = ceilSquare (T / D)` (`T / 2` outputs). -/
def ampP (D K code T : ℕ) : ProgP :=
  ((emitP T (UniformAdapter.ceilSquare (T / D) * UniformAdapter.ceilSquare (T / D) * (D / 4))
      (D + D) (ampRef D K code T (UniformAdapter.ceilSquare (T / D)))).1,
    (List.range (T / 2)).map (fun j =>
      if j < UniformAdapter.ceilSquare (T / D) * UniformAdapter.ceilSquare (T / D) * (D / 4)
      then T + (j + 1) * (D + D) else T))

/-! ## The recursion -/

/-- `oneCopy R₁ H R₂` for `R₁` on `n` inputs: outputs `(x, H(R₁ x), R₂(H(R₁ x)))`. -/
def oneCopyP (n : ℕ) (R₁ H R₂ : ProgP) : ProgP :=
  ((pcompose n (pcompose n R₁ H) R₂).1,
    List.range n ++ (pcompose n R₁ H).2 ++ (pcompose n (pcompose n R₁ H) R₂).2)

/-- `messageWidth D ell = 16 D 2^ell`. -/
def mwP (D ell : ℕ) : ℕ := 16 * D * 2 ^ ell

/-- The encoder of level `ell` on plain data, `E = (D, K, code)`. -/
def encP (E : ℕ × ℕ × ℕ) : ℕ → ProgP
  | 0 => baseP E.1 E.2.2
  | ell + 1 => oneCopyP (2 * mwP E.1 ell) (ampP E.1 E.2.1 E.2.2 (2 * mwP E.1 ell)) (encP E ell)
      (ampP E.1 E.2.1 E.2.2 (4 * mwP E.1 ell))

end QecReliability.Trans.HashCallees
