import TensorMachineContextFL
import LatentWrappersFL

/-! Compiled tensor query wrapper: a scalar controller ordinal is looked up in
the cached grid, and the complete coordinate list is sent to the tensor CNF
compiler. Hash-program construction and random-seed slicing use the existing
certified implementation on the unchanged cause/Pauli key universe. -/

set_option autoImplicit false

namespace QecReliability.TensorMachine.QueryFL

open FL FL.Lib FL.Tm Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid TKey encKey)

abbrev TX := ContextFL.TX
abbrev CompilerArg : Ty :=
  .prod .bool (.prod .nat (.prod (.list .nat) (.prod TRowsW (.prod WProg
    (.prod .bool (.prod (.list .nat) (.prod WProg
      (.prod (.list .bool) (.prod (.list .bool) .nat)))))))))

abbrev degrees {Γ : List Ty} (x : Tm Γ TX) : Tm Γ (.list .nat) := .fst x
abbrev table {Γ : List Ty} (x : Tm Γ TX) : Tm Γ GridFL.Table := .fst (.snd x)
abbrev oldX {Γ : List Ty} (x : Tm Γ TX) : Tm Γ Trans.Wire.TX := .snd (.snd x)

abbrev mkArg {Γ : List Ty} (cell : Tm Γ .bool) (x : Tm Γ TX) (k : Tm Γ TKey)
    (js : Tm Γ (.list .nat)) (hp : Tm Γ WProg) (target pre : Tm Γ (.list .bool))
    (D : ℕ) : Tm Γ CompilerArg :=
  .pair cell (.pair (Xn (oldX x)) (.pair (degrees x) (.pair (Xrows (oldX x))
    (.pair (XC (oldX x)) (.pair (Kgood k) (.pair js (.pair hp
      (.pair target (.pair pre (.lit D))))))))))

variable (L : Lib) (c : CIx) (Q : FnSig CompilerArg (.list .bool))
  (H : FnSig Trans.Hash.THashArg WProg) (base den D getIdx idx : ℕ)

def compileBody : Tm [.prod TX TKey] (.list .bool) :=
  .letE (.app (getDF GridFL.Row getIdx)
    (.pair (table (.fst v0)) (.pair (Kcoef (.snd v0)) .lnil))) <|
  .ite (Kcell (.snd v1))
    (.app Q (mkArg .tt (.fst v1) (.snd v1) v0
      (.app (hashWF L c H base den) (.pair (oldX (.fst v1)) (.snd v1)))
      (.app (replicateF .bool L.rep) (.pair (Kscale (.snd v1)) .ff)) (Kpre (.snd v1)) D))
    (.app Q (mkArg .ff (.fst v1) (.snd v1) v0 (.lit ([], [])) .lnil .lnil D))

def compileF := bodySig idx (compileBody L c Q H base den D getIdx)

theorem compile_den_base (ds : List ℕ) (points : List (List ℕ)) (n : ℕ)
    (rows : List (List (Bool × ℕ))) (C : Trans.Query.Plain.ProgP) (q SB : ℕ)
    (coins : List Bool) (side : Bool) (j rep : ℕ) :
    (compileF L c Q H base den D getIdx idx).den
      ((ds, points, n, rows, C, q, SB, coins), encKey (.base side j rep)) =
      Q.den (false, n, ds, rows, C, side, points.getD j [], ([], []), [], [], D) := by
  simp [compileF, bodySig_den, compileBody, mkArg, degrees, table, oldX,
    tm_simp, encKey, getDF]

theorem compile_den_cell (ds : List ℕ) (points : List (List ℕ)) (n : ℕ)
    (rows : List (List (Bool × ℕ))) (C : Trans.Query.Plain.ProgP) (q SB : ℕ)
    (coins : List Bool) (side : Bool) (j rep scale : ℕ) (pre : List Bool) :
    (compileF L c Q H base den D getIdx idx).den
      ((ds, points, n, rows, C, q, SB, coins), encKey (.cell side j rep scale pre)) =
      Q.den (true, n, ds, rows, C, side, points.getD j [],
        H.den (base, den, q, scale, (coins.drop (rep * SB)).take SB),
        List.replicate scale false, pre, D) := by
  simp [compileF, bodySig_den, compileBody, mkArg, degrees, table, oldX,
    tm_simp, encKey, getDF, hashWF, hashWBody, sliceF, sliceBody]

theorem compile_valid {P : FL.Program} (hL : L.OK P)
    (hQ : ∀ x, Q.ValidAt P x)
    (hg : ∀ x, (getDF GridFL.Row getIdx).ValidAt P x)
    (hh : ∀ x, (hashWF L c H base den).ValidAt P x)
    (hi : P[idx]? = some (compileBody L c Q H base den D getIdx).compile) :
    ∀ x, (compileF L c Q H base den D getIdx idx).ValidAt P x := by
  intro x
  apply bodySig_valid hi
  simp [compileBody, mkArg, degrees, table, oldX, tm_simp, hQ, hg, hh, hL.rep]

end QecReliability.TensorMachine.QueryFL
