import Trans.Query.Codec

/-!
# Trans.Query.Plain: the query construction on plain (first-order) data

Every dependent object of the construction is represented by naturals, booleans and lists
(`Fin` indices become their values). This file defines the construction on that
representation, in exactly the recursive shape of the FL bodies (`Trans/Query/FL*.lean`);
`Trans/Query/Corr*.lean` proves that it is the image of the Lean construction.

Representation (see `Trans/Query/Types.lean` for the encoding functions):
* literal `(index, sign)`, clause, formula: `Lit`, `Clause`, `Form` (= `QueryCodec.PlainFormula`);
* gate `(u, s, x, y)`: `and x y = (false,false,x,y)`, `xor x y = (false,true,x,y)`,
  `not x = (true,false,x,0)`, `const b = (true,true,b.toNat,0)`;
* circuit: list of gates (output wire of gate `k` is `inputs + k`);
* program: `(gates, outputs)`;
* block: `(aux, formula)`;
* Pauli coordinate: `inl i ↦ (false, i)`, `inr i ↦ (true, i)`;
* reconstruction: `(gates, x-outputs, z-outputs)`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Query.Plain
open QecReliability.OracleCost QecReliability.Trans.Query

abbrev Lit := ℕ × Bool
abbrev Clause := List Lit
abbrev Form := List Clause
abbrev GateP := Bool × Bool × ℕ × ℕ
abbrev BlockP := ℕ × Form
abbrev ProgP := List GateP × List ℕ
abbrev Coord := Bool × ℕ
abbrev RecP := List GateP × List ℕ × List ℕ

/-! ## Wire maps -/

/-- `i ↦ i` below `e.1`, `i ↦ i + e.2` above (`Fin.castAdd`-type lifts). -/
def shiftWire (e : ℕ × ℕ) (i : ℕ) : ℕ := if i < e.1 then i else i + e.2

/-- Table lookup below `e.2.1 = f.length`, `i ↦ e.2.2 + (i - e.2.1)` above (`liftWire f`). -/
def tableWire (e : List ℕ × ℕ × ℕ) (i : ℕ) : ℕ :=
  if i < e.2.1 then e.1.getD i 0 else e.2.2 + (i - e.2.1)

def litS (e : ℕ × ℕ) (l : Lit) : Lit := (shiftWire e l.1, l.2)
def clauseS (e : ℕ × ℕ) (c : Clause) : Clause := c.map (fun l => litS e l)
def formS (e : ℕ × ℕ) (F : Form) : Form := F.map (fun c => clauseS e c)

def litT (e : List ℕ × ℕ × ℕ) (l : Lit) : Lit := (tableWire e l.1, l.2)
def clauseT (e : List ℕ × ℕ × ℕ) (c : Clause) : Clause := c.map (fun l => litT e l)
def formT (e : List ℕ × ℕ × ℕ) (F : Form) : Form := F.map (fun c => clauseT e c)

/-- Shift the wires of a gate (constants carry no wire). -/
def gateS (e : ℕ × ℕ) (g : GateP) : GateP :=
  if g.1 then
    (if g.2.1 then g else (g.1, g.2.1, shiftWire e g.2.2.1, g.2.2.2))
  else (g.1, g.2.1, shiftWire e g.2.2.1, shiftWire e g.2.2.2)

def gatesS (e : ℕ × ℕ) (gs : List GateP) : List GateP := gs.map (fun g => gateS e g)
def wiresS (e : ℕ × ℕ) (ws : List ℕ) : List ℕ := ws.map (fun w => shiftWire e w)

/-! ## Gates and circuits -/

def constGate (b : Bool) : GateP := (true, true, if b then 1 else 0, 0)

/-- Tseitin clauses of a gate with output wire `out`. -/
def gateClauses (out : ℕ) (g : GateP) : Form :=
  if g.1 then
    (if g.2.1 then [[(out, decide (g.2.2.1 ≠ 0))]]
     else [[(g.2.2.1, true), (out, true)], [(g.2.2.1, false), (out, false)]])
  else
    (if g.2.1 then
      [[(g.2.2.1, true), (g.2.2.2, true), (out, false)],
       [(g.2.2.1, true), (g.2.2.2, false), (out, true)],
       [(g.2.2.1, false), (g.2.2.2, true), (out, true)],
       [(g.2.2.1, false), (g.2.2.2, false), (out, false)]]
     else
      [[(g.2.2.1, false), (g.2.2.2, false), (out, true)],
       [(g.2.2.1, true), (out, false)], [(g.2.2.2, true), (out, false)]])

/-- `compileAt k gs`: the gate list compiled with first output wire `k`. -/
def compileAt : ℕ → List GateP → Form
  | _, [] => []
  | k, g :: gs => gateClauses k g ++ compileAt (k + 1) gs

/-! ## Blocks -/

def blockAnd (n : ℕ) (B C : BlockP) : BlockP := (B.1 + C.1, B.2 ++ formS (n, B.1) C.2)

def blockMerge (n : ℕ) : List BlockP → BlockP
  | [] => (0, [])
  | B :: Bs => blockAnd n B (blockMerge n Bs)

/-- `Program.matchBlock` on `v` primary wires. -/
def outputUnits : List ℕ → List Bool → Form
  | o :: os, b :: bs => [(o, b)] :: outputUnits os bs
  | _, _ => []

def matchBlock (v : ℕ) (P : ProgP) (bits : List Bool) : BlockP :=
  (P.1.length, compileAt v P.1 ++ outputUnits P.2 bits)

/-! ## Sparse normalizer, pairing and support (Bad side) -/

def rowWires (ox oz : ℕ) (row : List Coord) : List ℕ :=
  row.map (fun c => if c.1 then ox + c.2 else oz + c.2)

def parityGates (v : ℕ) : List ℕ → List GateP
  | [] => [constGate false]
  | x :: xs => parityGates v xs ++ [(false, true, x, v + xs.length)]

def rowBlock (v : ℕ) (row : List ℕ) : BlockP :=
  (row.length + 1, compileAt v (parityGates v row) ++ [[(v + row.length, false)]])

def nonempty (row : List ℕ) : Bool := !row.isEmpty

def normalizer (v ox oz : ℕ) (rows : List (List Coord)) : BlockP :=
  blockMerge v (((rows.map (fun row => rowWires ox oz row)).filter nonempty).map
    (fun row => rowBlock v row))

def productParityGates (v : ℕ) : List (ℕ × ℕ) → List GateP
  | [] => [constGate false]
  | p :: ps => productParityGates v ps ++
      [(false, false, p.1, p.2), (false, true, v + 2 * ps.length + 1, v + 2 * ps.length)]

def offsetPairs (n a b : ℕ) : List (ℕ × ℕ) := (List.range n).map (fun i => (a + i, b + i))

/-- `pairingPairs x z x' z'` for offset wirings. -/
def pairingPairs (n ox oz ox' oz' : ℕ) : List (ℕ × ℕ) :=
  offsetPairs n ox oz' ++ offsetPairs n oz ox'

def supportPairs (n ox oz oe : ℕ) : List (ℕ × ℕ) := offsetPairs n ox oe ++ offsetPairs n oz oe

def supportClauses (ps : List (ℕ × ℕ)) : Form := ps.map (fun p => [(p.1, false), (p.2, true)])

def pairingBlock (v : ℕ) (ps : List (ℕ × ℕ)) : BlockP :=
  (2 * ps.length + 1, compileAt v (productParityGates v ps) ++ [[(v + 2 * ps.length, true)]])

/-- `BadEncoding.block rows` (primary wires `e, zx, zz, xx, xz` at `0, n, 2n, 3n, 4n`). -/
def badBlock (n : ℕ) (rows : List (List Coord)) : BlockP :=
  blockAnd (5 * n) (normalizer (5 * n) n (2 * n) rows)
    (blockAnd (5 * n) (normalizer (5 * n) (3 * n) (4 * n) rows)
      (blockAnd (5 * n) (0, supportClauses (supportPairs n (3 * n) (4 * n) 0))
        (pairingBlock (5 * n) (pairingPairs n (3 * n) (4 * n) n (2 * n)))))

/-! ## Sparse reconstruction and cleaning (Good side) -/

def recZero (n v : ℕ) : RecP := ([constGate false], List.replicate n v, List.replicate n v)

def recAddInc (v : ℕ) (R : RecP) (c : Coord) (coeff : ℕ) : RecP :=
  (R.1 ++ [(false, true, if c.1 then R.2.2.getD c.2 0 else R.2.1.getD c.2 0, coeff)],
    if c.1 then (R.2.1, R.2.2.set c.2 (v + R.1.length))
    else (R.2.1.set c.2 (v + R.1.length), R.2.2))

def recAddRow (v : ℕ) (R : RecP) (coeff : ℕ) : List Coord → RecP
  | [] => R
  | c :: cs => recAddInc v (recAddRow v R coeff cs) c coeff

def synthesize (n v : ℕ) : ℕ → List (List Coord) → RecP
  | _, [] => recZero n v
  | base, row :: rows => recAddRow v (synthesize n v (base + 1) rows) base row

def condEq (e x y : ℕ) : Form := [[(e, false), (x, false), (y, true)], [(e, false), (x, true), (y, false)]]

/-- `condEqs i oz [s_i, s_{i+1}, …] = condEq i s_i (oz + i) ++ …`. -/
def condEqs (oz : ℕ) : ℕ → List ℕ → Form
  | _, [] => []
  | i, s :: ss => condEq i s (oz + i) ++ condEqs oz (i + 1) ss

def cleaning (n v : ℕ) (R : RecP) : BlockP :=
  (R.1.length, compileAt v R.1 ++ (condEqs n 0 R.2.1 ++ condEqs (2 * n) 0 R.2.2))

def trimRows (rows : List (List Coord)) : List (List Coord) := rows.filter (fun row => !row.isEmpty)

/-- `GoodEncoding.block rows` (primary wires `e, zx, zz, coeff` at `0, n, 2n, 3n`). -/
def goodBlock (n : ℕ) (rows : List (List Coord)) : BlockP :=
  blockAnd (3 * n + (trimRows rows).length) (normalizer (3 * n + (trimRows rows).length) n (2 * n) rows)
    (cleaning n (3 * n + (trimRows rows).length)
      (synthesize n (3 * n + (trimRows rows).length) (3 * n) (trimRows rows)))

/-! ## Population counter -/

def adderGates (v x y c : ℕ) : List GateP :=
  [(false, true, x, y), (false, true, v, c), (false, false, x, y), (false, false, v, c),
    (false, true, v + 2, v + 3)]

/-- `ripple k x y c` on `v` primary wires. -/
def ripple : ℕ → List ℕ → List ℕ → ℕ → ProgP
  | v, x :: xs, y :: ys, c =>
      (adderGates v x y c ++ (ripple (v + 5) xs ys (v + 4)).1, (v + 1) :: (ripple (v + 5) xs ys (v + 4)).2)
  | _, _, _, c => ([], [c])

/-- `countTree k xs zero` on `v` primary wires (`xs` has `2 ^ k` entries). -/
def countTree (v : ℕ) : ℕ → List ℕ → ℕ → ProgP
  | 0, xs, _ => ([], xs)
  | k + 1, xs, z =>
      let L := countTree v k (xs.take (xs.length / 2)) z
      let R := countTree v k (xs.drop (xs.length / 2)) z
      let gs := L.1 ++ gatesS (v, L.1.length) R.1
      let os := L.2 ++ wiresS (v, L.1.length) R.2
      let A := ripple (v + gs.length) (os.take (k + 1)) (os.drop (k + 1)) z
      (gs ++ A.1, A.2)

/-- `2 ^ n.size`. -/
def pow2Size (n : ℕ) : ℕ := 2 ^ n.size

def paddedWires (n : ℕ) : List ℕ := List.range n ++ List.replicate (pow2Size (max 1 n) - n) n

def population (n : ℕ) : ProgP :=
  (constGate false :: (countTree (n + 1) (max 1 n).size (paddedWires n) n).1,
    (countTree (n + 1) (max 1 n).size (paddedWires n) n).2)

/-- `weightBlock causeWire j` over `v ≥ r` primary wires (causes are wires `0 … r-1`). -/
def weightBlock (r v j : ℕ) : BlockP :=
  matchBlock v (gatesS (r, v - r) (population r).1, wiresS (r, v - r) (population r).2)
    (QueryCodec.word ((max 1 r).size + 1) j)

/-! ## Latent layer, hash cell, requests -/

/-- `pullback C B` for `B` on `3n + w` wires; `q = r + 2n + w` is the latent key + witness width. -/
def pullback (n r w : ℕ) (C : ProgP) (B : BlockP) : BlockP :=
  ((gatesS (r, 2 * n + w) C.1).length + B.1,
    compileAt (r + 2 * n + w) (gatesS (r, 2 * n + w) C.1) ++
      formT (wiresS (r, 2 * n + w) C.2 ++ List.range' r (2 * n + w), 3 * n + w,
        r + 2 * n + w + (gatesS (r, 2 * n + w) C.1).length) B.2)

def layerBlock (n r w : ℕ) (C : ProgP) (B : BlockP) (j : ℕ) : BlockP :=
  blockAnd (r + 2 * n + w) (pullback n r w C B) (weightBlock r (r + 2 * n + w) j)

def witness (n : ℕ) (rows : List (List Coord)) (side : Bool) : ℕ :=
  if side then (trimRows rows).length else 2 * n

def quantumBlock (n : ℕ) (rows : List (List Coord)) (side : Bool) : BlockP :=
  if side then goodBlock n rows else badBlock n rows

def quantumLayer (n r : ℕ) (rows : List (List Coord)) (C : ProgP) (side : Bool) (j : ℕ) : BlockP :=
  layerBlock n r (witness n rows side) C (quantumBlock n rows side) j

def hashCell (q w : ℕ) (B : BlockP) (H : ProgP) (target : List Bool) : BlockP :=
  blockAnd (q + w) B (matchBlock (q + w) (gatesS (q, w) H.1, wiresS (q, w) H.2) target)

def quantumCell (n r : ℕ) (rows : List (List Coord)) (C : ProgP) (side : Bool) (j : ℕ)
    (H : ProgP) (target : List Bool) : BlockP :=
  hashCell (r + 2 * n) (witness n rows side) (quantumLayer n r rows C side j) H target

/-- `PrefixCNF.units` (first index `k`). -/
def units : ℕ → ℕ → List Bool → Form
  | _, _, [] => []
  | _, 0, _ :: _ => [[]]
  | k, q + 1, b :: pre => [(k, b)] :: units (k + 1) q pre

/-- The projected request of a block over `q` keys and `w` witnesses, restricted to `pre`:
`(varCount, formula)`. -/
def request (q w : ℕ) (B : BlockP) (pre : List Bool) : ℕ × Form :=
  (q + (w + B.1), B.2 ++ units 0 q pre)

/-- `padRequest D` then `QueryCodec.encode`. -/
def query (D : ℕ) (req : ℕ × Form) : List Bool :=
  encodePlain (max req.1 (D * req.2.length)) req.2

def baseQuery (n r : ℕ) (rows : List (List Coord)) (C : ProgP) (side : Bool) (j : ℕ)
    (pre : List Bool) (D : ℕ) : List Bool :=
  query D (request (r + 2 * n) (witness n rows side) (quantumLayer n r rows C side j) pre)

def cellQuery (n r : ℕ) (rows : List (List Coord)) (C : ProgP) (side : Bool) (j : ℕ)
    (H : ProgP) (target : List Bool) (pre : List Bool) (D : ℕ) : List Bool :=
  query D (request (r + 2 * n) (witness n rows side) (quantumCell n r rows C side j H target) pre)

end QecReliability.Trans.Query.Plain
