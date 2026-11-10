import Trans.Query.Types
import Trans.Hash.Seed
import UniformWalkFactoryCandidate

/-!
# Trans.Hash.Plain: the hash program on plain (first-order) data

Programs are `Plain.ProgP = (gates, outputs)` (`Trans/Query/Plain.lean`): gate `k` of a
program on `n` inputs has output wire `n + k`; `encProg` (`Trans/Query/Types.lean`) is the
encoding of a `SharedCircuit.Program`. This file defines the hash program
`(K.forward e).compiled.implementation.program r s` of `UniformAdapter.DyadicXorData.walkCircuits`
on that representation, in the recursive shape of the FL bodies; `Trans/Hash/Corr*.lean`
proves it is the image of the Lean construction.

Every wire renaming is a table lookup `Plain.tableWire (table, k, base)`
(`i ↦ table[i]` below `k`, `i ↦ base + (i - k)` above), which is what `Circuit.liftWire`
computes on values.

* `pcompose n P Q` (`Program.compose`), `pselect P idx` (`P.compose (Program.pure f)`);
* `padP a q m P` (`padInputsAndOutputs`);
* `abit`, `affP` (`affineBit`, `bundle`, `localAffine`);
* `pAddWire`, `scatterP`, `revStep`, `revP`, `transP` (`XorProgram.transposed`);
* `pvisits`, `encIndex` (`PortGraph.visits` ∘ `walkLabel`, `repeatWires`);
* `hashPlain`: the whole program.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Hash
open QecReliability.Trans.Query QecReliability.Trans.Query.Plain

/-! ## Wire maps -/

/-- Map the wires of a plain gate (constants carry none). -/
def gmapW (σ : ℕ → ℕ) (g : GateP) : GateP :=
  if g.1 then (if g.2.1 then g else (g.1, g.2.1, σ g.2.2.1, g.2.2.2))
  else (g.1, g.2.1, σ g.2.2.1, σ g.2.2.2)

/-- Rename the gates' wires through a table. -/
def tabGates (e : List ℕ × ℕ × ℕ) (gs : List GateP) : List GateP :=
  gs.map (fun g => gmapW (tableWire e) g)

/-- Rename wires through a table. -/
def tabWires (e : List ℕ × ℕ × ℕ) (ws : List ℕ) : List ℕ := ws.map (fun w => tableWire e w)

/-! ## Program combinators -/

/-- `P.compose Q` for `P` on `n` inputs. -/
def pcompose (n : ℕ) (P Q : ProgP) : ProgP :=
  (P.1 ++ tabGates (P.2, P.2.length, n + P.1.length) Q.1,
    tabWires (P.2, P.2.length, n + P.1.length) Q.2)

/-- `P.compose (Program.pure f)`, `idx` the list of values of `f`. -/
def pselect (P : ProgP) (idx : List ℕ) : ProgP := (P.1, idx.map (fun i => P.2.getD i 0))

/-- The input wiring of `padInputsAndOutputs` from `a` to `q` inputs (`zeroInput q a`). -/
def padTable (a q : ℕ) : List ℕ := (List.range a).map (fun i => if i < q then i else q)

/-- `padInputsAndOutputs P q m _` for `P` on `a` inputs. -/
def padP (a q m : ℕ) (P : ProgP) : ProgP :=
  (constGate false :: tabGates (padTable a q, a, q + 1) P.1,
    tabWires (padTable a q, a, q + 1) P.2 ++ List.replicate (m - P.2.length) q)

/-! ## Local affine hashing -/

/-- `affineBit` on `v` inputs: coefficients, intercept, first input `x0` (coefficient `j`
reads input `x0 + j`); the gates and the output wire. -/
def abit (v : ℕ) : List Bool → Bool → ℕ → List GateP × ℕ
  | [], b, _ => ([constGate b], v)
  | c :: cs, b, x0 =>
    if c then ((abit v cs b (x0 + 1)).1 ++ [(false, true, x0, (abit v cs b (x0 + 1)).2)],
      v + (abit v cs b (x0 + 1)).1.length)
    else abit v cs b (x0 + 1)

/-- `bundle` of the affine bits of the rows `i, i+1, …` (row `i` reads inputs `t*i …`). -/
def affP (v t : ℕ) : ℕ → List (List Bool × Bool) → ProgP
  | _, [] => ([], [])
  | i, r :: rs =>
    ((abit v r.1 r.2 (t * i)).1 ++
        tabGates (List.range v, v, v + (abit v r.1 r.2 (t * i)).1.length) (affP v t (i + 1) rs).1,
      (abit v r.1 r.2 (t * i)).2 ::
        tabWires (List.range v, v, v + (abit v r.1 r.2 (t * i)).1.length) (affP v t (i + 1) rs).2)

/-! ## Transpose of an XOR program -/

/-- `Program.addWire target src` on `n` inputs. -/
def pAddWire (n : ℕ) (P : ProgP) (target src : ℕ) : ProgP :=
  (P.1 ++ [(false, true, P.2.getD target 0, src)], P.2.set target (n + P.1.length))

/-- `scatterList` (pairs `(target, source)`, the last one applied first). -/
def scatterP (n : ℕ) (P : ProgP) : List (ℕ × ℕ) → ProgP
  | [] => P
  | ts :: xs => pAddWire n (scatterP n P xs) ts.1 ts.2

/-- `[(o₀, i), (o₁, i+1), …]`. -/
def idxPairs : List ℕ → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | o :: os, i => (o, i) :: idxPairs os (i + 1)

/-- One step of `XorCircuit.reverse` for the gate `g` (a zero gate has `g.1 = true`,
an XOR gate `g = (false, true, x, y)`). -/
def revStep (n : ℕ) (P : ProgP) (g : GateP) : ProgP :=
  if g.1 then (P.1, P.2.dropLast)
  else
    ((pAddWire n (pAddWire n P g.2.2.1 (P.2.getD (P.2.length - 1) 0)) g.2.2.2
        ((pAddWire n P g.2.2.1 (P.2.getD (P.2.length - 1) 0)).2.getD (P.2.length - 1) 0)).1,
      (pAddWire n (pAddWire n P g.2.2.1 (P.2.getD (P.2.length - 1) 0)) g.2.2.2
        ((pAddWire n P g.2.2.1 (P.2.getD (P.2.length - 1) 0)).2.getD (P.2.length - 1) 0)).2.dropLast)

/-- `XorCircuit.reverse` over the gates in reverse order. -/
def revP (n : ℕ) : List GateP → ProgP → ProgP
  | [], P => P
  | g :: gs, P => revP n gs (revStep n P g)

/-- `XorProgram.transposed` of an XOR program `C` on `k` inputs (a program on
`C.2.length` inputs with `k` outputs). -/
def transP (k : ℕ) (C : ProgP) : ProgP :=
  revP C.2.length C.1.reverse
    (scatterP C.2.length ([constGate false], List.replicate (k + C.1.length) C.2.length)
      (idxPairs C.2 0))

/-! ## Walk symbols -/

/-- `PortGraph.visits` on values: neighbor map `nb`, degree `d`, walk digits `w` (base `d`). -/
def pvisits (nb : ℕ → ℕ → ℕ) (d : ℕ) : ℕ → ℕ → ℕ → ℕ
  | v, _, 0 => v
  | v, w, h + 1 => pvisits nb d (nb v (w % d)) (w / d) h

/-- The binary-code output read by encoder output `x` (`repeatWires M L t`, then
`symbolProgram` with `D = d ^ steps` walks per vertex and `t = steps + 1` visits). -/
def encIndex (nb : ℕ → ℕ → ℕ) (d D M t x : ℕ) : ℕ :=
  pvisits nb d ((x % t + t * (x / t % M)) / t / D) ((x % t + t * (x / t % M)) / t % D)
    ((x % t + t * (x / t % M)) % t)

/-! ## The whole program -/

/-- The neighbor map of an `MGGInput` at side `s` on values (`0` off the domain). -/
noncomputable def gNbr (G : UniformAdapter.MGGInput) (s v i : ℕ) : ℕ :=
  if h : 3 ≤ s ∧ v < s * s ∧ i < 16 then
    ((G.graph s h.1).neighbor ⟨v, h.2.1⟩ ⟨i, h.2.2⟩).val
  else 0

/-- The scalar parameters of the walk code at input length `q`:
`(firstIndex, firstLength, side, order, steps, 16^steps, walkCount, secondIndex, L)`. -/
structure Params where
  e1 : ℕ
  N1 : ℕ
  s : ℕ
  m : ℕ
  k : ℕ
  D : ℕ
  M : ℕ
  e2 : ℕ
  L : ℕ

def params (base den q : ℕ) : Params :=
  let e1 := UniformAdapter.dyadicUp base (4 * q)
  let N1 := base * 2 ^ e1
  let s := UniformAdapter.ceilSquare N1
  let k := UniformAdapter.walkClock den
  let M := s * s * 16 ^ k
  let e2 := UniformAdapter.dyadicUp base M
  ⟨e1, N1, s, s * s, k, 16 ^ k, M, e2, base * 2 ^ e2⟩

/-- The hash program on plain data: `prog ell` is the plain encoder program of index `ell`,
`nb s` the neighbor map of the graph of side `s`, `r` the scale, `bits` the seed bits. -/
def hashPlain (base den q : ℕ) (prog : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ) (r : ℕ)
    (bits : List Bool) : ProgP :=
  let p := params base den q
  pselect
    (pcompose q
      (pcompose q
        (pselect (padP (p.N1 / 4) q p.m (prog p.e1))
          ((List.range (p.L * (p.k + 1))).map (encIndex (nb p.s) 16 p.D p.M (p.k + 1))))
        (affP (p.L * (p.k + 1)) (p.k + 1) 0 (seedRows (p.k + 1) p.L bits)))
      (pselect (transP (p.L / 4) (prog p.e2)) (List.range q)))
    (List.range r)

end QecReliability.Trans.Hash
