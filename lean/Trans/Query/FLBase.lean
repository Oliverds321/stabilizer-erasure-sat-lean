import Trans.Query.Plain

/-!
# Trans.Query.FLBase: index table, type notations, exact signatures

* `Ix`: the program indices of every global function used by the query transcription
  (library functions included). Bodies and signatures take `x : Ix`; `Trans/Query/Main.lean`
  fixes a concrete `Ix` and the corresponding program.
* Type notations for the plain representation (`TGate`, `TBlock`, …).
* `FnSig.exact i body den`: the signature of a non-recursive function whose bounds are
  *exactly* those of its body (`cost = body.cost + 2`, `depth = body.depth + 1`,
  `msize = body.msize`); `exact_valid` reduces its contract to the calls and the meaning.
  Closed-form bounds are proved separately.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Query
open QecReliability.FL QecReliability.FL.Lib

/-- Program indices of all functions of the query transcription. -/
structure Ix where
  -- FL.Lib.Nat
  succ : ℕ
  pred : ℕ
  addc : ℕ
  add : ℕ
  subb : ℕ
  sub : ℕ
  le : ℕ
  lt : ℕ
  eq : ℕ
  max : ℕ
  mul : ℕ
  bitLen : ℕ
  div2 : ℕ
  -- FL.Lib.List (one index serves every element type: the compiled body ignores types)
  length : ℕ
  append : ℕ
  replicate : ℕ
  getD : ℕ
  take : ℕ
  drop : ℕ
  rangeFrom : ℕ
  range : ℕ
  -- Codec
  word : ℕ
  natHeader : ℕ
  literal : ℕ
  literals : ℕ
  clause : ℕ
  body : ℕ
  encode : ℕ
  -- circuits and blocks
  shiftWire : ℕ
  litS : ℕ
  clauseS : ℕ
  formS : ℕ
  tableWire : ℕ
  litT : ℕ
  clauseT : ℕ
  formT : ℕ
  gateS : ℕ
  gatesS : ℕ
  wiresS : ℕ
  gateClauses : ℕ
  compileAt : ℕ
  blockAnd : ℕ
  blockMerge : ℕ
  outputUnits : ℕ
  matchBlock : ℕ
  -- sparse (Bad / Good)
  coordWire : ℕ
  rowWires : ℕ
  rowsWires : ℕ
  parityGates : ℕ
  rowBlock : ℕ
  rowBlocks : ℕ
  nonempty : ℕ
  filterNonempty : ℕ
  filterNonemptyC : ℕ
  normalizer : ℕ
  productParityGates : ℕ
  offsetPair : ℕ
  offsetPairs : ℕ
  pairingPairs : ℕ
  supportPairs : ℕ
  supportClause : ℕ
  supportClauses : ℕ
  pairingBlock : ℕ
  badBlock : ℕ
  set : ℕ
  recZero : ℕ
  recAddInc : ℕ
  recAddRow : ℕ
  synthesize : ℕ
  condEq : ℕ
  condEqs : ℕ
  cleaning : ℕ
  goodBlock : ℕ
  -- population counter
  adderGates : ℕ
  ripple : ℕ
  countTree : ℕ
  treeCombine : ℕ
  treeSplit : ℕ
  pow2Size : ℕ
  paddedWires : ℕ
  population : ℕ
  weightBlock : ℕ
  -- layer, cell, request
  pullback : ℕ
  layerBlock : ℕ
  witness : ℕ
  quantumBlock : ℕ
  quantumLayer : ℕ
  hashCell : ℕ
  quantumCell : ℕ
  units : ℕ
  request : ℕ
  query : ℕ
  baseQuery : ℕ
  cellQuery : ℕ
  queryFn : ℕ

/-! ## Type notations -/

scoped notation "TGate" => Ty.prod Ty.bool (Ty.prod Ty.bool (Ty.prod Ty.nat Ty.nat))
scoped notation "TGates" => Ty.list (Ty.prod Ty.bool (Ty.prod Ty.bool (Ty.prod Ty.nat Ty.nat)))
scoped notation "TWires" => Ty.list Ty.nat
scoped notation "TProg" =>
  Ty.prod (Ty.list (Ty.prod Ty.bool (Ty.prod Ty.bool (Ty.prod Ty.nat Ty.nat)))) (Ty.list Ty.nat)
scoped notation "TBlock" => Ty.prod Ty.nat (Ty.list (Ty.list (Ty.prod Ty.nat Ty.bool)))
scoped notation "TCoord" => Ty.prod Ty.bool Ty.nat
scoped notation "TRow" => Ty.list (Ty.prod Ty.bool Ty.nat)
scoped notation "TRows" => Ty.list (Ty.list (Ty.prod Ty.bool Ty.nat))
scoped notation "TEnvS" => Ty.prod Ty.nat Ty.nat
scoped notation "TEnvT" => Ty.prod (Ty.list Ty.nat) (Ty.prod Ty.nat Ty.nat)
scoped notation "TRec" =>
  Ty.prod (Ty.list (Ty.prod Ty.bool (Ty.prod Ty.bool (Ty.prod Ty.nat Ty.nat))))
    (Ty.prod (Ty.list Ty.nat) (Ty.list Ty.nat))

/-! ## Exact signatures -/

/-- A non-recursive function with the exact bounds of its body. -/
def FnSig.exact {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den) : FnSig a b where
  idx := i
  den := den
  cost x := body.cost (Env.one x) + 2
  depth x := body.depth (Env.one x) + 1
  msize x := body.msize (Env.one x)

@[simp] theorem FnSig.exact_idx {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den) :
    (FnSig.exact i body den).idx = i := rfl
@[simp] theorem FnSig.exact_den {a b : Ty} (i : ℕ) (body : Tm [a] b) (den : a.den → b.den)
    (x : a.den) : (FnSig.exact i body den).den x = den x := rfl

theorem FnSig.exact_valid {a b : Ty} {P : Program} {i : ℕ} {body : Tm [a] b}
    {den : a.den → b.den} (hP : P[i]? = some body.compile)
    (hcalls : ∀ x, body.CallsOK P (Env.one x)) (hden : ∀ x, body.den (Env.one x) = den x) :
    ∀ x, (FnSig.exact i body den).ValidAt P x :=
  FnSig.valid_of_body_nonrec _ body hP fun x =>
    ⟨hcalls x, hden x, le_refl _, le_refl _, le_refl _⟩

end QecReliability.Trans.Query
