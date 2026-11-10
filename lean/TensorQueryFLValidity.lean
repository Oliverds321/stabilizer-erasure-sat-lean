import TensorQueryFL

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace QecReliability.TensorQuery.FLCompiler
open FL FL.Lib FL.Tm Trans.Query
open Trans.Control (bodySig_valid)

structure Indices.OK (x : Ix) (i : Indices) (P : FL.Program) : Prop where
  scanStep : P[i.scanStep]? = some (scanStepBody x).compile
  scanFold : P[i.scanFold]? = some (foldlBody (scanStepF x i) i.scanFold).compile
  reverseAux : P[i.reverseAux]? = some (revAppBody TItem i.reverseAux).compile
  reverseItems : P[i.reverseItems]? = some (reverseBody TItem i.reverseAux).compile
  items : P[i.items]? = some (itemsBody x i).compile
  sumFold : P[i.sumFold]? = some (foldrBody (addF x.add) i.sumFold).compile
  weight : P[i.weight]? = some (weightBody x).compile
  weightsStep : P[i.weightsStep]? = some (weightsStepBody x i).compile
  weightsFold : P[i.weightsFold]? = some (foldrBody (weightsStepF x i) i.weightsFold).compile
  weights : P[i.weights]? = some (weightsBody x i).compile
  layer : P[i.layer]? = some (layerBody x i).compile
  query : P[i.query]? = some (queryBody x i).compile

/-- Previously certified scalar/circuit/query routines used by the new bodies. -/
structure Dependencies (x : Ix) (P : FL.Program) : Prop where
  lib : LibOK P x
  population : ∀ p, (populationF x).ValidAt P p
  gates : ∀ p, (gatesSF x).ValidAt P p
  wires : ∀ p, (wiresSF x).ValidAt P p
  word : ∀ p, (wordF x.word).ValidAt P p
  matchBlock : ∀ p, (matchBlockF x).ValidAt P p
  blockAnd : ∀ p, (blockAndF x).ValidAt P p
  witness : ∀ p, (witnessF x).ValidAt P p
  quantumBlock : ∀ p, (quantumBlockF x).ValidAt P p
  pullback : ∀ p, (pullbackF x).ValidAt P p
  hashCell : ∀ p, (hashCellF x).ValidAt P p
  request : ∀ p, (requestF x).ValidAt P p
  serialize : ∀ p, (Trans.Query.queryF x).ValidAt P p

variable {x : Ix} {i : Indices} {P : FL.Program}

theorem scanStep_valid (h : Dependencies x P) (hi : i.OK x P) :
    ∀ p, (scanStepF x i).ValidAt P p := by
  intro p
  apply bodySig_valid hi.scanStep
  simp [scanStepBody,tm_simp,h.lib]

theorem items_valid (h : Dependencies x P) (hi : i.OK x P) :
    ∀ p, (itemsF x i).ValidAt P p := by
  have hs := Trans.Hash.foldl_validAll (scanStep_valid h hi) hi.scanFold
  have hr := reverse_valid (revApp_valid hi.reverseAux) hi.reverseItems
  intro p
  apply bodySig_valid hi.items
  simp [itemsBody,tm_simp,hs,hr]

theorem sum_valid (h : Dependencies x P) (hi : i.OK x P) :
    ∀ p, (foldrF (addF x.add) i.sumFold).ValidAt P p :=
  Trans.Hash.foldr_validAll h.lib.add hi.sumFold

theorem weight_valid (h : Dependencies x P) (hi : i.OK x P) :
    ∀ p, (weightF x i).ValidAt P p := by
  intro p
  apply bodySig_valid hi.weight
  simp [weightBody,tm_simp,h.lib,h.population,h.gates,h.wires,h.word,h.matchBlock]

theorem weightsStep_valid (h : Dependencies x P) (hi : i.OK x P) :
    ∀ p, (weightsStepF x i).ValidAt P p := by
  intro p
  apply bodySig_valid hi.weightsStep
  simp [weightsStepBody,tm_simp,weight_valid h hi,h.blockAnd]

theorem weights_valid (h : Dependencies x P) (hi : i.OK x P) :
    ∀ p, (weightsF x i).ValidAt P p := by
  have hf := Trans.Hash.foldr_validAll (weightsStep_valid h hi) hi.weightsFold
  intro p
  apply bodySig_valid hi.weights
  simp [weightsBody,tm_simp,hf,items_valid h hi]

theorem layer_valid (h : Dependencies x P) (hi : i.OK x P) :
    ∀ p, (layerF x i).ValidAt P p := by
  intro p
  apply bodySig_valid hi.layer
  simp [layerBody,tm_simp,h.lib,sum_valid h hi,weights_valid h hi,
    h.witness,h.blockAnd,h.pullback,h.quantumBlock]

theorem query_valid (h : Dependencies x P) (hi : i.OK x P) :
    ∀ p, (queryF x i).ValidAt P p := by
  intro p
  apply bodySig_valid hi.query
  simp [queryBody,tm_simp,argN,argDs,argRows,argC,argSide,argJs,argH,argTarget,argPre,argD,
    h.lib,sum_valid h hi,layer_valid h hi,h.witness,h.serialize,h.request,h.hashCell]

set_option maxHeartbeats 1000000 in
/-- The actual installed FL query builder computes the serialized SAT word.
The bounds here are the compiled body's concrete compositional resource bounds. -/
theorem query_computes (h : Dependencies x P) (hi : i.OK x P)
    (isCell : Bool) (n : ℕ) (ds : List ℕ) (rows : List (List Plain.Coord))
    (C : Plain.ProgP) (side : Bool) (js : List ℕ) (H : Plain.ProgP)
    (target pre : List Bool) (D : ℕ) :
    let p : TArg.den := (isCell,n,ds,rows,C,side,js,H,target,pre,D)
    FL.Computes P i.query (TArg.enc p)
      (Ty.enc TBits (TensorQuery.query isCell n ds rows C side js H target pre D))
      (max ((queryF x i).msize p) (TArg.enc p).size)
      ((queryF x i).cost p) ((queryF x i).depth p) := by
  dsimp only
  have hc := (query_valid h hi (isCell,n,ds,rows,C,side,js,H,target,pre,D)).computes
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [query_den x i isCell n ds rows C side js H target pre D] at hc
  exact hc

def indices (base : ℕ) : Indices where
  scanStep := base
  scanFold := base+1
  reverseAux := base+2
  reverseItems := base+3
  items := base+4
  sumFold := base+5
  weight := base+6
  weightsStep := base+7
  weightsFold := base+8
  weights := base+9
  layer := base+10
  query := base+11

/-- Twelve executable bodies, ready to append to a program containing the
existing query library. Index placement is explicit and checked by `Indices.OK`. -/
def bodies (x : Ix) (base : ℕ) : FL.Program :=
  let i := indices base
  [(scanStepBody x).compile,
   (foldlBody (scanStepF x i) i.scanFold).compile,
   (revAppBody TItem i.reverseAux).compile,
   (reverseBody TItem i.reverseAux).compile,
   (itemsBody x i).compile,
   (foldrBody (addF x.add) i.sumFold).compile,
   (weightBody x).compile,
   (weightsStepBody x i).compile,
   (foldrBody (weightsStepF x i) i.weightsFold).compile,
   (weightsBody x i).compile,
   (layerBody x i).compile,
   (queryBody x i).compile]

theorem bodies_length (x : Ix) (base : ℕ) : (bodies x base).length = 12 := rfl

theorem appended_ok (x : Ix) (P : FL.Program) :
    (indices P.length).OK x (P ++ bodies x P.length) := by
  constructor <;> simp [indices,bodies,List.getElem?_append_right]

end QecReliability.TensorQuery.FLCompiler
