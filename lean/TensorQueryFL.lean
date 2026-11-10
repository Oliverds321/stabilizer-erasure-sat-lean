import TensorQueryPlain
import Trans.Query.Main
import Trans.Wire.Header

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace QecReliability.TensorQuery.FLCompiler
open FL FL.Lib FL.Tm Trans.Query
open Trans.Control (bodySig bodySig_den bodySig_valid)

abbrev TItem : Ty := .prod .nat (.prod .nat .nat)
abbrev TScan : Ty := .prod .nat (.prod (.list .nat) (.list TItem))
abbrev TWeights : Ty := .prod .nat (.prod (.list .nat) (.list .nat))
abbrev TLayer : Ty := .prod .nat (.prod (.list .nat)
  (.prod TRows (.prod TProg (.prod .bool (.list .nat)))))
abbrev TArg : Ty := .prod .bool (.prod .nat (.prod (.list .nat)
  (.prod TRows (.prod TProg (.prod .bool (.prod (.list .nat)
    (.prod TProg (.prod (.list .bool) (.prod (.list .bool) .nat)))))))))

structure Indices where
  scanStep : ℕ
  scanFold : ℕ
  reverseAux : ℕ
  reverseItems : ℕ
  items : ℕ
  sumFold : ℕ
  weight : ℕ
  weightsStep : ℕ
  weightsFold : ℕ
  weights : ℕ
  layer : ℕ
  query : ℕ

def scanStepBody (x : Ix) : Tm [.prod TScan .nat] TScan :=
  .pair (.app (addF x.add) (.pair (.fst (.fst v0)) (.snd v0)))
    (.pair (.app (dropF .nat x.drop) (.pair (.lit (1:ℕ)) (.fst (.snd (.fst v0)))))
      (.lcons (.pair (.snd v0) (.pair (.fst (.fst v0))
        (.app (getDF .nat x.getD) (.pair (.fst (.snd (.fst v0))) (.pair .zero .zero)))))
        (.snd (.snd (.fst v0)))))

def scanStepF (x : Ix) (i : Indices) := bodySig i.scanStep (scanStepBody x)

theorem scanStep_den (x : Ix) (i : Indices) (s : TScan.den) (r : ℕ) :
    (scanStepF x i).den (s,r) = scanStep s r := by
  rcases s with ⟨off,js,acc⟩
  cases js <;> simp [scanStepF,bodySig_den,scanStepBody,tm_simp,scanStep]

theorem scanFold_den (x : Ix) (i : Indices) (s : TScan.den) (ds : List ℕ) :
    foldlDen (scanStepF x i) s ds = ds.foldl scanStep s := by
  induction ds generalizing s with
  | nil => rfl
  | cons r ds ih => rw [foldlDen_cons,scanStep_den,ih,List.foldl_cons]

def itemsBody (x : Ix) (i : Indices) : Tm [.prod (.list .nat) (.list .nat)] (.list TItem) :=
  .app (reverseF TItem i.reverseItems)
    (.snd (.snd (.app (foldlF (scanStepF x i) i.scanFold)
      (.pair (.pair .zero (.pair (.snd v0) .lnil)) (.fst v0)))))

def itemsF (x : Ix) (i : Indices) := bodySig i.items (itemsBody x i)

theorem items_den (x : Ix) (i : Indices) (ds js : List ℕ) :
    (itemsF x i).den (ds,js) = items ds js 0 := by
  simp only [itemsF,bodySig_den,itemsBody,tm_simp,reverseF_den,foldlF_den,
    scanFold_den,scan_eq,List.append_nil,List.reverse_reverse]

theorem sumFold_den (x : Ix) (ds : List ℕ) :
    foldrDen (addF x.add) ds 0 = ds.sum := by
  induction ds with
  | nil => rfl
  | cons r ds ih =>
    change r + foldrDen (addF x.add) ds 0 = r + ds.sum
    exact congrArg (r + ·) ih

/-- Input is the full primary width and one class descriptor. -/
def weightBody (x : Ix) : Tm [.prod .nat TItem] TBlock :=
  .letE (.app (populationF x) (.fst (.snd v0))) <|
  .letE (.app (addF x.add) (.pair (.fst (.snd v1)) (.fst (.snd (.snd v1))))) <|
  .letE (.pair v0 (.app (subF x.sub) (.pair (.fst v2) v0))) <|
  .letE (.pair .zero (.fst (.snd (.snd v3)))) <|
  .app (matchBlockF x) (.pair (.fst v4) (.pair
    (.pair (.app (gatesSF x) (.pair v1 (.app (gatesSF x) (.pair v0 (.fst v3)))) )
      (.app (wiresSF x) (.pair v1 (.app (wiresSF x) (.pair v0 (.snd v3))))))
    (.app (wordF x.word) (.pair
      (.app (succF x.succ) (.app (bitLenF x.bitLen)
        (.app (maxF x.max) (.pair (.lit (1:ℕ)) (.fst (.snd v4))))))
      (.snd (.snd (.snd v4)))))))

def weightF (x : Ix) (i : Indices) := bodySig i.weight (weightBody x)

theorem weight_den (x : Ix) (i : Indices) (v : ℕ) (a : Item) :
    (weightF x i).den (v,a) = weightOffset v a := by
  simp [weightF,bodySig_den,weightBody,tm_simp,weightOffset]

/-- The fold carries the primary width unchanged. -/
def weightsStepBody (x : Ix) (i : Indices) :
    Tm [.prod TItem (.prod .nat TBlock)] (.prod .nat TBlock) :=
  .pair (.fst (.snd v0)) (.app (blockAndF x)
    (.pair (.fst (.snd v0)) (.pair
      (.app (weightF x i) (.pair (.fst (.snd v0)) (.fst v0))) (.snd (.snd v0)))))

def weightsStepF (x : Ix) (i : Indices) := bodySig i.weightsStep (weightsStepBody x i)

theorem weightsStep_den (x : Ix) (i : Indices) (a : Item) (v : ℕ) (B : Plain.BlockP) :
    (weightsStepF x i).den (a,v,B) = (v,Plain.blockAnd v (weightOffset v a) B) := by
  simp only [weightsStepF,bodySig_den,weightsStepBody,tm_simp,blockAndF_den]
  exact congrArg (fun B' => (v,Plain.blockAnd v B' B)) (weight_den x i v a)

theorem weightsFold_den (x : Ix) (i : Indices) (as : List Item) (v : ℕ) (B : Plain.BlockP) :
    foldrDen (weightsStepF x i) as (v,B) =
      (v,as.foldr (fun a B => Plain.blockAnd v (weightOffset v a) B) B) := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [foldrDen_cons,ih,weightsStep_den,List.foldr_cons]

def weightsBody (x : Ix) (i : Indices) : Tm [TWeights] TBlock :=
  .snd (.app (foldrF (weightsStepF x i) i.weightsFold)
    (.pair (.app (itemsF x i) (.snd v0)) (.pair (.fst v0) (.pair .zero .lnil))))

def weightsF (x : Ix) (i : Indices) := bodySig i.weights (weightsBody x i)

theorem weights_den (x : Ix) (i : Indices) (v : ℕ) (ds js : List ℕ) :
    (weightsF x i).den (v,ds,js) = weights v ds js := by
  simp only [weightsF,bodySig_den,weightsBody,tm_simp,foldrF_den]
  have hi := congrArg (fun as => (foldrDen (weightsStepF x i) as (v,0,[])).2)
    (items_den x i ds js)
  have hf := congrArg Prod.snd (weightsFold_den x i (items ds js 0) v (0,[]))
  exact hi.trans hf

def layerBody (x : Ix) (i : Indices) : Tm [TLayer] TBlock :=
  .letE (.app (foldrF (addF x.add) i.sumFold) (.pair (.fst (.snd v0)) .zero)) <|
  .letE (.app (witnessF x) (.pair (.fst v1)
    (.pair (.fst (.snd (.snd v1))) (.fst (.snd (.snd (.snd (.snd v1)))))))) <|
  .letE (.app (addF x.add) (.pair (.app (addF x.add)
    (.pair v1 (.app (mulF x.mul) (.pair (.lit (2:ℕ)) (.fst v2)))) ) v0)) <|
  .app (blockAndF x) (.pair v0 (.pair
    (.app (pullbackF x) (.pair (.fst v3) (.pair v2 (.pair v1
      (.pair (.fst (.snd (.snd (.snd v3))))
        (.app (quantumBlockF x) (.pair (.fst v3) (.pair (.fst (.snd (.snd v3)))
          (.fst (.snd (.snd (.snd (.snd v3)))))))))))))
    (.app (weightsF x i) (.pair v0 (.pair (.fst (.snd v3))
      (.snd (.snd (.snd (.snd (.snd v3))))))))))

def layerF (x : Ix) (i : Indices) := bodySig i.layer (layerBody x i)

theorem layer_den (x : Ix) (i : Indices) (n : ℕ) (ds : List ℕ)
    (rows : List (List Plain.Coord)) (C : Plain.ProgP) (side : Bool) (js : List ℕ) :
    (layerF x i).den (n,ds,rows,C,side,js) = quantumLayer n ds rows C side js := by
  simp [layerF,bodySig_den,layerBody,tm_simp,sumFold_den,quantumLayer]
  exact congrArg (Plain.blockAnd (ds.sum+2*n+Plain.witness n rows side)
    (Plain.pullback n ds.sum (Plain.witness n rows side) C (Plain.quantumBlock n rows side)))
      (weights_den x i _ ds js)

/- Readable projections keep the final wrapper's nested argument format stable. -/
def argN {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ .nat := .fst (.snd p)
def argDs {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ (.list .nat) := .fst (.snd (.snd p))
def argRows {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ TRows := .fst (.snd (.snd (.snd p)))
def argC {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ TProg := .fst (.snd (.snd (.snd (.snd p))))
def argSide {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ .bool := .fst (.snd (.snd (.snd (.snd (.snd p)))))
def argJs {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ (.list .nat) := .fst (.snd (.snd (.snd (.snd (.snd (.snd p))))))
def argH {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ TProg := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))
def argTarget {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ (.list .bool) := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p))))))))
def argPre {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ (.list .bool) := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))))
def argD {Γ : List Ty} (p : Tm Γ TArg) : Tm Γ .nat := .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))))

def queryBody (x : Ix) (i : Indices) : Tm [TArg] TBits :=
  .letE (.app (addF x.add) (.pair
    (.app (foldrF (addF x.add) i.sumFold) (.pair (argDs v0) .zero))
    (.app (mulF x.mul) (.pair (.lit (2:ℕ)) (argN v0))))) <|
  .letE (.app (witnessF x) (.pair (argN v1) (.pair (argRows v1) (argSide v1)))) <|
  .letE (.app (layerF x i) (.pair (argN v2) (.pair (argDs v2)
    (.pair (argRows v2) (.pair (argC v2) (.pair (argSide v2) (argJs v2))))))) <|
  .app (queryF x) (.pair (argD v3) (.app (requestF x)
    (.pair v2 (.pair v1 (.pair
      (.ite (.fst v3)
        (.app (hashCellF x) (.pair v2 (.pair v1 (.pair v0 (.pair (argH v3) (argTarget v3)))))) v0)
      (argPre v3))))))

def queryF (x : Ix) (i : Indices) := bodySig i.query (queryBody x i)

theorem query_den (x : Ix) (i : Indices) (isCell : Bool) (n : ℕ) (ds : List ℕ)
    (rows : List (List Plain.Coord)) (C : Plain.ProgP) (side : Bool) (js : List ℕ)
    (H : Plain.ProgP) (target pre : List Bool) (D : ℕ) :
    (queryF x i).den (isCell,n,ds,rows,C,side,js,H,target,pre,D) =
      TensorQuery.query isCell n ds rows C side js H target pre D := by
  cases isCell <;> simp [queryF,bodySig_den,queryBody,tm_simp,sumFold_den,
    argN,argDs,argRows,argC,argSide,argJs,argH,argTarget,argPre,argD,
    TensorQuery.query,quantumCell]
  · exact congrArg (fun B => Plain.query D (Plain.request (ds.sum+2*n)
      (Plain.witness n rows side) B pre)) (layer_den x i n ds rows C side js)
  · exact congrArg (fun B => Plain.query D (Plain.request (ds.sum+2*n)
      (Plain.witness n rows side) (Plain.hashCell (ds.sum+2*n)
        (Plain.witness n rows side) B H target) pre)) (layer_den x i n ds rows C side js)

end QecReliability.TensorQuery.FLCompiler
