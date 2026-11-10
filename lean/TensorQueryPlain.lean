import QecReliability.TensorQuantumEncoder
import Trans.Query.CorrLayer

/-! A total first-order query compiler for multiple cause classes. Malformed
index lists use zero for missing entries; typed correctness uses indexList. -/
namespace QecReliability.TensorQuery
open SharedCircuit OracleCost Trans.Query Trans.Query.Plain
open TensorBernstein TensorLatent

abbrev Item := ℕ × ℕ × ℕ

/-- Degree, starting cause wire, and requested Hamming weight. -/
def items : List ℕ → List ℕ → ℕ → List Item
  | [], _, _ => []
  | r :: ds, js, off => (r, off, js.headD 0) :: items ds (js.drop 1) (off+r)

def scanStep (s : ℕ × List ℕ × List Item) (r : ℕ) : ℕ × List ℕ × List Item :=
  (s.1+r, s.2.1.drop 1, (r,s.1,s.2.1.headD 0)::s.2.2)

theorem scan_eq (ds js : List ℕ) (off : ℕ) (acc : List Item) :
    (ds.foldl scanStep (off,js,acc)).2.2 = (items ds js off).reverse ++ acc := by
  induction ds generalizing js off acc with
  | nil => rfl
  | cons r ds ih =>
    rw [List.foldl_cons,scanStep,ih]
    simp only [items,List.reverse_cons,List.append_assoc,List.singleton_append]

/-- Two existing shifts implement the contiguous class wiring, preserving
the population counter's auxiliary wires above the complete primary block. -/
def weightOffset (v : ℕ) (a : Item) : BlockP :=
  let P := Plain.population a.1
  let first := (0,a.2.1)
  let second := (a.1+a.2.1,v-(a.1+a.2.1))
  Plain.matchBlock v
    (gatesS second (gatesS first P.1),wiresS second (wiresS first P.2))
    (QueryCodec.word ((max 1 a.1).size+1) a.2.2)

def weights (v : ℕ) (ds js : List ℕ) (off : ℕ := 0) : BlockP :=
  (items ds js off).foldr (fun a B => blockAnd v (weightOffset v a) B) (0,[])

def quantumLayer (n : ℕ) (ds : List ℕ) (rows : List (List Coord))
    (C : ProgP) (side : Bool) (js : List ℕ) : BlockP :=
  let w := witness n rows side
  blockAnd (ds.sum+2*n+w)
    (Plain.pullback n ds.sum w C (Plain.quantumBlock n rows side))
    (weights (ds.sum+2*n+w) ds js)

def quantumCell (n : ℕ) (ds : List ℕ) (rows : List (List Coord))
    (C : ProgP) (side : Bool) (js : List ℕ) (H : ProgP) (target : List Bool) : BlockP :=
  Plain.hashCell (ds.sum+2*n) (witness n rows side)
    (quantumLayer n ds rows C side js) H target

def query (isCell : Bool) (n : ℕ) (ds : List ℕ) (rows : List (List Coord))
    (C : ProgP) (side : Bool) (js : List ℕ) (H : ProgP)
    (target pre : List Bool) (D : ℕ) : List Bool :=
  Plain.query D (Plain.request (ds.sum+2*n) (witness n rows side)
    (if isCell then quantumCell n ds rows C side js H target
     else quantumLayer n ds rows C side js) pre)

private theorem gmap_comp (f g : ℕ → ℕ) (a : GateP) :
    gmap f (gmap g a) = gmap (f ∘ g) a := by
  unfold gmap
  split_ifs <;> rfl

theorem encBlock_weightOffset {r v : ℕ} (xs : Fin r → Fin v) (off j : ℕ)
    (hxs : ∀ i, (xs i).val = off+i.val) (hfit : off+r ≤ v) :
    encBlock (SharedCircuit.weightBlock xs j) = weightOffset v (r,off,j) := by
  have hw : liftσ xs = shiftWire (r+off,v-(r+off)) ∘ shiftWire (0,off) := by
    funext i
    simp only [liftσ,Function.comp_apply,shiftWire,not_lt_zero,ite_false]
    split_ifs with hi hj
    · simpa only [Nat.add_comm] using hxs ⟨i,hi⟩
    · omega
    · omega
    · omega
  rw [SharedCircuit.weightBlock,encBlock_matchBlock,encProg_rewire,
    encProg_population,ofFn_targetBits,counterDepth_eq]
  simp only [weightOffset,gatesS_eq,wiresS_eq,List.map_map,hw]
  congr 2
  apply congrArg (fun f => List.map f (Plain.population r).1)
  funext a
  exact (gmap_comp _ _ a).symm

set_option backward.isDefEq.respectTransparency false in
theorem encBlock_weights {v : ℕ} (ds : List ℕ) (xs : Fin ds.sum → Fin v)
    (j : Grid ds) (off : ℕ) (hxs : ∀ i, (xs i).val = off+i.val)
    (hfit : off+ds.sum ≤ v) :
    encBlock (TensorEncoding.weightsBlock ds xs j) = weights v ds (indexList ds j) off := by
  induction ds generalizing off with
  | nil => rfl
  | cons r ds ih =>
    simp only [TensorEncoding.weightsBlock,encBlock_and,weights,items,indexList,
      List.headD_cons,List.drop_succ_cons,List.drop_zero,List.foldr_cons]
    have hhead : off+r ≤ v := by simp only [List.sum_cons] at hfit; omega
    rw [encBlock_weightOffset (fun i => xs (Fin.castAdd ds.sum i)) off j.1.val
      (fun i => hxs _) hhead]
    congr 1
    exact ih _ _ (off+r) (fun i => by rw [hxs]; simp only [Fin.coe_natAdd]; omega)
      (by simpa only [List.sum_cons,Nat.add_assoc] using hfit)

theorem encBlock_quantumLayer (ds : List ℕ) {n : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (i : TensorCoefficientCounting.Index ds) :
    encBlock (TensorEncoding.quantumLayer ds rows C i) =
      quantumLayer n ds (encRows rows) (encProg C) i.1 (indexList ds i.2) := by
  rw [TensorEncoding.quantumLayer,encBlock_and,encBlock_pullback,
    encBlock_weights _ _ _ 0 (fun _ => by simp [LatentEncoding.causeWire])
      (by simp only [LatentEncoding.keySize]; omega),
    Trans.Query.encBlock_quantumBlock,witness_eq]
  simp only [quantumLayer,LatentEncoding.keySize]
  congr 2 <;> omega

theorem encBlock_quantumCell (ds : List ℕ) {n t : ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n)
    (i : TensorCoefficientCounting.Index ds)
    (H : SharedCircuit.Program (LatentEncoding.keySize n ds.sum) t) (target : BitModels t) :
    encBlock (TensorEncoding.quantumCell ds rows C i H target) =
      quantumCell n ds (encRows rows) (encProg C) i.1 (indexList ds i.2)
        (encProg H) (List.ofFn target) := by
  rw [TensorEncoding.quantumCell,encBlock_hashCell,encBlock_quantumLayer,witness_eq]
  simp only [quantumCell,LatentEncoding.keySize]
  congr 1 <;> omega

end QecReliability.TensorQuery
