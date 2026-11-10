import TensorQueryBoundary
import TensorFactorySeeds
import TensorMachineQueryFL
import TensorQueryFL
import Install.Remaining

/-! Actual compiled query bytes for the fixed all-length hash factory. Runtime
ordinals select the same tensor coefficient and exact stored seed slices used
by the source estimator. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.TensorMachine.RuntimeQueries
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t)
  (density : ℕ) (i : TensorQuery.FLCompiler.Indices) (compilerIdx : ℕ)

def compiler := QueryFL.compileF Install.wL Install.wC
  (TensorQuery.FLCompiler.queryF Trans.Query.stdIx i) (Install.theHash hD hd A)
  (data hD hd A).base (data hD hd A).den density 16 compilerIdx

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem compile_agrees {n : ℕ} {ds : List ℕ}
    (rows : List (List (PauliCoord n))) (C : SharedCircuit.Program ds.sum n) (m : ℕ)
    (coins : Fin (CodeHash.repeatBits (Factory.length hD hd A n ds)
      (Factory.width hD hd A n ds) m) → Bool) (key : RequestKey)
    (valid : ValidKey (keySize n ds.sum) (slots ds-1) m key) :
    (compiler hD hd A density i compilerIdx).den
      (ContextFL.externalData (data hD hd A).base (data hD hd A).den
        ds rows C (List.ofFn coins), Trans.Control.encKey key) =
      Boundary.query rows C (Factory.system hD hd A n ds).stages
        (Factory.circuits hD hd A n ds) m
        (LatentMachine.decodeCoins (Factory.length hD hd A n ds)
          (Factory.width hD hd A n ds) m coins) density key := by
  rw [Boundary.query_valid rows C _ _ m _ density key valid]
  have hgrid : ∀ j (hj : j < slots ds-1+1),
      (grid ds).getD j [] = TensorLatent.indexList ds (Boundary.index ds ⟨j,hj⟩) := by
    intro j hj
    have hj' : j < slots ds := by simpa only [Boundary.slots_pred_succ] using hj
    exact (grid_getD_ordinal ds ⟨j,hj'⟩).trans (indexList_eq_latent ds _)
  have hh : ∀ x, (Install.theHash hD hd A).den x =
      Trans.Hash.hashPlain x.1 x.2.1 x.2.2.1 (Install.thePg hD hd A)
        (Trans.Hash.gNbr actualMGG) x.2.2.2.1 x.2.2.2.2 := fun _ => rfl
  unfold compiler ContextFL.externalData LatentMachine.ContextFL.externalData
  cases key with
  | base side j rep =>
    dsimp only [Boundary.resolve]
    rw [QueryFL.compile_den_base Install.wL Install.wC
      (TensorQuery.FLCompiler.queryF Trans.Query.stdIx i) (Install.theHash hD hd A)
      (data hD hd A).base (data hD hd A).den density 16 compilerIdx]
    rw [TensorQuery.FLCompiler.query_den Trans.Query.stdIx i]
    exact (congrArg (fun js => TensorQuery.query false n ds
      (Trans.Query.encRows rows) (Trans.Query.encProg C) side js ([],[]) [] [] density)
      (hgrid j valid.1)).trans
        (TensorQuery.Service.query_base rows C (side,Boundary.index ds ⟨j,valid.1⟩)
          [] density ([],[]) [])
  | cell side j rep scale pre =>
    dsimp only [Boundary.resolve]
    rw [QueryFL.compile_den_cell Install.wL Install.wC
      (TensorQuery.FLCompiler.queryF Trans.Query.stdIx i) (Install.theHash hD hd A)
      (data hD hd A).base (data hD hd A).den density 16 compilerIdx]
    rw [TensorQuery.FLCompiler.query_den Trans.Query.stdIx i]
    let sb := Trans.Wire.seedB (data hD hd A).base (data hD hd A).den (keySize n ds.sum)
    let bits := ((List.ofFn coins).drop (rep*sb)).take sb
    have hb : bits.length = CodeHash.seedBits (Factory.length hD hd A n ds)
        (Factory.width hD hd A n ds) := by
      dsimp only [bits,sb]
      rw [Factory.seed_length]
      exact LatentMachine.Factory.slice_length _ _ m coins rep valid.2.1
    have hseed := LatentMachine.Factory.decode_slice
      (Factory.length hD hd A n ds) (Factory.width hD hd A n ds) m coins ⟨rep,valid.2.1⟩
    have hseed' : LatentMachine.decodeCoins (Factory.length hD hd A n ds)
        (Factory.width hD hd A n ds) m coins ⟨rep,valid.2.1⟩ =
          Trans.Hash.seedOfBits (Factory.length hD hd A n ds)
            (Factory.width hD hd A n ds) bits := by
      dsimp only [bits,sb]
      rw [Factory.seed_length]
      exact hseed
    have hhash : (Install.theHash hD hd A).den
        ((data hD hd A).base,(data hD hd A).den,keySize n ds.sum,scale,bits) =
          Trans.Query.encProg ((Factory.circuits hD hd A n ds).program
            ⟨scale,valid.2.2.1⟩ (LatentMachine.decodeCoins (Factory.length hD hd A n ds)
              (Factory.width hD hd A n ds) m coins ⟨rep,valid.2.1⟩)) := by
      have hh0 := hh ((data hD hd A).base,(data hD hd A).den,keySize n ds.sum,scale,bits)
      have hp := Factory.hash_program hD hd A n ds ⟨scale,valid.2.2.1⟩ bits hb
      have he := congrArg (fun seed => Trans.Query.encProg
        ((Factory.circuits hD hd A n ds).program ⟨scale,valid.2.2.1⟩ seed)) hseed'.symm
      dsimp only [Prod.fst,Prod.snd,Install.thePg] at hh0
      exact hh0.trans (hp.symm.trans he)
    exact (congrArg₂ (fun js hp => TensorQuery.query true n ds
      (Trans.Query.encRows rows) (Trans.Query.encProg C) side js hp
        (List.replicate scale false) pre density) (hgrid j valid.1) hhash).trans
          (TensorQuery.Service.query_cell rows C (Factory.system hD hd A n ds).stages
            (Factory.circuits hD hd A n ds) (side,Boundary.index ds ⟨j,valid.1⟩)
            ⟨scale,valid.2.2.1⟩ (LatentMachine.decodeCoins (Factory.length hD hd A n ds)
              (Factory.width hD hd A n ds) m coins ⟨rep,valid.2.1⟩) pre density)

end QecReliability.TensorMachine.RuntimeQueries
