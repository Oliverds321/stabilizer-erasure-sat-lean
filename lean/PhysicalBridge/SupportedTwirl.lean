import PhysicalBridge.CoordinateSplit
import PhysicalBridge.ReindexChannels
import PhysicalBridge.SubsystemTwirl

/-! The uniform physical Pauli channel supported on E becomes maximally
mixed replacement under the actual survivor/erased-coordinate split. -/
noncomputable section
namespace QecPhysical.BinaryPauli
open scoped BigOperators Kronecker
open Matrix
open QecReliability.Binary
variable {n : ℕ} (E : Finset (Fin n))

theorem supportedPauli_split (u : Pauli (Fintype.card E)) :
    (pauli (supportedLabelEquiv E u).val).submatrix (wordSplit E).symm (wordSplit E).symm =
      (1 : Square (SurvivorWord E)) ⊗ₖ pauli u := by
  ext p q
  have hs (q : SurvivorWord E × ErasedWord E) :
      wordSplit E (joinWord E q + extendErased E u.1) = (q.1,q.2+u.1) := by
    rw [wordSplit_add_extend, survivorPart_join, erasedPart_join]
  have hj (p : SurvivorWord E × ErasedWord E) : wordSplit E (joinWord E p) = p :=
    (wordSplit E).apply_symm_apply p
  have heq : joinWord E p = joinWord E q + extendErased E u.1 ↔ p=(q.1,q.2+u.1) := by
    constructor
    · intro h
      simpa only [hj,hs] using congrArg (wordSplit E) h
    · intro h
      apply (wordSplit E).injective
      simpa only [hj,hs] using h
  change (if joinWord E p = joinWord E q + extendErased E u.1 then
    bitSign (wordDot (extendErased E u.2) (joinWord E q)) else 0) = _
  rw [wordDot_extend, erasedPart_join]
  simp only [heq, Prod.ext_iff, Matrix.kroneckerMap_apply, Matrix.one_apply, pauli]
  by_cases h₁ : p.1=q.1 <;> by_cases h₂ : p.2=q.2+u.1 <;> simp [h₁,h₂]

def supportedTwirl : Channel (Word n) (Word n) :=
  uniformChannel (fun u : supported E => isometryChannel (pauli u.val) (pauli_unitary u.val))

theorem supportedTwirl_split :
    (reindexChannel (wordSplit E)).map.comp (supportedTwirl E).map =
      (mixedReplacement : Channel (SurvivorWord E × ErasedWord E)
        (SurvivorWord E × ErasedWord E)).map.comp (reindexChannel (wordSplit E)).map := by
  change (reindexMap (wordSplit E)).comp
    (uniformMap (fun u : supported E => conjugateMap (pauli u.val))) = _
  rw [← uniformMap_reindex (supportedLabelEquiv E) (fun u : supported E =>
    conjugateMap (pauli u.val)), comp_uniformMap]
  have h (u : Pauli (Fintype.card E)) :
      (reindexMap (wordSplit E)).comp (conjugateMap (pauli (supportedLabelEquiv E u).val)) =
      (conjugateMap ((1 : Square (SurvivorWord E)) ⊗ₖ pauli u)).comp (reindexMap (wordSplit E)) := by
    rw [reindexMap_conjugate, supportedPauli_split]
  rw [funext h, ← uniformMap_comp]
  have ht := (binaryResolution (Fintype.card E)).twirlRight (a:=SurvivorWord E)
    (Fintype.card_prod _ _)
  change uniformMap (fun u : Pauli (Fintype.card E) =>
    conjugateMap ((1 : Square (SurvivorWord E)) ⊗ₖ pauli u)) =
      (mixedReplacement : Channel (SurvivorWord E × ErasedWord E)
        (SurvivorWord E × ErasedWord E)).map at ht
  rw [ht]
  rfl

end QecPhysical.BinaryPauli
