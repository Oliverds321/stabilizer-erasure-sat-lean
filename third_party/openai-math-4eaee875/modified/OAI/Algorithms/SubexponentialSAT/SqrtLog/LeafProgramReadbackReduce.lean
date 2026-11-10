import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramReadback
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel

namespace OAI.Algorithms

/-! The count reader reduces the extracted scalar word before returning it.
It therefore works for arbitrary valid coefficient codes, including codes
with noncanonical representatives of zero. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Readback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ProgramLinking SubexponentialSAT.SubexpFlatCount

private theorem cons_at_1 {α : Type} (a : α) (v : Fin 1 → α) :
    Matrix.vecCons a v (1 : Fin 2) = v (0 : Fin 1) := by
  rfl

private theorem cons_at_2 {α : Type} (a : α) (v : Fin 2 → α) :
    Matrix.vecCons a v (2 : Fin 3) = v (1 : Fin 2) := by
  rfl

private theorem cons_at_3 {α : Type} (a : α) (v : Fin 3 → α) :
    Matrix.vecCons a v (3 : Fin 4) = v (2 : Fin 3) := by
  rfl

private theorem cons_at_4 {α : Type} (a : α) (v : Fin 4 → α) :
    Matrix.vecCons a v (4 : Fin 5) = v (3 : Fin 4) := by
  rfl

private theorem cons_at_5 {α : Type} (a : α) (v : Fin 5 → α) :
    Matrix.vecCons a v (5 : Fin 6) = v (4 : Fin 5) := by
  rfl

private theorem cons_at_6 {α : Type} (a : α) (v : Fin 6 → α) :
    Matrix.vecCons a v (6 : Fin 7) = v (5 : Fin 6) := by
  rfl

private theorem cons_at_7 {α : Type} (a : α) (v : Fin 7 → α) :
    Matrix.vecCons a v (7 : Fin 8) = v (6 : Fin 7) := by
  rfl

private theorem embed_remainder (pc : Option (Fin 89)) (regs frameRegs : Fin 8 → Bool)
    (input modulus word width : List Bool) :
    embedCfg id decoderPorts id none
      (⟨none, frameRegs, store [] modulus [] width⟩ : Cfg 8 8 89)
      ⟨pc, regs, ModularDivisionPrograms.resting input modulus word⟩ =
      ⟨pc, regs, store input modulus word width⟩ := by
  apply embedCfg_eq_of_ports id decoderPorts id none _ _ _
    Function.injective_id decoderPorts_injective
  · cases pc <;> rfl
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · exact False.elim (hi ⟨6, rfl⟩)
    · change store input modulus word width (7 : Fin 8) = store [] modulus [] width (7 : Fin 8)
      simp only [store, cons_at_1, cons_at_2, cons_at_3, cons_at_4, cons_at_5, cons_at_6, cons_at_7, Matrix.cons_val_zero]

abbrev remainderProgram : Program 8 8 89 :=
  liftProgram ModularDivisionPrograms.remainderProgram id decoderPorts

theorem remainder_eval (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    ∃ n finalRegs, n ≤ 100 * (modulus.length + word.length + 1)^2 ∧
      Eval (.call remainderProgram) n (finish regs modulus width word)
        ⟨finalRegs, store (ModularArithmetic.reduce modulus word) modulus [] width⟩ := by
  obtain ⟨finalRegs, n, hn, ht⟩ := ModularDivisionPrograms.remainder_correct regs modulus word
  have h := liftProgram_trace ModularDivisionPrograms.remainderProgram id decoderPorts
    (⟨none, regs, store [] modulus [] width⟩ : Cfg 8 8 89)
    Function.injective_id decoderPorts_injective ht
  rw [embed_remainder, embed_remainder] at h
  exact ⟨n, finalRegs, hn, .call _ h⟩

abbrev countCommand : Cmd 8 8 := .seq extractCmd (.call remainderProgram)
def countProgram := compiled countCommand 0 0

theorem countProgram_run {B : ℕ} (hB : 0 < B)
    (word suffix : List Bool) (hword : word.length = B)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B) :
    ∃ finalRegs, RunsIn countProgram (budget B modulus (word ++ suffix))
      ((start regs modulus width (word ++ suffix)).withPC (some countProgram.entry))
      (⟨none, finalRegs, store (ModularArithmetic.reduce modulus word) modulus [] width⟩ : Cfg 8 8 _) := by
  have he := extract_eval hB word suffix hword regs modulus width hwidth
  obtain ⟨n, finalRegs, hn, ht⟩ := remainder_eval (reset regs) modulus width word
  refine ⟨finalRegs, 14 * B + 2 * suffix.length + 16 + n + 1, ?_,
    compiled_halt_trace (he.seq ht) 0 0⟩
  dsimp [budget]
  simp only [List.length_append, hword] at *
  nlinarith

open RingProgram SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

theorem firstWord_mod_eq (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) (z : ℕ)
    (hz : z < 3^t) (hx : (modelRing t ht hd a M cache).decode x = (z : a.O t)) :
    BinaryArithmetic.toNat (x ⟨0, hd⟩).val % 3^t = z := by
  have h := congrArg (a.decodeCount t ht) hx
  rw [a.decodeCount_natCast t ht (Nat.ne_of_gt hd) z hz] at h
  unfold RingModel.Data.decodeCount at h
  rw [modelRing_readBase] at h
  simpa [wordValue, ZMod.val_natCast] using h

theorem reduced_firstWord_value (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) (z : ℕ)
    (hz : z < 3^t) (hx : (modelRing t ht hd a M cache).decode x = (z : a.O t))
    (modulus : List Bool) (hm : BinaryArithmetic.toNat modulus = 3^t) :
    BinaryArithmetic.toNat (ModularArithmetic.reduce modulus (x ⟨0, hd⟩).val) = z := by
  rw [ModularArithmetic.reduce_correct _ _ (by rw [hm]; positivity), hm]
  exact firstWord_mod_eq t ht hd a M cache x z hz hx

end SubexponentialSAT.SqrtLog.LeafProgram.Readback

end OAI.Algorithms
