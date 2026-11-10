import LatentRuntimeAgreement
import Trans.Bounds.Loop

/-! Actual unchanged auxiliary slots of the latent runtime. Bounds depend on
encoded state sizes (including output numerators/denominators), not their values.
No iid dimensions, true-mode repair, or assumed auxiliary implementation. -/
set_option autoImplicit false
noncomputable section
namespace QecReliability.LatentMachine.Runtime
open FL Trans.Wire Trans.Control
open SharedCircuit SharedCircuit.LatentEncoding
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.WholeWrapperCandidate

/-- Actual fixed indices: only initialization and step differ from the old table. -/
def assemblyIndices : Assembly.Indices :=
  { Install.topIdx with init := 297, step := 308 }

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
local notation "CX" => controller hD hd A density
local notation "PP" => program hD hd A density

private theorem auxiliary_extends : Install.Extends (Install.theProg hD hd A density) PP :=
  ControllerInstalled.extends_prefix _ _ _ _ _ _

theorem auxiliary_isDone_valid (a : (TArg TX).den) : (isDoneF CX).ValidAt PP a :=
  Install.ValidAt.extend (auxiliary_extends hD hd A density) (Install.isDone_ok a)

theorem auxiliary_isInvoke_valid (a : (TArg TX).den) : (isInvokeF CX).ValidAt PP a :=
  Install.ValidAt.extend (auxiliary_extends hD hd A density) (Install.isInvoke_ok a)

theorem auxiliary_query_valid (a : (TArg TX).den) : (queryOfF CX).ValidAt PP a :=
  Install.ValidAt.extend (auxiliary_extends hD hd A density) (Install.queryOf_ok a)

theorem auxiliary_output_valid (a : (TArg TX).den) :
    (Trans.Bounds.outputF Install.oX TX).ValidAt PP a :=
  Install.ValidAt.extend (auxiliary_extends hD hd A density) (Install.output_ok a)

theorem auxiliary_resume_valid (a : (Ty.prod Ty.bool (TArg TX)).den) :
    (Trans.Bounds.resumeTopF Install.oX CX).ValidAt PP a :=
  Install.ValidAt.extend (auxiliary_extends hD hd A density)
    (Install.resumeTop_ok (Install.theHash_ok hD hd A density) a)

/-- One numeric resource scale for the auxiliary routines. -/
def auxiliaryValue (S : ℕ) : ℕ := 40*S+260
def auxiliaryCost (S : ℕ) : ℕ := 1100*(S+1)^3+4000
def auxiliaryDepth (S : ℕ) : ℕ := 10*(S+1)^2+21

private theorem auxiliary_computes {a b : Ty} {F : FnSig a b} {x : a.den} {S : ℕ}
    (hv : F.ValidAt PP x) (hm : F.msize x ≤ auxiliaryValue S)
    (hx : (a.enc x).size ≤ auxiliaryValue S)
    (ht : F.cost x ≤ auxiliaryCost S) (hdp : F.depth x ≤ auxiliaryDepth S) :
    Computes PP F.idx (a.enc x) (b.enc (F.den x))
      (auxiliaryValue S) (auxiliaryCost S) (auxiliaryDepth S) := by
  obtain ⟨hi,t,d,ht',hd',he⟩ := hv.computes hm hx
  exact ⟨hi,t,d,ht'.trans ht,hd'.trans hdp,he⟩

variable (q r B m : ℕ) (X : TX.den) (s : Config) (S : ℕ)
local notation "ctx" => encCtx q r B m X
local notation "arg" => (ctx,encCfg s)

/-- The installed stop test includes fault; no global no-fault premise is hidden. -/
theorem auxiliary_isDone_terminal (ext : External) :
    (isDoneF CX).den arg = true ↔
      WholeWrapperCandidate.step q r B m false ext s = none := by
  have h := Trans.Control.isDone_correct CX q r B m X ext s
  rw [Trans.Control.step_none_iff q r B m ext s true] at h
  rw [Trans.Control.step_none_iff q r B m ext s false]
  exact h

theorem auxiliary_isDone_computes (hf : s.pc ≠ .fault) (hs : (Ty.enc (TArg TX) arg).size ≤ S) :
    Computes PP assemblyIndices.isDone (Ty.enc (TArg TX) arg) (Enc.bool (decide (s.pc = .done)))
      (auxiliaryValue S) (auxiliaryCost S) (auxiliaryDepth S) := by
  obtain ⟨ht,hdp,hm⟩ := Trans.Bounds.isDone_bounds CX ctx s
  have h := auxiliary_computes hD hd A density (auxiliary_isDone_valid hD hd A density arg)
    (S := S) (by unfold auxiliaryValue; omega) (by unfold auxiliaryValue; omega)
    (by unfold auxiliaryCost; omega) (by unfold auxiliaryDepth; omega)
  rw [Trans.Bounds.isDone_den CX q r B m X s hf] at h
  exact h

theorem auxiliary_isInvoke_computes (hs : (Ty.enc (TArg TX) arg).size ≤ S) :
    Computes PP assemblyIndices.isInvoke (Ty.enc (TArg TX) arg) (Enc.bool (decide (s.pc = .invoke)))
      (auxiliaryValue S) (auxiliaryCost S) (auxiliaryDepth S) := by
  obtain ⟨ht,hdp,hm⟩ := Trans.Bounds.isInvoke_bounds CX ctx s
  have h := auxiliary_computes hD hd A density (auxiliary_isInvoke_valid hD hd A density arg)
    (S := S) (by unfold auxiliaryValue; omega) (by unfold auxiliaryValue; omega)
    (by unfold auxiliaryCost; omega) (by unfold auxiliaryDepth; omega)
  rw [Trans.Bounds.isInvoke_den CX q r B m X s] at h
  exact h

theorem auxiliary_query_computes (hs : (Ty.enc (TArg TX) arg).size ≤ S) :
    Computes PP assemblyIndices.query (Ty.enc (TArg TX) arg) (Assembly.bitsVal s.query)
      (auxiliaryValue S) (auxiliaryCost S) (auxiliaryDepth S) := by
  obtain ⟨ht,hdp,hm⟩ := Trans.Bounds.queryOf_bounds CX ctx s
  have h := auxiliary_computes hD hd A density (auxiliary_query_valid hD hd A density arg)
    (S := S) (by unfold auxiliaryValue; omega) (by unfold auxiliaryValue; omega)
    (by unfold auxiliaryCost; omega) (by unfold auxiliaryDepth; omega)
  rw [Trans.Bounds.queryOf_den CX q r B m X s] at h
  exact h

/-- Arbitrary output ratio list, with no iid or r+1-length specialization. -/
theorem auxiliary_output_computes (hs : (Ty.enc (TArg TX) arg).size ≤ S) :
    Computes PP assemblyIndices.output (Ty.enc (TArg TX) arg) (Assembly.bitsVal (Assembly.ratioWord s.output))
      (auxiliaryValue S) (auxiliaryCost S) (auxiliaryDepth S) := by
  have hc : (Ty.enc TCfg (encCfg s)).size ≤ S := by
    rw [Trans.Bounds.shape2] at hs
    omega
  obtain ⟨ht,hdp,hm⟩ := Trans.Bounds.outputF_bounds Install.oX ctx s
  have hp3 := Nat.pow_le_pow_left (show (Ty.enc TCfg (encCfg s)).size+1 ≤ S+1 by omega) 3
  have hp2 := Nat.pow_le_pow_left (show (Ty.enc TCfg (encCfg s)).size+1 ≤ S+1 by omega) 2
  have h := auxiliary_computes hD hd A density (auxiliary_output_valid hD hd A density arg)
    (S := S) (by unfold auxiliaryValue; omega) (by unfold auxiliaryValue; omega)
    (by unfold auxiliaryCost; omega) (by unfold auxiliaryDepth; omega)
  rw [Trans.Bounds.outputF_den] at h
  exact h

/-- False-mode invocation transport uses the actual unchanged answer/resume slots. -/
theorem auxiliary_resume_computes (ext : External) (e : Edge) (hpc : s.pc = .invoke)
    (he : WholeWrapperCandidate.step q r B m false ext s = some e)
    (hs : (Ty.enc (TArg TX) arg).size ≤ S) (hs' : (Ty.enc (TArg TX) (ctx,encCfg e.next)).size ≤ S) :
    Computes PP assemblyIndices.resume
      (Val.cons (Enc.bool (ext.sat s.query).value) (Ty.enc (TArg TX) arg))
      (Ty.enc (TArg TX) (ctx,encCfg e.next))
      (auxiliaryValue S) (auxiliaryCost S) (auxiliaryDepth S) := by
  have hn := ControllerInstalled.invoke_next q r B m ext s hpc
  rw [he,Option.map_some,Option.some.injEq] at hn
  have hden : (Trans.Bounds.resumeTopF Install.oX CX).den ((ext.sat s.query).value,arg) =
      (ctx,encCfg e.next) := by
    rw [Trans.Bounds.resumeTopF_den, ← hn]
  obtain ⟨ht,hdp,hm⟩ := Trans.Bounds.resumeTop_bounds CX ctx s Install.oX (ext.sat s.query).value
  rw [hden] at hm
  have hb := Enc.bool_size (ext.sat s.query).value
  have hsz : (Ty.enc (.prod (TArg TX) .bool) (arg,(ext.sat s.query).value)).size =
      (Ty.enc (TArg TX) arg).size + (Enc.bool (ext.sat s.query).value).size + 1 := by
    rw [Trans.Bounds.shape2]; rfl
  rw [hsz] at hm
  have h := auxiliary_computes hD hd A density
    (auxiliary_resume_valid hD hd A density ((ext.sat s.query).value,arg))
    (S := S) (by unfold auxiliaryValue; omega)
    (by change 1+(Enc.bool (ext.sat s.query).value).size+(Ty.enc (TArg TX) arg).size ≤ _
        unfold auxiliaryValue; omega)
    (by unfold auxiliaryCost; omega) (by unfold auxiliaryDepth; omega)
  rw [hden] at h
  exact h

end QecReliability.LatentMachine.Runtime
end
