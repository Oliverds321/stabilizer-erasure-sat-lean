import TensorMachineCallbackRuns
import TensorMachineAgreement
import Trans.Bounds.Loop

/-! Encoded-size bounds for the installed tensor machine's unchanged observer,
resume, and output callbacks. Natural-number values are never charged as
unit-size operands. Resume is bounded for either possible SAT answer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace QecReliability.TensorMachine.Auxiliary
open FL Trans.Control OracleCost.WholeWrapperCandidate

def space (S : ℕ) : ℕ := 40*S+260
def time (S : ℕ) : ℕ := 1100*(S+1)^3+4000
def depth (S : ℕ) : ℕ := 10*(S+1)^2+21

variable {TX : Ty} (x : Ix TX) (c : (TCtx TX).den) (s : Config) (S : ℕ)
  (hs : (Ty.enc (TArg TX) (c,encCfg s)).size≤S)

include hs in
theorem isInvoke_bounds : CallBounds (isInvokeF x) (c,encCfg s) (space S) (time S) (depth S) := by
  obtain ⟨ht,hd,hm⟩ := Trans.Bounds.isInvoke_bounds x c s
  constructor
  · unfold space; omega
  · unfold space; omega
  · unfold time; omega
  · unfold depth; omega

include hs in
theorem isDone_bounds : CallBounds (isDoneF x) (c,encCfg s) (space S) (time S) (depth S) := by
  obtain ⟨ht,hd,hm⟩ := Trans.Bounds.isDone_bounds x c s
  constructor
  · unfold space; omega
  · unfold space; omega
  · unfold time; omega
  · unfold depth; omega

include hs in
theorem query_bounds : CallBounds (queryOfF x) (c,encCfg s) (space S) (time S) (depth S) := by
  obtain ⟨ht,hd,hm⟩ := Trans.Bounds.queryOf_bounds x c s
  constructor
  · unfold space; omega
  · unfold space; omega
  · unfold time; omega
  · unfold depth; omega

theorem resume_config_size (answer : Bool) :
    (Ty.enc TCfg (encCfg {s with pc := .resume,reply := answer})).size≤
      (Ty.enc TCfg (encCfg s)).size+21 := by
  have hn : (Ty.enc .nat (pcCode PC.resume)).size≤13 :=
    Trans.Bounds.enc_lit 4 3 (by decide)
  have ha := Enc.bool_size answer
  have hb := Enc.bool_size s.reply
  simp only [encCfg,Ty.sz_prod,Ty.enc_bool] at *
  omega

include hs in
theorem resume_bounds (o : Trans.Bounds.OIx) (answer : Bool) :
    CallBounds (Trans.Bounds.resumeTopF o x) (answer,(c,encCfg s))
      (space S) (time S) (depth S) := by
  obtain ⟨ht,hd,hm⟩ := Trans.Bounds.resumeTop_bounds x c s o answer
  have hden : (Trans.Bounds.resumeTopF o x).den (answer,(c,encCfg s))=
      (c,encCfg {s with pc := .resume,reply := answer}) := rfl
  rw [hden] at hm
  have hr := resume_config_size s answer
  have hb := Enc.bool_size answer
  have hctx : (Ty.enc (TArg TX) (c,encCfg {s with pc := .resume,reply := answer})).size≤S+21 := by
    rw [Trans.Bounds.shape2] at hs ⊢
    omega
  have hpair : (Ty.enc (.prod (TArg TX) .bool) ((c,encCfg s),answer)).size≤S+4 := by
    rw [Trans.Bounds.shape2]
    change (Ty.enc (TArg TX) (c,encCfg s)).size+(Enc.bool answer).size+1≤S+4
    omega
  have harg : (Ty.enc (.prod .bool (TArg TX)) (answer,(c,encCfg s))).size≤S+4 := by
    rw [Trans.Bounds.shape2]
    change (Enc.bool answer).size+(Ty.enc (TArg TX) (c,encCfg s)).size+1≤S+4
    omega
  constructor
  · unfold space; omega
  · unfold space; omega
  · unfold time; omega
  · unfold depth; omega

include hs in
theorem output_bounds (o : Trans.Bounds.OIx) :
    CallBounds (Trans.Bounds.outputF o TX) (c,encCfg s) (space S) (time S) (depth S) := by
  have hcfg : (Ty.enc TCfg (encCfg s)).size≤S := by
    rw [Trans.Bounds.shape2] at hs
    omega
  obtain ⟨ht,hd,hm⟩ := Trans.Bounds.outputF_bounds o c s
  have hp3 := Nat.pow_le_pow_left (show (Ty.enc TCfg (encCfg s)).size+1≤S+1 by omega) 3
  have hp2 := Nat.pow_le_pow_left (show (Ty.enc TCfg (encCfg s)).size+1≤S+1 by omega) 2
  constructor
  · unfold space; omega
  · unfold space; omega
  · unfold time; omega
  · unfold depth; omega

end QecReliability.TensorMachine.Auxiliary

noncomputable section
namespace QecReliability.TensorMachine.Runtime
open FL Trans.Control
open SharedCircuit.FixedLocalEmitter.AllLength UniformAdapter FiniteLocalSelectorCandidate
open OracleCost.WholeWrapperCandidate
variable {D t : ℕ} (hD : D=16^384) (hd : D=256*t)
  (A : CertifiedParity (512*t) (64*t) t) (density : ℕ)
  (c : (TCtx ContextFL.TX).den) (s : Config) (S : ℕ)
  (hs : (Ty.enc (TArg ContextFL.TX) (c,encCfg s)).size≤S)

include hs in
theorem auxiliary_observers :
    CallBounds (isInvokeF (controller hD hd A density)) (c,encCfg s)
      (Auxiliary.space S) (Auxiliary.time S) (Auxiliary.depth S) ∧
    CallBounds (isDoneF (controller hD hd A density)) (c,encCfg s)
      (Auxiliary.space S) (Auxiliary.time S) (Auxiliary.depth S) ∧
    CallBounds (queryOfF (controller hD hd A density)) (c,encCfg s)
      (Auxiliary.space S) (Auxiliary.time S) (Auxiliary.depth S) :=
  ⟨Auxiliary.isInvoke_bounds _ c s S hs,Auxiliary.isDone_bounds _ c s S hs,
    Auxiliary.query_bounds _ c s S hs⟩

include hs in
theorem auxiliary_resume (answer : Bool) :
    CallBounds (Trans.Bounds.resumeTopF Install.oX (controller hD hd A density))
      (answer,(c,encCfg s)) (Auxiliary.space S) (Auxiliary.time S) (Auxiliary.depth S) :=
  Auxiliary.resume_bounds _ c s S hs Install.oX answer

include hs in
theorem auxiliary_output :
    CallBounds (Trans.Bounds.outputF Install.oX ContextFL.TX) (c,encCfg s)
      (Auxiliary.space S) (Auxiliary.time S) (Auxiliary.depth S) :=
  Auxiliary.output_bounds c s S hs Install.oX

end QecReliability.TensorMachine.Runtime
