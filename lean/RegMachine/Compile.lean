import Mathlib.Tactic.Ring
import RegMachine.Lang
import RegMachine.Abstract
import OracleCost.LabelRoutedMachineNetwork

/-!
# The compiler: CFG programs to `LabelRoutedNetwork` machines

A `Library` assigns to every primitive a gadget machine on the common tape arena.
`compile lib prog` is the `LabelRoutedNetwork.machine` whose blocks are the gadgets
of the program nodes and whose routing table is the program's `next`.

`Realizes lib σ enc Inv W α`: every gadget, started at its start label on the
normal form `⟨enc s, heads at 0⟩` of a state `s` (with `Inv s`, its precondition and
`Inv` of the result), runs within window `W` in at most `α · cost` steps to the
normal form of the new state and halts with the semantic answer.

Main results (proved once, for every primitive set):
* `compile_exec`: an abstract halting execution with cost `C` and `N` primitive
  steps is simulated by a windowed abstract run of `compile lib prog` of length
  `< α·C + N`, ending in the normal form of the final state with the same answer;
* `compile_completed`: the same as an actual `MultiTape.Completed` run from
  `Machine.initial`, with `time ≤ α·C + N` and every tape's visited set inside `W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.RegMachine
open QecReliability.OracleCost.MultiTape QecReliability.OracleCost.MultiTape.LabelRoutedNetwork Turing

/-! ## Abstract view of label-routed networks -/

section Net
variable {k : ℕ} {Γ : Type} [Fintype Γ] [Inhabited Γ]
variable {I : Type} [Fintype I] {Labels : I → Type} [∀ i, Fintype (Labels i)]
variable (blocks : ∀ i, Machine k Γ (Labels i)) (first : I)
  (next : (i : I) → Labels i → Bool → Option I)

/-- Block-local abstract configuration seen inside the network. -/
def aembed (i : I) (a : ACfg k Γ (Labels i)) : ACfg k Γ (Sigma Labels) :=
  ⟨⟨i, a.label⟩, a.C, a.P⟩

theorem aanswer_eq_some {Λ : Type} [Fintype Λ] {M : Machine k Γ Λ} {a : ACfg k Γ Λ} {b : Bool}
    (h : aanswer M a = some b) : M.transition a.label a.heads = .halt b := by
  unfold aanswer at h
  cases htr : M.transition a.label a.heads with
  | halt c => rw [htr] at h; cases h; rfl
  | advance q w mv => rw [htr] at h; cases h

theorem net_astep {i : I} {a a' : ACfg k Γ (Labels i)} (h : astep (blocks i) a = some a') :
    astep (machine Labels blocks first next) (aembed i a) = some (aembed i a') := by
  obtain ⟨q, w, mv, htr, rfl⟩ := astep_eq_some h
  have ht : (machine Labels blocks first next).transition (aembed i a).label (aembed i a).heads =
      .advance ⟨i, q⟩ w mv := by
    rw [show (aembed i a).heads = a.heads from rfl]
    dsimp only [machine, aembed]
    rw [htr]
  rw [astep_of_advance ht]
  rfl

theorem net_handoff {i j : I} {a : ACfg k Γ (Labels i)} {b : Bool}
    (h : aanswer (blocks i) a = some b) (route : next i a.label b = some j) :
    astep (machine Labels blocks first next) (aembed i a) =
      some ⟨⟨j, (blocks j).start⟩, a.C, a.P⟩ := by
  have htr := aanswer_eq_some h
  have ht : (machine Labels blocks first next).transition (aembed i a).label (aembed i a).heads =
      .advance ⟨j, (blocks j).start⟩ (aembed i a).heads (fun _ => .stay) := by
    rw [show (aembed i a).heads = a.heads from rfl]
    dsimp only [machine, aembed]
    rw [htr]
    simp only [route]
  rw [astep_of_advance ht]
  congr 1
  refine ACfg.ext rfl ?_ ?_
  · funext x; exact Function.update_eq_self _ _
  · funext x; show a.P x + Move.stay.delta = a.P x; simp [Move.delta]

theorem net_answer {i : I} {a : ACfg k Γ (Labels i)} {b : Bool}
    (h : aanswer (blocks i) a = some b) (route : next i a.label b = none) :
    aanswer (machine Labels blocks first next) (aembed i a) = some b := by
  have htr := aanswer_eq_some h
  apply aanswer_of_halt
  rw [show (aembed i a).heads = a.heads from rfl]
  dsimp only [machine, aembed]
  rw [htr]
  simp only [route]

theorem net_run {W : Fin (k + 1) → Set ℤ} {i : I} {a a' : ACfg k Γ (Labels i)} {n : ℕ}
    (h : ARun (blocks i) W a n a') :
    ARun (machine Labels blocks first next) W (aembed i a) n (aembed i a') := by
  induction h with
  | nil hw => exact .nil hw
  | cons hs hw _ ih => exact .cons (net_astep blocks first next hs) hw ih

end Net

/-! ## Libraries and the compiler -/

/-- A gadget machine for every primitive, on a common tape arena. -/
structure Library (k : ℕ) (Γ : Type) [Fintype Γ] [Inhabited Γ] (P : Type) where
  L : P → Type
  fin : ∀ p, Fintype (L p)
  gadget : (p : P) → Machine k Γ (L p)

attribute [instance] Library.fin

section Compile
variable {k : ℕ} {Γ : Type} [Fintype Γ] [Inhabited Γ] {P S : Type} {n : ℕ}

/-- Control labels of the compiled machine: (program node, gadget label). -/
abbrev CLabel (lib : Library k Γ P) (prog : Prog P n) := Σ i : Fin n, lib.L (prog.prim i)

/-- The compiled machine: a label-routed network of the nodes' gadgets. -/
def compile (lib : Library k Γ P) (prog : Prog P n) : Machine k Γ (CLabel lib prog) :=
  machine (fun i : Fin n => lib.L (prog.prim i)) (fun i => lib.gadget (prog.prim i)) prog.entry
    (fun i _ b => prog.next i b)

/-- Normal form: given contents, every head on cell `0`. -/
def nfA {Λ : Type} (q : Λ) (C : Fin (k + 1) → ℤ → Γ) : ACfg k Γ Λ := ⟨q, C, fun _ => 0⟩

/-- The gadget library implements the primitive semantics `σ` w.r.t. the encoding
`enc`, the invariant `Inv`, the window `W`, with time factor `α`. -/
def Realizes (lib : Library k Γ P) (σ : PrimSem P S) (enc : S → Fin (k + 1) → ℤ → Γ)
    (Inv : S → Prop) (W : Fin (k + 1) → Set ℤ) (α : ℕ) : Prop :=
  ∀ p s, Inv s → σ.pre p s → Inv (σ.eval p s).1 →
    ∃ (m : ℕ) (q : lib.L p), m ≤ α * σ.cost p s ∧
      ARun (lib.gadget p) W (nfA (lib.gadget p).start (enc s)) m (nfA q (enc (σ.eval p s).1)) ∧
      aanswer (lib.gadget p) (nfA q (enc (σ.eval p s).1)) = some (σ.eval p s).2

variable {lib : Library k Γ P} {σ : PrimSem P S} {enc : S → Fin (k + 1) → ℤ → Γ}
  {Inv : S → Prop} {W : Fin (k + 1) → Set ℤ} {α : ℕ} {prog : Prog P n}

/-- **Compiler correctness (abstract level).** -/
theorem compile_exec (hreal : Realizes lib σ enc Inv W α) {i : Fin n} {s t : S} {N C : ℕ}
    {b : Bool} (h : Exec σ prog Inv i s N C t b) :
    ∃ (m : ℕ) (c : CLabel lib prog), m + 1 ≤ α * C + N ∧
      ARun (compile lib prog) W (nfA ⟨i, (lib.gadget (prog.prim i)).start⟩ (enc s)) m
        (nfA c (enc t)) ∧
      aanswer (compile lib prog) (nfA c (enc t)) = some b := by
  induction h with
  | @halt i s t b hs hp he ht hn =>
    obtain ⟨m, q, hm, hrun, hans⟩ := hreal (prog.prim i) s hs hp (by rw [he]; exact ht)
    rw [he] at hrun hans
    refine ⟨m, ⟨i, q⟩, by omega, ?_, ?_⟩
    · exact net_run (fun i => lib.gadget (prog.prim i)) prog.entry (fun i _ b => prog.next i b)
        (i := i) hrun
    · exact net_answer (fun i => lib.gadget (prog.prim i)) prog.entry (fun i _ b => prog.next i b)
        (i := i) (a := nfA q (enc t)) hans hn
  | @step i j s s' t b b' N C hs hp he hn _ ih =>
    obtain ⟨m1, q, hm1, hrun1, hans1⟩ := hreal (prog.prim i) s hs hp
      (by rw [he]; exact (by assumption : Exec σ prog Inv j s' N C t b').inv_start)
    rw [he] at hrun1 hans1
    obtain ⟨m2, c, hm2, hrun2, hans2⟩ := ih
    have hl := net_run (fun i => lib.gadget (prog.prim i)) prog.entry (fun i _ b => prog.next i b)
      (i := i) hrun1
    have hh := net_handoff (fun i => lib.gadget (prog.prim i)) prog.entry
      (fun i _ b => prog.next i b) (i := i) (a := nfA q (enc s')) hans1 hn
    refine ⟨m1 + (m2 + 1), c, ?_, hl.trans (ARun.step hh hrun2 hl.end_mem), hans2⟩
    have : α * (σ.cost (prog.prim i) s + C) = α * σ.cost (prog.prim i) s + α * C := by ring
    omega

/-- **Compiler correctness (concrete machine).** From `Machine.initial bits`, whose
tapes are the encoding of `s₀`, the compiled machine has a completed run with the
program's answer, `time ≤ α·C + N`, every visited cell inside `W`, and final tapes
equal to the encoding of the final state with every head back on cell `0`. -/
theorem compile_completed (hreal : Realizes lib σ enc Inv W α) {s₀ t : S} {N C : ℕ} {b : Bool}
    (h : Exec σ prog Inv prog.entry s₀ N C t b) (bits : List Bool)
    (hinit : ∀ i z, (((compile lib prog).initial bits).tapes i).nth z = enc s₀ i z)
    (hvis : ∀ i, ↑((initialObserved (compile lib prog) bits).visited i) ⊆ W i) :
    ∃ run : Completed (compile lib prog) bits, run.output = b ∧ run.time ≤ α * C + N ∧
      (∀ i, ↑(run.final.visited i) ⊆ W i) ∧
      (∀ i z, (run.final.core.tapes i).nth z = enc t i z) ∧
      run.final.position = fun _ => 0 := by
  obtain ⟨m, c, hm, hrun, hans⟩ := compile_exec hreal h
  have ho : ORep (initialObserved (compile lib prog) bits)
      (nfA ⟨prog.entry, (lib.gadget (prog.prim prog.entry)).start⟩ (enc s₀)) := by
    refine ⟨⟨rfl, ?_⟩, rfl⟩
    intro i z
    simpa only [initialObserved, nfA, zero_add] using hinit i z
  obtain ⟨o, htr, hrep, hv⟩ := hrun.observe ho hvis
  have hhalt : (compile lib prog).answer o.core = some b := by
    rw [hrep.1.answer]; exact hans
  refine ⟨⟨m, o, b, htr, hhalt⟩, rfl, ?_, hv, ?_, hrep.2⟩
  · show m + 1 ≤ _; exact hm
  · intro i z
    have := hrep.1.2 i z
    rw [this]
    simp [nfA]

end Compile

end QecReliability.RegMachine
