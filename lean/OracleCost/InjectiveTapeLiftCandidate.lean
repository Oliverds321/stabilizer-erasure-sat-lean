import OracleCost.TraceDisplacementCandidate
import Mathlib.Data.List.OfFn

/-! Actual injection of a fixed smaller tape arena
into a fixed larger arena. The inverse selector is a COMPUTABLE finite list
lookup depending only on the fixed injection and physical tape index. No head
position, numeric tape operand, width, or visited set is readable by the table.
Outside-image rows write their currently read head and move stay. Every source
edge becomes exactly ONE physical edge, with unchanged labels and answers. -/
set_option autoImplicit false
namespace QecReliability.OracleCost.MultiTape.InjectiveTapeLift
open Turing Displacement
variable {k l : Nat} {Λ : Type} [Fintype Λ]

/-- Logical tape index -> actual tape index; a machine constant. -/
abbrev Embedding (k l : Nat) := Fin (k+1) ↪ Fin (l+1)

/-- Explicit finite inverse table, no classical/noncomputable choice. -/
def inverse (e : Embedding k l) (j : Fin (l+1)) : Option (Fin (k+1)) :=
  (List.ofFn (fun i : Fin (k+1) => i)).find? (fun i => decide (e i=j))

@[simp] theorem inverse_image (e : Embedding k l) (i : Fin (k+1)) :
    inverse e (e i)=some i := by
  apply List.find?_ofFn_eq_some.mpr
  refine ⟨by simp,⟨i,rfl,?_⟩⟩
  intro j hj he
  have hji : j=i := e.injective (by simpa using he)
  subst j
  exact (lt_irrefl i) hj

theorem inverse_spec (e : Embedding k l) (j : Fin (l+1)) (i : Fin (k+1))
    (h : inverse e j=some i) : e i=j := by
  have hs := (List.find?_ofFn_eq_some.mp h).1
  simpa using hs

theorem inverse_outside (e : Embedding k l) (j : Fin (l+1))
    (h : ∀ i, e i≠j) : inverse e j=none := by
  apply List.find?_eq_none.mpr
  intro i hi
  simpa using h i

def mapAction (e : Embedding k l) (heads : Fin (l+1) → Option Bool) :
    Action k (Option Bool) Λ → Action l (Option Bool) Λ
  | .halt answer => .halt answer
  | .advance next write moves => .advance next
      (fun j => match inverse e j with | some i => write i | none => heads j)
      (fun j => match inverse e j with | some i => moves i | none => .stay)

/-- Literal finite table lift; no additional submachine, jump, or clock edge. -/
def machine (M : Machine k (Option Bool) Λ) (e : Embedding k l) :
    Machine l (Option Bool) Λ where
  start := M.start
  inputSymbol := M.inputSymbol
  input_injective := M.input_injective
  input_not_blank := M.input_not_blank
  transition q heads := mapAction e heads (M.transition q (fun i => heads (e i)))

/-- Arbitrary outside tapes are retained, not assumed blank or freshly loaded. -/
def config (e : Embedding k l) (outside : Fin (l+1) → Tape (Option Bool))
    (s : Config k (Option Bool) Λ) : Config l (Option Bool) Λ :=
  ⟨s.label,fun j => match inverse e j with | some i => s.tapes i | none => outside j⟩

def offsets (e : Embedding k l) (d : Fin (k+1) → Int) : Fin (l+1) → Int :=
  fun j => match inverse e j with | some i => d i | none => 0

@[simp] theorem config_image (e : Embedding k l) (outside : Fin (l+1) → Tape (Option Bool))
    (s : Config k (Option Bool) Λ) (i : Fin (k+1)) : (config e outside s).tapes (e i)=s.tapes i := by
  simp [config]

theorem config_outside (e : Embedding k l) (outside : Fin (l+1) → Tape (Option Bool))
    (s : Config k (Option Bool) Λ) (j : Fin (l+1)) (h : ∀ i, e i≠j) :
    (config e outside s).tapes j=outside j := by simp [config,inverse_outside e j h]

@[simp] theorem offsets_image (e : Embedding k l) (d : Fin (k+1) → Int) (i : Fin (k+1)) :
    offsets e d (e i)=d i := by simp [offsets]

theorem offsets_outside (e : Embedding k l) (d : Fin (k+1) → Int)
    (j : Fin (l+1)) (h : ∀ i, e i≠j) : offsets e d j=0 := by simp [offsets,inverse_outside e j h]

@[simp] theorem offsets_zero (e : Embedding k l) : offsets e (fun _ => 0)=(fun _ => 0) := by
  funext j; cases h : inverse e j <;> simp [offsets,h]

theorem offsets_add (e : Embedding k l) (d f : Fin (k+1) → Int) :
    (fun j => offsets e d j+offsets e f j)=offsets e (fun i => d i+f i) := by
  funext j; cases h : inverse e j <;> simp [offsets,h]

variable (M : Machine k (Option Bool) Λ) (e : Embedding k l)
    (outside : Fin (l+1) → Tape (Option Bool))

theorem action (s : Config k (Option Bool) Λ) :
    (machine M e).action (config e outside s)=
      mapAction e (fun j => (config e outside s).tapes j |>.head) (M.action s) := by
  have hh : (fun i => (config e outside s).tapes (e i) |>.head)=(fun i => (s.tapes i).head) := by
    funext i; simp
  simp only [Machine.action,machine,config,hh,inverse_image]

theorem step (s : Config k (Option Bool) Λ) :
    (machine M e).step (config e outside s)=(M.step s).map (config e outside) := by
  cases ha : M.action s with
  | halt answer => simp [Machine.step,action,mapAction,ha]
  | advance next write moves =>
    simp only [Machine.step,action,ha,mapAction,Option.map_some,Option.some.injEq]
    congr 1; funext j
    cases hj : inverse e j <;> simp [config,hj,Move.apply,Tape.write_self]

theorem delta (s : Config k (Option Bool) Λ) :
    Displacement.delta (machine M e) (config e outside s)=offsets e (Displacement.delta M s) := by
  funext j
  cases ha : M.action s <;> cases hj : inverse e j <;>
    simp [Displacement.delta,action,mapAction,ha,offsets,hj,Move.delta]

/-- Exact source trace transport, unchanged edge count. Displacements on active
physical tapes equal source displacements; every other tape has zero drift. -/
theorem run {s t : Config k (Option Bool) Λ} {n : Nat} {d : Fin (k+1) → Int}
    (h : Run M s n d t) :
    Run (machine M e) (config e outside s) n (offsets e d) (config e outside t) := by
  induction h with
  | nil => simpa using (Run.nil (M:=machine M e) (config e outside _))
  | @cons s mid t n d he tail ih =>
    have hs : (machine M e).step (config e outside s)=some (config e outside mid) := by
      rw [step M e outside s,he]; rfl
    have h' := Run.cons hs ih
    rw [delta M e outside s,offsets_add] at h'
    exact h'

/-- Explicit row-level outside framing, independent of source tape contents. -/
theorem outside_row (q : Λ) (heads : Fin (l+1) → Option Bool) (j : Fin (l+1))
    (houtside : ∀ i, e i≠j) (next : Λ) (write : Fin (l+1) → Option Bool)
    (moves : Fin (l+1) → Move)
    (h : (machine M e).transition q heads=.advance next write moves) :
    write j=heads j ∧ moves j=.stay := by
  cases ha : M.transition q (fun i => heads (e i)) with
  | halt answer => simp [machine,mapAction,ha] at h
  | advance label sourceWrite sourceMoves =>
    simp only [machine,mapAction,ha,Action.advance.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    simp [inverse_outside e j houtside]

/-- Actual observed run with the exact framed endpoint and absolute positions.
No equality of blank tape contents is used as a head-coordinate reset. -/
theorem observed {s t : Config k (Option Bool) Λ} {n : Nat} {d : Fin (k+1) → Int}
    (h : Run M s n d t) (initial : Observed l (Option Bool) Λ)
    (hi : initial.core=config e outside s) :
    ∃ final, Trace (machine M e) initial n final ∧ final.core=config e outside t ∧
      (∀ i, final.core.tapes (e i)=t.tapes i) ∧
      (∀ i, final.position (e i)=initial.position (e i)+d i) ∧
      (∀ j, (∀ i, e i≠j) → final.core.tapes j=outside j ∧ final.position j=initial.position j) := by
  obtain ⟨last,ht,hf,hp⟩ := (run M e outside h).observe initial hi
  refine ⟨last,ht,hf,?_,?_,?_⟩
  · intro i; rw [hf]; exact config_image e outside t i
  · intro i; simpa using hp (e i)
  · intro j hj
    constructor
    · rw [hf]; exact config_outside e outside t j hj
    · simpa [offsets_outside e d j hj] using hp j

/-- Naming aliases for larger-arena callers. -/
abbrev lift (A : Machine k (Option Bool) Λ) (injection : Embedding k l) := machine A injection
abbrev embed (injection : Embedding k l) (frame : Fin (l+1) → Tape (Option Bool))
    (s : Config k (Option Bool) Λ) := config injection frame s

theorem zero_run {s t : Config k (Option Bool) Λ} {n : Nat}
    (h : Run M s n (fun _ => 0) t) :
    Run (machine M e) (config e outside s) n (fun _ => 0) (config e outside t) := by
  simpa using run M e outside h

theorem answer_embed (s : Config k (Option Bool) Λ) :
    (machine M e).answer (config e outside s)=M.answer s := by
  cases ha : M.action s <;> simp [Machine.answer,action,mapAction,ha]

end QecReliability.OracleCost.MultiTape.InjectiveTapeLift
