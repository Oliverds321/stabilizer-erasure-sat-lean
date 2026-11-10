import Trans.Query.Plain
import OracleCost.QuantumService

/-!
# Trans.Query.Types: plain encodings of the dependent objects

`Fin` indices become their values; the bounds are recorded in the correctness statements.

* `encLit`, `encForm` (`= QueryCodec.plain`): literals and formulas;
* `encGate`, `encCirc`, `encProg`: gates, circuits (gate list, output wire of gate `k` is
  `n + k`), programs (gates, output wires);
* `encBlock`: `(aux, formula)`;
* `encCoord`, `encRows`: Pauli coordinates `inl i ↦ (false, i)`, `inr i ↦ (true, i)`;
* `encReq`: a SAT request as `(varCount, plain formula)`;
* `encIndex`: a coefficient index `(side, j)` as `(side, j.val)`.

Each encoding is injective (`*_injective`), so the plain construction determines the Lean one.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Query
open QecReliability.SharedCircuit QecReliability.PrefixCNF QecReliability.OracleCost

def encLit {v : ℕ} (l : Literal v) : Plain.Lit := (l.1.val, l.2)

def encForm {v : ℕ} (F : Formula v) : Plain.Form := QueryCodec.plain F

theorem encForm_eq {v : ℕ} (F : Formula v) :
    encForm F = F.map (fun c => c.map (fun l => (l.1.val, l.2))) := rfl

@[simp] theorem encForm_append {v : ℕ} (F G : Formula v) :
    encForm (F ++ G) = encForm F ++ encForm G := by simp [encForm_eq]

@[simp] theorem encForm_nil {v : ℕ} : encForm ([] : Formula v) = [] := rfl

@[simp] theorem encForm_cons {v : ℕ} (c : List (Literal v)) (F : Formula v) :
    encForm (c :: F) = c.map (fun l => (l.1.val, l.2)) :: encForm F := rfl

@[simp] theorem encForm_length {v : ℕ} (F : Formula v) : (encForm F).length = F.length := by
  simp [encForm_eq]

theorem encLit_injective {v : ℕ} : Function.Injective (@encLit v) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [encLit, Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  rw [Fin.ext h1]

theorem encForm_injective {v : ℕ} : Function.Injective (@encForm v) := by
  intro F G h
  rw [encForm_eq, encForm_eq] at h
  have hc : Function.Injective (fun c : List (Literal v) => c.map (fun l => (l.1.val, l.2))) :=
    List.map_injective_iff.mpr encLit_injective
  exact (List.map_injective_iff.mpr hc) h

/-! ## Gates, circuits, programs -/

def encGate {v : ℕ} : Gate v → Plain.GateP
  | .andGate x y => (false, false, x.val, y.val)
  | .xorGate x y => (false, true, x.val, y.val)
  | .notGate x => (true, false, x.val, 0)
  | .constGate b => Plain.constGate b

theorem encGate_injective {v : ℕ} : Function.Injective (@encGate v) := by
  intro g h e
  cases g <;> cases h <;> simp_all [encGate, Plain.constGate, Fin.ext_iff]
  rename_i a b
  cases a <;> cases b <;> simp_all

def encCirc {n : ℕ} : {g : ℕ} → Circuit n g → List Plain.GateP
  | _, .nil => []
  | _, .snoc C gate => encCirc C ++ [encGate gate]

@[simp] theorem encCirc_nil {n : ℕ} : encCirc (Circuit.nil : Circuit n 0) = [] := rfl
@[simp] theorem encCirc_snoc {n g : ℕ} (C : Circuit n g) (gate : Gate (n + g)) :
    encCirc (C.snoc gate) = encCirc C ++ [encGate gate] := rfl

@[simp] theorem encCirc_length {n g : ℕ} (C : Circuit n g) : (encCirc C).length = g := by
  induction C with
  | nil => rfl
  | snoc C gate ih => simp [ih]

theorem encCirc_injective {n g : ℕ} : Function.Injective (@encCirc n g) := by
  intro C D h
  induction C with
  | nil => cases D; rfl
  | @snoc g C gate ih =>
    cases D with
    | snoc D gate' =>
      simp only [encCirc_snoc] at h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
      have := ih h1
      simp only [List.cons.injEq, and_true] at h2
      rw [this, encGate_injective h2]

def encProg {n k : ℕ} (P : Program n k) : Plain.ProgP :=
  (encCirc P.circuit, List.ofFn (fun i => (P.output i).val))

theorem encProg_injective {n k : ℕ} : Function.Injective (@encProg n k) := by
  rintro ⟨g, C, o⟩ ⟨g', C', o'⟩ h
  simp only [encProg, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hg : g = g' := by simpa using congrArg List.length h1
  subst hg
  have hC := encCirc_injective h1
  subst hC
  have ho : o = o' := by
    funext i
    exact Fin.ext (congrFun (List.ofFn_injective h2) i)
  subst ho
  rfl

/-! ## Blocks -/

def encBlock {n : ℕ} (B : Block n) : Plain.BlockP := (B.aux, encForm B.formula)

theorem encBlock_injective {n : ℕ} : Function.Injective (@encBlock n) := by
  rintro ⟨a, F⟩ ⟨a', F'⟩ h
  simp only [encBlock, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  rw [encForm_injective h2]

/-! ## Pauli coordinates and rows -/

def encCoord {n : ℕ} : PauliCoord n → Plain.Coord
  | .inl i => (false, i.val)
  | .inr i => (true, i.val)

theorem encCoord_injective {n : ℕ} : Function.Injective (@encCoord n) := by
  intro a b h
  cases a <;> cases b <;> simp_all [encCoord, Fin.ext_iff]

def encRows {n : ℕ} (rows : List (List (PauliCoord n))) : List (List Plain.Coord) :=
  rows.map (fun row => row.map encCoord)

theorem encRows_injective {n : ℕ} : Function.Injective (@encRows n) :=
  List.map_injective_iff.mpr (List.map_injective_iff.mpr encCoord_injective)

/-! ## Requests and coefficient indices -/

def encReq (req : SATRequest) : ℕ × Plain.Form := (req.varCount, encForm req.formula)

theorem encReq_injective : Function.Injective encReq := by
  rintro ⟨v, F, hF⟩ ⟨v', F', hF'⟩ h
  simp only [encReq, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have := encForm_injective h2
  subst this
  rfl

def encIndex {r : ℕ} (i : Binary.CoefficientIndex r) : Bool × ℕ := (i.1, i.2.val)

theorem encIndex_injective {r : ℕ} : Function.Injective (@encIndex r) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [encIndex, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  rw [Fin.ext h2]

end QecReliability.Trans.Query
