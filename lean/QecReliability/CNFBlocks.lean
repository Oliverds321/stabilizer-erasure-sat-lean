import QecReliability.QuantumCircuitPieces

/-! Concrete CNF conjunction with shared primary inputs and disjoint gate outputs. -/

namespace QecReliability.SharedCircuit
open PrefixCNF

structure Block (n : ℕ) where
  aux : ℕ
  formula : Formula (n + aux)

namespace Block

def Accepts {n : ℕ} (B : Block n) (a : BitModels n) : Prop :=
  ∃ u : BitModels B.aux, PrefixCNF.eval B.formula (Fin.append a u) = true

def Deterministic {n : ℕ} (B : Block n) : Prop :=
  ∀ a (u v : BitModels B.aux),
    PrefixCNF.eval B.formula (Fin.append a u) = true →
    PrefixCNF.eval B.formula (Fin.append a v) = true → u = v

def leftWire (n k l : ℕ) : Fin (n + k) → Fin (n + (k + l)) :=
  Fin.addCases (Fin.castAdd (k + l)) (fun i => Fin.natAdd n (Fin.castAdd l i))

def rightWire (n k l : ℕ) : Fin (n + l) → Fin (n + (k + l)) :=
  Fin.addCases (Fin.castAdd (k + l)) (fun i => Fin.natAdd n (Fin.natAdd k i))

def and {n : ℕ} (B C : Block n) : Block n where
  aux := B.aux + C.aux
  formula := rename (leftWire n B.aux C.aux) B.formula ++
    rename (rightWire n B.aux C.aux) C.formula

theorem and_eval {n : ℕ} (B C : Block n) (a : BitModels n)
    (u : BitModels B.aux) (v : BitModels C.aux) :
    PrefixCNF.eval (B.and C).formula (Fin.append a (Fin.append u v)) =
      (PrefixCNF.eval B.formula (Fin.append a u) &&
       PrefixCNF.eval C.formula (Fin.append a v)) := by
  have hl : (fun i => Fin.append a (Fin.append u v) (leftWire n B.aux C.aux i)) =
      Fin.append a u := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [leftWire]
  have hr : (fun i => Fin.append a (Fin.append u v) (rightWire n B.aux C.aux i)) =
      Fin.append a v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [rightWire]
  calc
    _ = (PrefixCNF.eval (rename (leftWire n B.aux C.aux) B.formula)
          (Fin.append a (Fin.append u v)) &&
        PrefixCNF.eval (rename (rightWire n B.aux C.aux) C.formula)
          (Fin.append a (Fin.append u v))) := List.all_append
    _ = _ := by rw [eval_rename, eval_rename, hl, hr]

theorem and_accepts {n : ℕ} (B C : Block n) (a : BitModels n) :
    (B.and C).Accepts a ↔ B.Accepts a ∧ C.Accepts a := by
  constructor
  · rintro ⟨uv, huv⟩
    let u := fun i => uv (Fin.castAdd C.aux i)
    let v := fun i => uv (Fin.natAdd B.aux i)
    have he : Fin.append u v = uv := Fin.append_castAdd_natAdd
    rw [← he, and_eval, Bool.and_eq_true] at huv
    exact ⟨⟨u, huv.1⟩, ⟨v, huv.2⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨Fin.append u v, by rw [and_eval, hu, hv]; rfl⟩

theorem and_deterministic {n : ℕ} (B C : Block n)
    (hB : B.Deterministic) (hC : C.Deterministic) : (B.and C).Deterministic := by
  intro a u v hu hv
  have eu := Fin.append_castAdd_natAdd (f := u)
  have ev := Fin.append_castAdd_natAdd (f := v)
  rw [← eu, and_eval, Bool.and_eq_true] at hu
  rw [← ev, and_eval, Bool.and_eq_true] at hv
  have hl := hB a _ _ hu.1 hv.1
  have hr := hC a _ _ hu.2 hv.2
  rw [← eu, ← ev, hl, hr]

theorem and_width {n k : ℕ} (B C : Block n)
    (hB : Width k B.formula) (hC : Width k C.formula) : Width k (B.and C).formula := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact width_rename _ _ hB c hc
  · exact width_rename _ _ hC c hc

@[simp] theorem and_length {n : ℕ} (B C : Block n) :
    (B.and C).formula.length = B.formula.length + C.formula.length := by
  simp [and, rename]

def empty (n : ℕ) : Block n := ⟨0, []⟩

def merge {n : ℕ} : List (Block n) → Block n
  | [] => empty n
  | B :: Bs => B.and (merge Bs)

theorem merge_accepts {n : ℕ} (Bs : List (Block n)) (a : BitModels n) :
    (merge Bs).Accepts a ↔ ∀ B ∈ Bs, B.Accepts a := by
  induction Bs with
  | nil => simp [merge, Accepts, empty, PrefixCNF.eval]
  | cons B Bs ih => simp [merge, and_accepts, ih]

theorem merge_aux {n : ℕ} (Bs : List (Block n)) :
    (merge Bs).aux = (Bs.map Block.aux).sum := by
  induction Bs with
  | nil => rfl
  | cons B Bs ih => simp [merge, and, ih]

theorem merge_length {n : ℕ} (Bs : List (Block n)) :
    (merge Bs).formula.length = (Bs.map (fun B => B.formula.length)).sum := by
  induction Bs with
  | nil => rfl
  | cons B Bs ih => simp [merge, ih]

theorem merge_width {n k : ℕ} (Bs : List (Block n))
    (h : ∀ B ∈ Bs, Width k B.formula) : Width k (merge Bs).formula := by
  induction Bs with
  | nil => intro c hc; cases hc
  | cons B Bs ih => exact and_width _ _ (h B (by simp)) (ih (by simp_all))

theorem merge_deterministic {n : ℕ} (Bs : List (Block n))
    (h : ∀ B ∈ Bs, B.Deterministic) : (merge Bs).Deterministic := by
  induction Bs with
  | nil => intro a u v _ _; exact @Subsingleton.elim (BitModels 0) _ u v
  | cons B Bs ih => exact and_deterministic _ _ (h B (by simp)) (ih (by simp_all))

def constrained {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (b : Bool) : Block n :=
  ⟨g, C.constrained out b⟩

theorem constrained_deterministic {n g : ℕ} (C : Circuit n g)
    (out : Fin (n + g)) (b : Bool) : (constrained C out b).Deterministic := by
  intro a u v hu hv
  have h₁ := (Circuit.constrained_eval C out b _).mp hu
  have h₂ := (Circuit.constrained_eval C out b _).mp hv
  exact (Circuit.unique_auxiliaries C a).unique h₁.1 h₂.1

def direct {n : ℕ} (F : Formula n) : Block n :=
  ⟨0, rename (Fin.cast (Nat.add_zero n).symm) F⟩

theorem direct_accepts {n : ℕ} (F : Formula n) (a : BitModels n) :
    (direct F).Accepts a ↔ PrefixCNF.eval F a = true := by
  simp [Accepts, direct, eval_rename]
  congr 1
  funext i
  exact Fin.append_left a finZeroElim i

theorem direct_deterministic {n : ℕ} (F : Formula n) : (direct F).Deterministic := by
  intro a u v _ _; exact @Subsingleton.elim (BitModels 0) _ u v

def projectedFormula {q w : ℕ} (B : Block (q + w)) : Formula (q + (w + B.aux)) :=
  rename (Fin.cast (Nat.add_assoc q w B.aux)) B.formula

theorem projectedFormula_correct {q w : ℕ} (B : Block (q + w)) (a : BitModels q) :
    Projected B.projectedFormula a ↔ ∃ b : BitModels w, B.Accepts (Fin.append a b) := by
  constructor
  · rintro ⟨bu, hbu⟩
    let b := fun i => bu (Fin.castAdd B.aux i)
    let u := fun i => bu (Fin.natAdd w i)
    have he : Fin.append b u = bu := Fin.append_castAdd_natAdd
    refine ⟨b, u, ?_⟩
    rw [projectedFormula, eval_rename] at hbu
    have hassoc := Fin.append_assoc a b u
    rw [← he] at hbu
    change PrefixCNF.eval B.formula (Fin.append a (Fin.append b u) ∘ Fin.cast _) = true at hbu
    rwa [← hassoc] at hbu
  · rintro ⟨b, u, hu⟩
    refine ⟨Fin.append b u, ?_⟩
    rw [projectedFormula, eval_rename]
    change PrefixCNF.eval B.formula (Fin.append a (Fin.append b u) ∘ Fin.cast _) = true
    rwa [← Fin.append_assoc]

theorem projectedFormula_width {q w k : ℕ} (B : Block (q + w)) (h : Width k B.formula) :
    Width k B.projectedFormula := width_rename _ _ h

theorem projectedFormula_length {q w : ℕ} (B : Block (q + w)) :
    B.projectedFormula.length = B.formula.length := by simp [projectedFormula, rename]

end Block
end QecReliability.SharedCircuit
