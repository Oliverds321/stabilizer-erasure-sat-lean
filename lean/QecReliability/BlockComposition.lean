import QecReliability.GoodEncoder

/-! Supplied-DAG composition and hash-cell filtering preserve the original projection keys. -/
namespace QecReliability.SharedCircuit
open PrefixCNF
namespace Block

def rewire {n m : ℕ} (B : Block n) (f : Fin n → Fin m) : Block m :=
  ⟨B.aux, rename (Circuit.liftWire f B.aux) B.formula⟩

theorem rewire_eval {n m : ℕ} (B : Block n) (f : Fin n → Fin m) (a : BitModels m) (u : BitModels B.aux) :
    PrefixCNF.eval (B.rewire f).formula (Fin.append a u) = PrefixCNF.eval B.formula (Fin.append (a ∘ f) u) := by
  change PrefixCNF.eval (rename _ B.formula) _ = _
  rw [eval_rename]
  dsimp only [rewire]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Circuit.liftWire, Function.comp_def]

theorem rewire_accepts {n m : ℕ} (B : Block n) (f : Fin n → Fin m) (a : BitModels m) :
    (B.rewire f).Accepts a ↔ B.Accepts (a ∘ f) := by
  unfold Accepts
  exact exists_congr (fun u => by rw [rewire_eval])

theorem rewire_deterministic {n m : ℕ} (B : Block n) (f : Fin n → Fin m) (h : B.Deterministic) :
    (B.rewire f).Deterministic := by
  intro a u v hu hv
  rw [rewire_eval] at hu hv
  exact h (a ∘ f) u v hu hv

theorem rewire_width {n m k : ℕ} (B : Block n) (f : Fin n → Fin m) (h : Width k B.formula) :
    Width k (B.rewire f).formula := width_rename _ _ h

@[simp] theorem rewire_length {n m : ℕ} (B : Block n) (f : Fin n → Fin m) :
    (B.rewire f).formula.length = B.formula.length := by simp [rewire, rename]

def after {n g : ℕ} (C : Circuit n g) (B : Block (n + g)) : Block n where
  aux := g + B.aux
  formula := rename (Fin.cast (Nat.add_assoc n g B.aux))
    (rename (Fin.castAdd B.aux) C.compile ++ B.formula)

theorem after_eval {n g : ℕ} (C : Circuit n g) (B : Block (n + g))
    (a : BitModels n) (u : BitModels g) (v : BitModels B.aux) :
    PrefixCNF.eval (after C B).formula (Fin.append a (Fin.append u v)) =
      (PrefixCNF.eval C.compile (Fin.append a u) && PrefixCNF.eval B.formula (Fin.append (Fin.append a u) v)) := by
  change PrefixCNF.eval (rename _ (_ ++ _)) _ = _
  rw [eval_rename]
  change PrefixCNF.eval _ (Fin.append a (Fin.append u v) ∘ Fin.cast _) = _
  rw [← Fin.append_assoc]
  simp only [PrefixCNF.eval, List.all_append]
  change (PrefixCNF.eval (rename _ C.compile) _ && _) = _
  rw [eval_rename]
  simp only [Fin.append_left]
  rfl

theorem after_accepts {n g : ℕ} (C : Circuit n g) (B : Block (n + g)) (a : BitModels n) :
    (after C B).Accepts a ↔ B.Accepts (C.run a) := by
  constructor
  · rintro ⟨uv, huv⟩
    let u := fun i => uv (Fin.castAdd B.aux i)
    let v := fun i => uv (Fin.natAdd g i)
    have he : Fin.append u v = uv := Fin.append_castAdd_natAdd
    rw [← he, after_eval, Bool.and_eq_true] at huv
    have hu := Circuit.satisfying_unique C a (Fin.append a u) huv.1 (by funext i; exact Fin.append_left _ _ _)
    exact ⟨v, by simpa only [hu] using huv.2⟩
  · rintro ⟨v, hv⟩
    refine ⟨Fin.append (C.auxiliaries a) v, ?_⟩
    rw [after_eval, Circuit.append_auxiliaries, Circuit.run_satisfies, hv]
    rfl

theorem after_deterministic {n g : ℕ} (C : Circuit n g) (B : Block (n + g))
    (hB : B.Deterministic) : (after C B).Deterministic := by
  intro a u v hu hv
  have eu := Fin.append_castAdd_natAdd (f := u)
  have ev := Fin.append_castAdd_natAdd (f := v)
  rw [← eu, after_eval, Bool.and_eq_true] at hu
  rw [← ev, after_eval, Bool.and_eq_true] at hv
  have hfirst := (Circuit.unique_auxiliaries C a).unique hu.1 hv.1
  rw [hfirst] at hu
  have hlast := hB _ _ _ hu.2 hv.2
  rw [← eu, ← ev, hfirst, hlast]

theorem after_width {n g : ℕ} (C : Circuit n g) (B : Block (n + g)) (hB : Width 3 B.formula) :
    Width 3 (after C B).formula := by
  apply width_rename
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact width_rename _ _ (Circuit.compile_width C) c hc
  · exact hB c hc

theorem after_length {n g : ℕ} (C : Circuit n g) (B : Block (n + g)) :
    (after C B).formula.length ≤ 4 * g + B.formula.length := by
  have h := Circuit.compile_length C
  simpa [after, rename] using Nat.add_le_add_right h B.formula.length

def hashCell {q w t : ℕ} (B : Block (q + w)) (H : Program q t) (target : BitModels t) : Block (q + w) :=
  B.and ((H.rewire (Fin.castAdd w)).matchBlock target)

theorem hashCell_projected {q w t : ℕ} (B : Block (q + w)) (H : Program q t)
    (target : BitModels t) (a : BitModels q) :
    Projected (B.hashCell H target).projectedFormula a ↔
      Projected B.projectedFormula a ∧ H.eval a = target := by
  have hi : ∀ b : BitModels w, Fin.append a b ∘ Fin.castAdd w = a := by
    intro b; funext i; exact Fin.append_left _ _ _
  rw [projectedFormula_correct, projectedFormula_correct]
  simp only [hashCell, and_accepts, Program.matchBlock_correct, Program.rewire_eval, hi]
  constructor
  · rintro ⟨b, hb, hh⟩; exact ⟨⟨b, hb⟩, hh⟩
  · rintro ⟨⟨b, hb⟩, hh⟩; exact ⟨b, hb, hh⟩

theorem hashCell_contract {q w t : ℕ} (B : Block (q + w)) (H : Program q t) (target : BitModels t)
    (hwidth : Width 3 B.formula) (hdet : B.Deterministic) :
    (B.hashCell H target).aux = B.aux + H.gates ∧
    (B.hashCell H target).formula.length ≤ B.formula.length + 4 * H.gates + t ∧
    Width 3 (B.hashCell H target).formula ∧ (B.hashCell H target).Deterministic := by
  refine ⟨rfl, ?_, and_width _ _ hwidth (Program.matchBlock_width _ _),
    and_deterministic _ _ hdet (Program.matchBlock_deterministic _ _)⟩
  rw [hashCell, and_length]
  have h := Program.matchBlock_length (H.rewire (Fin.castAdd w)) target
  change _ ≤ 4 * H.gates + t at h
  omega

end Block
end QecReliability.SharedCircuit
