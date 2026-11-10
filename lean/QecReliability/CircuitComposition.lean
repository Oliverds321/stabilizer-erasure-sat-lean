import QecReliability.SharedCircuitCore

/-! Sequential composition retains shared wires and adds gate counts. -/
namespace QecReliability.SharedCircuit.Circuit

def extend {n g : ℕ} (C : Circuit n g) : {h : ℕ} → Circuit (n + g) h → Circuit n (g + h)
  | _, .nil => C
  | _, .snoc D gate => (extend C D).snoc (gate.map (Fin.cast (Nat.add_assoc n g _)))

theorem extend_run {n g h : ℕ} (C : Circuit n g) (D : Circuit (n + g) h)
    (a : BitModels n) (i : Fin ((n + g) + h)) :
    (C.extend D).run a (Fin.cast (Nat.add_assoc n g h) i) = D.run (C.run a) i := by
  induction D with
  | nil => rfl
  | @snoc h D gate ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have he : Fin.cast (Nat.add_assoc n g (h + 1)) (Fin.last ((n + g) + h)) =
          Fin.last (n + (g + h)) := by apply Fin.ext; simp [Nat.add_assoc]
      have hg : (gate.map (Fin.cast (Nat.add_assoc n g h))).eval ((C.extend D).run a) =
          gate.eval (D.run (C.run a)) := by
        rw [Gate.eval_map]
        congr 1
        funext j
        exact ih j
      exact (congrArg ((C.extend (D.snoc gate)).run a) he).trans
        ((snoc_output (C.extend D) _ a).trans (hg.trans (snoc_output D gate (C.run a)).symm))
    · change ((C.extend D).snoc (gate.map _)).run a
        (Fin.castSucc (Fin.cast (Nat.add_assoc n g h) j)) =
        (D.snoc gate).run (C.run a) j.castSucc
      rw [snoc_old, snoc_old]
      exact ih j

def liftWire {n m : ℕ} (f : Fin n → Fin m) (g : ℕ) : Fin (n + g) → Fin (m + g) :=
  Fin.addCases (fun i => Fin.castAdd g (f i)) (Fin.natAdd m)

def rewire {n m : ℕ} (f : Fin n → Fin m) : {g : ℕ} → Circuit n g → Circuit m g
  | _, .nil => .nil
  | _, .snoc C gate => (rewire f C).snoc (gate.map (liftWire f _))

theorem rewire_run {n m g : ℕ} (f : Fin n → Fin m) (C : Circuit n g)
    (a : BitModels m) (i : Fin (n + g)) :
    (C.rewire f).run a (liftWire f g i) = C.run (a ∘ f) i := by
  induction C with
  | nil =>
    change a (liftWire f 0 i) = a (f i)
    exact congrArg a (Fin.addCases_left (motive := fun _ => Fin (m + 0))
      (left := fun j => Fin.castAdd 0 (f j)) (right := Fin.natAdd m) i)
  | @snoc g C gate ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hlast : liftWire f (g + 1) (Fin.last (n + g)) = Fin.last (m + g) := by
        have he : Fin.last (n + g) = Fin.natAdd n (Fin.last g) := by apply Fin.ext; rfl
        rw [he]
        simp only [liftWire, Fin.addCases_right]
        apply Fin.ext; rfl
      have hlast' : liftWire f (g + 1) (Fin.last (n.add g)) = Fin.last (m + g) := hlast
      rw [hlast']
      change ((C.rewire f).snoc (gate.map _)).run a _ = (C.snoc gate).run (a ∘ f) _
      have hg : (gate.map (liftWire f g)).eval ((C.rewire f).run a) =
          gate.eval (C.run (a ∘ f)) := by
        rw [Gate.eval_map]
        congr 1
        funext j
        exact ih j
      exact (snoc_output (C.rewire f) _ a).trans (hg.trans (snoc_output C gate (a ∘ f)).symm)
    · have hold : liftWire f (g + 1) j.castSucc = (liftWire f g j).castSucc := by
        refine Fin.addCases (fun k => ?_) (fun k => ?_) j
        · change liftWire f (g + 1) (Fin.castAdd (g + 1) k) = _
          simp only [liftWire, Fin.addCases_left]
          rfl
        · change liftWire f (g + 1) (Fin.natAdd n k.castSucc) = _
          simp only [liftWire, Fin.addCases_right]
          rfl
      rw [hold]
      change ((C.rewire f).snoc (gate.map _)).run a _ = (C.snoc gate).run (a ∘ f) _
      rw [snoc_old, snoc_old]
      exact ih j

end QecReliability.SharedCircuit.Circuit
