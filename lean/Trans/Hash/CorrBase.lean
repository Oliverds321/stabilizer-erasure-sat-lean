import Trans.Hash.Plain

/-!
# Trans.Hash.CorrBase: program combinators commute with `encProg`

`encProg` of `Circuit.extend/rewire`, `Program.compose`, `Program.pure`, `Program.follow`,
`Program.rewire`, `Program.parallel`, `Program.constant`, `padInputsAndOutputs`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.Hash
open QecReliability.SharedCircuit QecReliability.Trans.Query QecReliability.Trans.Query.Plain

/-- The table of a `Fin` map. -/
def tab {n m : ℕ} (f : Fin n → Fin m) : List ℕ := List.ofFn (fun j => (f j).val)

@[simp] theorem tab_length {n m : ℕ} (f : Fin n → Fin m) : (tab f).length = n := by simp [tab]

theorem tab_getD {n m : ℕ} (f : Fin n → Fin m) (i : ℕ) (h : i < n) :
    (tab f).getD i 0 = (f ⟨i, h⟩).val := by
  simp [tab, List.getD_eq_getElem?_getD, h]

theorem tableWire_lt (e : List ℕ × ℕ × ℕ) (i : ℕ) (h : i < e.2.1) :
    tableWire e i = e.1.getD i 0 := by simp [tableWire, h]

theorem tableWire_ge (e : List ℕ × ℕ × ℕ) (i : ℕ) (h : e.2.1 ≤ i) :
    tableWire e i = e.2.2 + (i - e.2.1) := by simp [tableWire, Nat.not_lt.mpr h]

theorem liftWire_val {n m : ℕ} (f : Fin n → Fin m) (g : ℕ) (i : Fin (n + g)) :
    (Circuit.liftWire f g i).val = tableWire (tab f, n, m) i.val := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Circuit.liftWire, Fin.addCases_left, Fin.coe_castAdd]
    rw [tableWire_lt _ _ j.isLt, tab_getD f j.val j.isLt]
  · simp only [Circuit.liftWire, Fin.addCases_right, Fin.coe_natAdd]
    rw [tableWire_ge _ _ (by simp)]
    simp

theorem encGate_map {v w : ℕ} (f : Fin v → Fin w) (σ : ℕ → ℕ) (hσ : ∀ i, (f i).val = σ i.val)
    (g : Gate v) : encGate (g.map f) = gmapW σ (encGate g) := by
  cases g <;> simp [Gate.map, encGate, gmapW, hσ, constGate]

theorem encGate_map_id {v w : ℕ} (f : Fin v → Fin w) (hσ : ∀ i, (f i).val = i.val)
    (g : Gate v) : encGate (g.map f) = encGate g := by
  rw [encGate_map f (fun i => i) hσ]
  unfold gmapW; split_ifs <;> rfl

theorem encCirc_extend {n g : ℕ} (C : Circuit n g) {h : ℕ} (D : Circuit (n + g) h) :
    encCirc (C.extend D) = encCirc C ++ encCirc D := by
  induction D with
  | nil => simp [Circuit.extend]
  | @snoc h D gate ih =>
    simp only [Circuit.extend, encCirc_snoc, ih, List.append_assoc]
    rw [encGate_map_id (Fin.cast (Nat.add_assoc n g h)) (fun _ => rfl)]

theorem encCirc_rewire {n m : ℕ} (f : Fin n → Fin m) {g : ℕ} (C : Circuit n g) :
    encCirc (C.rewire f) = tabGates (tab f, n, m) (encCirc C) := by
  induction C with
  | nil => rfl
  | @snoc g C gate ih =>
    simp only [Circuit.rewire, encCirc_snoc, ih, tabGates, List.map_append, List.map_cons,
      List.map_nil]
    rw [encGate_map _ (tableWire (tab f, n, m)) (liftWire_val f g)]

@[simp] theorem encProg_fst {n k : ℕ} (P : Program n k) : (encProg P).1 = encCirc P.circuit := rfl
@[simp] theorem encProg_snd {n k : ℕ} (P : Program n k) : (encProg P).2 = tab P.output := rfl

theorem encProg_compose {n m k : ℕ} (P : Program n m) (Q : Program m k) :
    encProg (P.compose Q) = pcompose n (encProg P) (encProg Q) := by
  simp only [encProg, Program.compose, pcompose, encCirc_extend, encCirc_rewire, tabWires,
    Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · congr 3 <;> simp [tab]
  · simp only [List.map_ofFn, Fin.coe_cast]
    congr 1
    funext i
    simp [liftWire_val, tab]

theorem encProg_pure {n k : ℕ} (f : Fin k → Fin n) : encProg (Program.pure f) = ([], tab f) := rfl

theorem encProg_select {n m k : ℕ} (P : Program n m) (f : Fin k → Fin m) :
    encProg (P.compose (Program.pure f)) = pselect (encProg P) (tab f) := by
  rw [encProg_compose, encProg_pure]
  simp only [pcompose, pselect, tabGates, List.map_nil, List.append_nil, tabWires, tab,
    List.map_ofFn, Prod.mk.injEq, true_and]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [tableWire_lt _ _ (by simp)]

theorem encProg_follow {n k l : ℕ} (P : Program n k) (Q : Program (n + P.gates) l) :
    encProg (P.follow Q) = ((encProg P).1 ++ (encProg Q).1, (encProg Q).2) := by
  simp [encProg, Program.follow, encCirc_extend, tab]

theorem encProg_rewire {n m k : ℕ} (P : Program n k) (f : Fin n → Fin m) :
    encProg (P.rewire f) = (tabGates (tab f, n, m) (encProg P).1,
      tabWires (tab f, n, m) (encProg P).2) := by
  simp only [encProg, Program.rewire, encCirc_rewire, tabWires, Prod.mk.injEq, true_and]
  simp [tab, List.map_ofFn, Function.comp_def, liftWire_val]

theorem encProg_outputCast {n k l : ℕ} (P : Program n k) (h : k = l) :
    encProg (P.outputCast h) = encProg P := by
  subst h; rfl

theorem encProg_constant (n : ℕ) (b : Bool) :
    encProg (Program.constant n b) = ([constGate b], [n]) := by
  simp [encProg, Program.constant, encGate]

theorem tab_castAdd (n k : ℕ) : tab (Fin.castAdd k : Fin n → Fin (n + k)) = List.range n := by
  apply List.ext_getElem <;> simp [tab]

theorem tableWire_range (v k i : ℕ) :
    tableWire (List.range v, v, v + k) i = shiftWire (v, k) i := by
  by_cases h : i < v
  · rw [tableWire_lt _ _ h]; simp [shiftWire, h, List.getD_eq_getElem?_getD]
  · rw [tableWire_ge _ _ (by simpa using h)]; simp [shiftWire, h]; omega

theorem encProg_parallel {n k l : ℕ} (P : Program n k) (Q : Program n l) :
    encProg (P.parallel Q) = ((encProg P).1 ++ tabGates (List.range n, n, n + P.gates) (encProg Q).1,
      (encProg P).2 ++ tabWires (List.range n, n, n + P.gates) (encProg Q).2) := by
  simp only [encProg, Program.parallel, encCirc_extend, encCirc_rewire, tab_castAdd,
    Prod.mk.injEq, true_and]
  simp only [tab, tabWires, List.map_ofFn]
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    have e : ∀ h, (Fin.castLE h i : Fin (k + l)) = Fin.castAdd l i := fun _ => Fin.ext rfl
    rw [e]; simp
  · congr 1
    funext i
    simp only [Fin.addCases_right, Fin.coe_cast, Function.comp_apply, liftWire_val]
    rw [← tab_castAdd n P.gates]

/-! ## Padding -/

theorem tab_zeroInput (q a : ℕ) : tab (UniformAdapter.zeroInput q a) = padTable a q := by
  apply List.ext_getElem
  · simp [padTable]
  · intro i h1 h2
    simp only [tab, List.getElem_ofFn, UniformAdapter.zeroInput, padTable, List.getElem_map,
      List.getElem_range]
    split_ifs <;> simp

theorem encProg_keepZeroOutputs {q N : ℕ} (P : Program (q + 1) N) (z : ℕ) :
    encProg (UniformAdapter.keepZeroOutputs P z) =
      ((encProg P).1, (encProg P).2 ++ List.replicate z q) := by
  simp only [encProg, UniformAdapter.keepZeroOutputs, tab, Prod.mk.injEq, true_and]
  rw [List.ofFn_add]
  congr 1
  · congr 1; funext i; simp
  · apply List.ext_getElem <;> simp

theorem encProg_padInputsAndOutputs {a N : ℕ} (P : Program a N) (q m : ℕ) (h : N ≤ m) :
    encProg (UniformAdapter.padInputsAndOutputs P q m h) = padP a q m (encProg P) := by
  simp only [UniformAdapter.padInputsAndOutputs, encProg_outputCast,
    UniformAdapter.padInputsAndAppend, encProg_follow, encProg_constant, encProg_keepZeroOutputs,
    encProg_rewire, tab_zeroInput, padP, List.singleton_append, encProg_snd, tab_length]

end QecReliability.Trans.Hash
