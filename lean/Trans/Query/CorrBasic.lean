import Trans.Query.Types

/-!
# Trans.Query.CorrBasic: the plain construction is the image of the Lean one (generic part)

Renamings, gate maps, circuit compilation/extension/rewiring, program combinators and
block combinators commute with the plain encodings of `Trans/Query/Types.lean`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Query
open QecReliability.SharedCircuit QecReliability.PrefixCNF QecReliability.OracleCost
open Plain

/-! ## Generic wire maps on plain data -/

/-- Map the wires of a plain gate (constants carry none). -/
def gmap (σ : ℕ → ℕ) (g : GateP) : GateP :=
  if g.1 then (if g.2.1 then g else (g.1, g.2.1, σ g.2.2.1, g.2.2.2))
  else (g.1, g.2.1, σ g.2.2.1, σ g.2.2.2)

def fmap (σ : ℕ → ℕ) (F : Form) : Form := F.map (fun c => c.map (fun l => (σ l.1, l.2)))

theorem gateS_eq (e : ℕ × ℕ) : gateS e = gmap (shiftWire e) := rfl
theorem gatesS_eq (e : ℕ × ℕ) (gs : List GateP) : gatesS e gs = gs.map (gmap (shiftWire e)) := rfl
theorem formS_eq (e : ℕ × ℕ) (F : Form) : formS e F = fmap (shiftWire e) F := rfl
theorem formT_eq (e : List ℕ × ℕ × ℕ) (F : Form) : formT e F = fmap (tableWire e) F := rfl
theorem wiresS_eq (e : ℕ × ℕ) (ws : List ℕ) : wiresS e ws = ws.map (shiftWire e) := rfl

theorem gmap_id (g : GateP) : gmap (fun i => i) g = g := by
  unfold gmap; split_ifs <;> rfl

theorem gmap_congr {σ τ : ℕ → ℕ} (h : ∀ i, σ i = τ i) (g : GateP) : gmap σ g = gmap τ g := by
  have : σ = τ := funext h
  rw [this]

theorem fmap_id (F : Form) : fmap (fun i => i) F = F := by simp [fmap]

theorem fmap_append (σ : ℕ → ℕ) (F G : Form) : fmap σ (F ++ G) = fmap σ F ++ fmap σ G := by
  simp [fmap]

theorem shiftWire_zero (a i : ℕ) : shiftWire (a, 0) i = i := by
  unfold shiftWire; split_ifs <;> simp

/-! ## Values of `Fin` maps -/

theorem addCases_val {m n k : ℕ} (l : Fin m → Fin k) (r : Fin n → Fin k) (i : Fin (m + n)) :
    (Fin.addCases (motive := fun _ => Fin k) l r i).val =
      if h : i.val < m then (l ⟨i.val, h⟩).val else (r ⟨i.val - m, by omega⟩).val := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [j.isLt]
  · simp only [Fin.addCases_right, Fin.coe_natAdd]
    rw [dif_neg (by omega)]
    congr 2; apply Fin.ext; simp

/-- The value map of `Circuit.liftWire f g` (independent of `g`). -/
def liftσ {n m : ℕ} (f : Fin n → Fin m) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩).val else m + (i - n)

theorem liftWire_val {n m : ℕ} (f : Fin n → Fin m) (g : ℕ) (i : Fin (n + g)) :
    (Circuit.liftWire f g i).val = liftσ f i.val := by
  unfold Circuit.liftWire liftσ
  rw [addCases_val]
  split_ifs <;> simp

/-- `liftσ` of a `castAdd`-type wiring is a shift. -/
theorem liftσ_shift {n m : ℕ} (f : Fin n → Fin m) (hf : ∀ i, (f i).val = i.val) (hnm : n ≤ m) :
    liftσ f = shiftWire (n, m - n) := by
  funext i
  unfold liftσ shiftWire
  split_ifs with h
  · simp [hf]
  · simp only; omega

/-! ## Formulas -/

theorem encForm_rename {v w : ℕ} (f : Fin v → Fin w) (σ : ℕ → ℕ) (hσ : ∀ i, (f i).val = σ i.val)
    (F : Formula v) : encForm (rename f F) = fmap σ (encForm F) := by
  simp [encForm_eq, rename, fmap, hσ]

theorem encForm_rename_id {v w : ℕ} (f : Fin v → Fin w) (hσ : ∀ i, (f i).val = i.val)
    (F : Formula v) : encForm (rename f F) = encForm F := by
  rw [encForm_rename f (fun i => i) hσ, fmap_id]

/-! ## Gates and circuits -/

theorem encGate_map {v w : ℕ} (f : Fin v → Fin w) (σ : ℕ → ℕ) (hσ : ∀ i, (f i).val = σ i.val)
    (g : Gate v) : encGate (g.map f) = gmap σ (encGate g) := by
  cases g <;> simp [Gate.map, encGate, gmap, hσ, constGate]

theorem encGate_map_id {v w : ℕ} (f : Fin v → Fin w) (hσ : ∀ i, (f i).val = i.val)
    (g : Gate v) : encGate (g.map f) = encGate g := by
  rw [encGate_map f (fun i => i) hσ, gmap_id]

theorem encForm_clauses {v : ℕ} (g : Gate v) (out : Fin v) :
    encForm (g.clauses out) = gateClauses out.val (encGate g) := by
  cases g with
  | constGate b => cases b <;> simp [Gate.clauses, gateClauses, encGate, constGate]
  | _ => simp [Gate.clauses, gateClauses, encGate]

theorem compileAt_append (k : ℕ) (gs hs : List GateP) :
    compileAt k (gs ++ hs) = compileAt k gs ++ compileAt (k + gs.length) hs := by
  induction gs generalizing k with
  | nil => simp [compileAt]
  | cons g gs ih =>
    simp only [List.cons_append, compileAt, ih, List.append_assoc, List.length_cons]
    congr 3; omega

theorem encForm_compile {n g : ℕ} (C : Circuit n g) : encForm C.compile = compileAt n (encCirc C) := by
  induction C with
  | nil => rfl
  | @snoc g C gate ih =>
    simp only [Circuit.compile, encForm_append, encCirc_snoc, compileAt_append, encCirc_length]
    rw [encForm_rename_id Fin.castSucc (fun _ => rfl), ih, encForm_clauses,
      encGate_map_id Fin.castSucc (fun _ => rfl)]
    simp [compileAt]

theorem encCirc_extend {n g : ℕ} (C : Circuit n g) {h : ℕ} (D : Circuit (n + g) h) :
    encCirc (C.extend D) = encCirc C ++ encCirc D := by
  induction D with
  | nil => simp [Circuit.extend]
  | @snoc h D gate ih =>
    simp only [Circuit.extend, encCirc_snoc, ih, List.append_assoc]
    rw [encGate_map_id (Fin.cast (Nat.add_assoc n g h)) (fun _ => rfl)]

theorem encCirc_rewire {n m : ℕ} (f : Fin n → Fin m) {g : ℕ} (C : Circuit n g) :
    encCirc (C.rewire f) = (encCirc C).map (gmap (liftσ f)) := by
  induction C with
  | nil => rfl
  | @snoc g C gate ih =>
    simp only [Circuit.rewire, encCirc_snoc, ih, List.map_append, List.map_cons, List.map_nil]
    rw [encGate_map _ (liftσ f) (liftWire_val f g)]

/-! ## Programs -/

theorem encProg_pure {n k : ℕ} (f : Fin k → Fin n) :
    encProg (Program.pure f) = ([], List.ofFn (fun i => (f i).val)) := rfl

theorem encProg_rewire {n m k : ℕ} (P : Program n k) (f : Fin n → Fin m) :
    encProg (P.rewire f) = ((encProg P).1.map (gmap (liftσ f)), (encProg P).2.map (liftσ f)) := by
  simp only [encProg, Program.rewire, encCirc_rewire, List.map_ofFn, Prod.mk.injEq, true_and]
  congr 1; funext i; simp [liftWire_val]

theorem encProg_follow {n k l : ℕ} (P : Program n k) (Q : Program (n + P.gates) l) :
    encProg (P.follow Q) = ((encProg P).1 ++ (encProg Q).1, (encProg Q).2) := by
  simp [encProg, Program.follow, encCirc_extend]

theorem encProg_outputCast {n k l : ℕ} (P : Program n k) (h : k = l) :
    encProg (P.outputCast h) = encProg P := by
  subst h; rfl

theorem encProg_constant (n : ℕ) (b : Bool) : encProg (Program.constant n b) = ([constGate b], [n]) := by
  simp [encProg, Program.constant, encGate]

theorem encProg_parallel {n k l : ℕ} (P : Program n k) (Q : Program n l) :
    encProg (P.parallel Q) = ((encProg P).1 ++ gatesS (n, P.gates) (encProg Q).1,
      (encProg P).2 ++ wiresS (n, P.gates) (encProg Q).2) := by
  have hl : liftσ (Fin.castAdd (n := n) P.gates) = shiftWire (n, P.gates) := by
    rw [liftσ_shift (Fin.castAdd (n := n) P.gates) (fun _ => rfl) (by omega)]; congr 2; omega
  simp only [encProg, Program.parallel, encCirc_extend, encCirc_rewire, hl, gatesS_eq,
    wiresS_eq, Prod.mk.injEq, true_and]
  rw [List.ofFn_add]
  simp [Fin.addCases_right, liftWire_val, hl, List.map_ofFn, Function.comp_def]
  funext i
  have e : ∀ h, (Fin.castLE h i : Fin (k + l)) = Fin.castAdd l i := fun _ => Fin.ext rfl
  rw [e]; simp

@[simp] theorem encProg_gates_length {n k : ℕ} (P : Program n k) : (encProg P).1.length = P.gates := by
  simp [encProg]

@[simp] theorem encProg_out_length {n k : ℕ} (P : Program n k) : (encProg P).2.length = k := by
  simp [encProg]

/-! ## Blocks -/

theorem encBlock_and {n : ℕ} (B C : Block n) :
    encBlock (B.and C) = blockAnd n (encBlock B) (encBlock C) := by
  have hl : ∀ i, (Block.leftWire n B.aux C.aux i).val = i.val := by
    intro i; unfold Block.leftWire; rw [addCases_val]; split_ifs <;> simp; omega
  have hr : ∀ i, (Block.rightWire n B.aux C.aux i).val = shiftWire (n, B.aux) i.val := by
    intro i; unfold Block.rightWire shiftWire; rw [addCases_val]; split_ifs <;> simp; omega
  simp only [encBlock, Block.and, blockAnd, encForm_append, formS_eq, Prod.mk.injEq, true_and]
  rw [encForm_rename_id _ hl, encForm_rename _ _ hr]

theorem encBlock_empty (n : ℕ) : encBlock (Block.empty n) = (0, []) := rfl

theorem encBlock_merge {n : ℕ} (Bs : List (Block n)) :
    encBlock (Block.merge Bs) = blockMerge n (Bs.map encBlock) := by
  induction Bs with
  | nil => rfl
  | cons B Bs ih => simp [Block.merge, blockMerge, encBlock_and, ih]

theorem encBlock_constrained {n g : ℕ} (C : Circuit n g) (out : Fin (n + g)) (b : Bool) :
    encBlock (Block.constrained C out b) = (g, compileAt n (encCirc C) ++ [[(out.val, b)]]) := by
  simp [encBlock, Block.constrained, Circuit.constrained, encForm_compile]

theorem encBlock_direct {n : ℕ} (F : Formula n) : encBlock (Block.direct F) = (0, encForm F) := by
  simp only [encBlock, Block.direct, Prod.mk.injEq, true_and]
  exact encForm_rename_id _ (fun i => rfl) F

theorem encForm_projectedFormula {q w : ℕ} (B : Block (q + w)) :
    encForm B.projectedFormula = encForm B.formula :=
  encForm_rename_id (Fin.cast (Nat.add_assoc q w B.aux)) (fun _ => rfl) _

theorem encBlock_rewire {n m : ℕ} (B : Block n) (f : Fin n → Fin m) :
    encBlock (B.rewire f) = (B.aux, fmap (liftσ f) (encForm B.formula)) := by
  simp only [encBlock, Block.rewire, Prod.mk.injEq, true_and]
  exact encForm_rename _ _ (liftWire_val f B.aux) _

theorem encBlock_after {n g : ℕ} (C : Circuit n g) (B : Block (n + g)) :
    encBlock (Block.after C B) = (g + B.aux, compileAt n (encCirc C) ++ encForm B.formula) := by
  simp only [encBlock, Block.after, Prod.mk.injEq, true_and]
  rw [encForm_rename_id (Fin.cast (Nat.add_assoc n g B.aux)) (fun _ => rfl), encForm_append,
    encForm_rename_id (Fin.castAdd B.aux) (fun _ => rfl), encForm_compile]

theorem outputUnits_ofFn {k : ℕ} (f : Fin k → ℕ) (g : Fin k → Bool) :
    Plain.outputUnits (List.ofFn f) (List.ofFn g) = List.ofFn (fun i => [(f i, g i)]) := by
  induction k with
  | zero => simp [Plain.outputUnits]
  | succ k ih => simp [List.ofFn_succ, Plain.outputUnits, ih]

theorem encBlock_matchBlock {v k : ℕ} (P : Program v k) (bits : BitModels k) :
    encBlock (P.matchBlock bits) = Plain.matchBlock v (encProg P) (List.ofFn bits) := by
  simp only [encBlock, Program.matchBlock, Plain.matchBlock, encForm_append, encForm_compile,
    encProg_gates_length, Prod.mk.injEq, true_and]
  congr 1
  simp only [encProg, outputUnits_ofFn, SharedCircuit.outputUnits, encForm_eq, List.map_ofFn]
  rfl

theorem encBlock_hashCell {q w t : ℕ} (B : Block (q + w)) (H : Program q t) (target : BitModels t) :
    encBlock (B.hashCell H target) =
      Plain.hashCell q w (encBlock B) (encProg H) (List.ofFn target) := by
  have hl : liftσ (Fin.castAdd (n := q) w) = shiftWire (q, w) := by
    rw [liftσ_shift (Fin.castAdd (n := q) w) (fun _ => rfl) (by omega)]; congr 2; omega
  simp only [Block.hashCell, encBlock_and, encBlock_matchBlock, encProg_rewire, hl,
    Plain.hashCell, gatesS_eq, wiresS_eq]

end QecReliability.Trans.Query
