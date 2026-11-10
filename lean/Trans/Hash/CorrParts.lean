import Trans.Hash.CorrBase

/-!
# Trans.Hash.CorrParts: local affine hashing, XOR transpose and walk symbols on plain data

* `encProg_affineBit`, `encProg_bundle_aff`, `encProg_localAffine` (→ `abit`, `affP`);
* `encProg_addWire`, `encProg_scatter`, `encProg_reverse`, `encProg_transposed` (→ `transP`);
* `visits_val`, `encoderIndex_eq` (→ `pvisits`, `encIndex`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.Hash
open QecReliability.SharedCircuit QecReliability.Trans.Query QecReliability.Trans.Query.Plain

/-! ## Local affine hashing -/

/-- A single-output plain program. -/
def abitP (B : List GateP × ℕ) : ProgP := (B.1, [B.2])

theorem encProg_xorInput {v : ℕ} (P : Program v 1) (x : Fin v) :
    encProg (P.xorInput x) =
      ((encProg P).1 ++ [(false, true, x.val, (P.output 0).val)], [v + P.gates]) := by
  simp [encProg, Program.xorInput, encGate, tab]

theorem encProg_affineBit {v : ℕ} (t : ℕ) (c : BitModels t) (b : Bool) (xs : Fin t → Fin v)
    (x0 : ℕ) (hx : ∀ j, (xs j).val = x0 + j.val) :
    encProg (affineBit t c b xs) = abitP (abit v (List.ofFn c) b x0) := by
  induction t generalizing x0 with
  | zero =>
    simp [affineBit, encProg_constant, abitP, abit]
  | succ t ih =>
    have hih := ih (Fin.tail c) (Fin.tail xs) (x0 + 1)
      (fun j => by simp only [Fin.tail, hx, Fin.val_succ]; omega)
    have hout : (affineBit t (Fin.tail c) b (Fin.tail xs)).output 0 =
        ⟨(abit v (List.ofFn (Fin.tail c)) b (x0 + 1)).2, by
          have := congrArg (fun p => p.2) hih
          simp only [encProg_snd, abitP, tab] at this
          have h0 := congrArg (fun l => l.getD 0 0) this
          simp at h0
          rw [← h0]; exact ((affineBit t (Fin.tail c) b (Fin.tail xs)).output 0).isLt⟩ := by
      have := congrArg (fun p => p.2) hih
      simp only [encProg_snd, abitP, tab] at this
      have h0 := congrArg (fun l => l.getD 0 0) this
      simp at h0
      exact Fin.ext h0
    have hg : (affineBit t (Fin.tail c) b (Fin.tail xs)).gates =
        (abit v (List.ofFn (Fin.tail c)) b (x0 + 1)).1.length := by
      have h1 := congrArg (fun p => p.1.length) hih
      simp only [encProg_fst, encCirc_length, abitP] at h1
      exact h1
    rw [List.ofFn_succ]
    have hx0 : (xs 0).val = x0 := by simpa using hx 0
    cases hc : c 0
    · simp only [affineBit, hc, Bool.false_eq_true, ↓reduceIte, abit]
      exact hih
    · simp only [affineBit, hc, ↓reduceIte, abit, encProg_xorInput, abitP, hout, hx0, hg]
      rw [hih]
      rfl

theorem encProg_bundle_aff {v t : ℕ} (m : ℕ) (P : Fin m → Program v 1) (i0 : ℕ)
    (rows : List (List Bool × Bool)) (hlen : rows.length = m)
    (hP : ∀ i : Fin m, encProg (P i) =
      abitP (abit v (rows[i.val]'(by omega)).1 (rows[i.val]'(by omega)).2 (t * (i0 + i.val)))) :
    encProg (bundle m P) = affP v t i0 rows := by
  induction m generalizing i0 rows with
  | zero =>
    cases rows with
    | nil => rfl
    | cons r rs => simp at hlen
  | succ m ih =>
    cases rows with
    | nil => simp at hlen
    | cons r rs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hih := ih (Fin.tail P) (i0 + 1) rs hlen (fun i => by
        rw [Fin.tail, hP i.succ]
        simp only [Fin.val_succ, List.getElem_cons_succ]
        congr 2; ring)
      have h0 := hP 0
      simp only [Fin.val_zero, List.getElem_cons_zero, Nat.add_zero] at h0
      have hg : (P 0).gates = (abit v r.1 r.2 (t * i0)).1.length := by
        have := congrArg (fun p => p.1.length) h0
        simpa [abitP] using this
      simp only [bundle, encProg_outputCast, encProg_parallel, hih, h0, abitP, affP, hg,
        List.singleton_append]

theorem ofFn_eq_map_range {α : Type*} {n : ℕ} (f : Fin n → α) (g : ℕ → α)
    (h : ∀ i : Fin n, f i = g i.val) : List.ofFn f = (List.range n).map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [h ⟨i, by simpa using h1⟩]

theorem encProg_localAffine (L t : ℕ) (bits : List Bool) (hb : (t + 1) * L ≤ bits.length) :
    encProg (localAffine (seedOfBits L t bits)) = affP (L * t) t 0 (seedRows t L bits) := by
  unfold localAffine
  refine encProg_bundle_aff L _ 0 _ (seedRows_length t L bits) (fun i => ?_)
  rw [encProg_affineBit _ _ _ _ (t * i.val) (fun j => by
    simp only [finProdFinEquiv_apply_val]; ring)]
  rw [seedRows_getElem t L bits hb]
  simp only [Nat.zero_add, seedOfBits_intercept]
  congr 3
  exact ofFn_eq_map_range _ _ (fun j => seedOfBits_coeff L t bits i j)

/-! ## Transpose of XOR programs -/

theorem ofFn_update {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (a : α) :
    List.ofFn (fun j => if j = i then a else f j) = (List.ofFn f).set i.val a := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_ofFn, List.getElem_set, Fin.ext_iff]
    split_ifs <;> first | rfl | omega

theorem encProg_addWire {n v : ℕ} (P : Program n v) (target : Fin v)
    (source : Fin (n + P.gates)) :
    encProg (P.addWire target source) = pAddWire n (encProg P) target.val source.val := by
  simp only [encProg, Program.addWire, encCirc_snoc, encGate, pAddWire, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · simp only [tab, encCirc_length]
    rw [← ofFn_update]
    congr 1; funext j
    split_ifs <;> simp

theorem encProg_scatterList {n v : ℕ} (P : Program n v) (xs : List (Fin v × Fin n)) :
    encProg (scatterList P xs) =
      scatterP n (encProg P) (xs.map (fun p => (p.1.val, p.2.val))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [scatterList, Program.addInput, encProg_addWire, ih, List.map_cons, scatterP,
      Fin.coe_castAdd]

theorem encProg_zeroAccumulator (n v : ℕ) :
    encProg (zeroAccumulator n v) = ([constGate false], List.replicate v n) := by
  simp only [encProg, zeroAccumulator, encCirc_snoc, encCirc_nil, encGate, tab, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply List.ext_getElem <;> simp

theorem idxPairs_ofFn {n : ℕ} (f : Fin n → ℕ) (k : ℕ) :
    idxPairs (List.ofFn f) k = List.ofFn (fun i => (f i, k + i.val)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, idxPairs, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, List.cons.injEq, true_and]
    congr 1; funext i; congr 1; omega

theorem encProg_scatter {n v : ℕ} (out : Fin n → Fin v) :
    encProg (scatter out) =
      scatterP n ([constGate false], List.replicate v n) (idxPairs (tab out) 0) := by
  rw [scatter, encProg_scatterList, encProg_zeroAccumulator, tab, idxPairs_ofFn, List.map_ofFn]
  congr 2
  funext i
  simp

theorem tab_castSucc {n v : ℕ} (f : Fin (v + 1) → Fin n) :
    tab (f ∘ Fin.castSucc) = (tab f).dropLast := by
  simp only [tab]
  rw [List.ofFn_succ' (fun j => (f j).val), List.concat_eq_append, List.dropLast_concat]
  rfl

theorem encProg_select_castSucc {n v : ℕ} (P : Program n (v + 1)) :
    encProg (P.select Fin.castSucc) = ((encProg P).1, (encProg P).2.dropLast) := by
  simp only [encProg, Program.select, Prod.mk.injEq, true_and]
  exact tab_castSucc P.output

theorem encProg_addOutput {n v : ℕ} (P : Program n v) (target source : Fin v) :
    encProg (P.addOutput target source) =
      pAddWire n (encProg P) target.val ((encProg P).2.getD source.val 0) := by
  rw [Program.addOutput, encProg_addWire, encProg_snd, tab_getD _ _ source.isLt]

theorem encProg_reverse {n m : ℕ} {g : ℕ} (C : XorCircuit n g) (P : Program m (n + g)) :
    encProg (C.reverse P) = revP m (encCirc C.toCircuit).reverse (encProg P) := by
  induction C with
  | nil => rfl
  | @zero g C ih =>
    simp only [XorCircuit.reverse, XorCircuit.toCircuit, encCirc_snoc, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, revP]
    rw [ih, encProg_select_castSucc]
    rfl
  | @xor g C x y ih =>
    simp only [XorCircuit.reverse, XorCircuit.toCircuit, encCirc_snoc, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, revP]
    rw [ih]
    congr 1
    simp only [reverseXor, encProg_select_castSucc, encProg_addOutput, revStep, encGate,
      Bool.false_eq_true, ↓reduceIte, Fin.coe_castSucc, Fin.val_last, encProg_snd, tab_length]
    have e : n + (g + 1) - 1 = n + g := by omega
    rw [e]

theorem encProg_transposed {n m : ℕ} (P : Program n m) (h : P.circuit.xorOnly = true) :
    encProg (P.asXor h).transposed = transP n (encProg P) := by
  rw [XorProgram.transposed, encProg_reverse, encProg_scatter]
  simp only [Program.asXor, Circuit.asXor_toCircuit, transP, encProg_fst, encProg_snd, tab_length,
    encCirc_length]

/-! ## Walks and encoder indices -/

theorem visits_val {m d : ℕ} (Gr : ExpanderWalk.PortGraph m d) (nb : ℕ → ℕ → ℕ)
    (hnb : ∀ v i, nb v.val i.val = (Gr.neighbor v i).val) :
    ∀ (k : ℕ) (v : Fin m) (a : Fin k → Fin d) (W : ℕ), (∀ j, (a j).val = W / d ^ j.val % d) →
      ∀ h : Fin (k + 1), (Gr.visits v a h).val = pvisits nb d v.val W h.val := by
  intro k
  induction k with
  | zero =>
    intro v a W _ h
    have : h = 0 := Fin.ext (by omega)
    subst this; rfl
  | succ k ih =>
    intro v a W ha h
    refine Fin.cases ?_ (fun j => ?_) h
    · rfl
    · simp only [ExpanderWalk.PortGraph.visits, Fin.cons_succ, Fin.val_succ, pvisits]
      have h0 : (a 0).val = W % d := by simpa using ha 0
      rw [ih _ (Fin.tail a) (W / d) (fun j => by
        simp only [Fin.tail, ha, Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul])]
      rw [ExpanderWalk.PortGraph.neighbor] at *
      congr 1
      rw [← h0, hnb]
      rfl

end QecReliability.Trans.Hash
