import Trans.HashCallees.EncoderPlain

/-!
# Trans.HashCallees.EncoderCorrX: XOR-program combinators on plain data

`encX P = encProg P.toProgram` for `P : XorProgram n k`, and its values on the combinators used
by the recursive encoder: `follow`, `rewire`, `keepFollow`, `keepInputs`, the casts,
`oneCopy` (`encX_oneCopy`), and the row emitter `row`, `rows`, `emitKeepZero`
(`encX_emitKeepZero : … = emitP n m c R`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace QecReliability.Trans.HashCallees
open QecReliability.SharedCircuit QecReliability.Trans.Query QecReliability.Trans.Query.Plain
open QecReliability.Trans.Hash

/-- The plain encoding of an XOR program. -/
def encX {n k : ℕ} (P : XorProgram n k) : ProgP := encProg P.toProgram

theorem encX_fst_length {n k : ℕ} (P : XorProgram n k) : (encX P).1.length = P.gates := by
  simp [encX, encProg, XorProgram.toProgram]

theorem encX_snd {n k : ℕ} (P : XorProgram n k) : (encX P).2 = tab P.output := rfl

theorem encX_snd_length {n k : ℕ} (P : XorProgram n k) : (encX P).2.length = k := by
  simp [encX_snd]

theorem encX_follow {n k l : ℕ} (P : XorProgram n k) (Q : XorProgram (n + P.gates) l) :
    encX (P.follow Q) = ((encX P).1 ++ (encX Q).1, (encX Q).2) := by
  simp only [encX, XorProgram.follow_toProgram]
  exact Hash.encProg_follow _ _

theorem encX_rewire {n m k : ℕ} (P : XorProgram n k) (f : Fin n → Fin m) :
    encX (P.rewire f) = (tabGates (tab f, n, m) (encX P).1, tabWires (tab f, n, m) (encX P).2) := by
  simp only [encX, XorProgram.rewire_toProgram]
  exact Hash.encProg_rewire _ _

theorem ofFn_add' {α : Type*} {m n : ℕ} (F : Fin (m + n) → α) :
    List.ofFn F = List.ofFn (fun i => F (Fin.castAdd n i)) ++
      List.ofFn (fun j => F (Fin.natAdd m j)) := by
  rw [List.ofFn_add]; rfl

theorem encX_keepFollow {n k l : ℕ} (P : XorProgram n k) (Q : XorProgram (n + P.gates) l) :
    encX (P.keepFollow Q) = ((encX P).1 ++ (encX Q).1, (encX P).2 ++ (encX Q).2) := by
  simp only [encX, encProg, XorProgram.toProgram, XorProgram.keepFollow,
    XorCircuit.extend_toCircuit, encCirc_extend, Prod.mk.injEq, true_and]
  rw [ofFn_add']
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.coe_cast, Fin.coe_castAdd]

theorem encX_keepInputs {n k : ℕ} (P : XorProgram n k) :
    encX P.keepInputs = ((encX P).1, List.range n ++ (encX P).2) := by
  simp only [encX, encProg, XorProgram.toProgram, XorProgram.keepInputs, Prod.mk.injEq, true_and]
  rw [ofFn_add']
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [← tab_castAdd n P.gates]; rfl

theorem encX_outputCast {n k l : ℕ} (P : XorProgram n k) (h : k = l) :
    encX (P.outputCast h) = encX P := by
  cases h; rfl

theorem encX_inputCast {n m k : ℕ} (P : XorProgram n k) (h : n = m) :
    encX (P.inputCast h) = encX P := by
  cases h; rfl

theorem encX_keepFollow_rewire {n h d : ℕ} (RH : XorProgram n h) (R₂ : XorProgram h d) :
    encX ((RH.keepFollow (R₂.rewire RH.output)).keepInputs) =
      ((pcompose n (encX RH) (encX R₂)).1,
        List.range n ++ (encX RH).2 ++ (pcompose n (encX RH) (encX R₂)).2) := by
  rw [encX_keepInputs, encX_keepFollow, encX_rewire]
  simp only [pcompose, encX_snd_length, encX_fst_length, encX_snd, List.append_assoc, tab_length]

/-- **`oneCopy` on plain data.** -/
theorem encX_oneCopy {n a h d : ℕ} (R₁ : XorProgram n a) (H : XorProgram a h)
    (R₂ : XorProgram h d) :
    encX (XorProgram.oneCopy R₁ H R₂) = oneCopyP n (encX R₁) (encX H) (encX R₂) := by
  have e1 : encX (R₁.follow (H.rewire R₁.output)) = pcompose n (encX R₁) (encX H) := by
    rw [encX_follow, encX_rewire]
    simp only [pcompose, encX_snd_length, encX_fst_length, encX_snd, tab_length]
  simp only [XorProgram.oneCopy]
  rw [encX_keepFollow_rewire, e1]
  rfl

/-! ## The row emitter -/

open FiniteXorRowEmitter

theorem encX_row {n : ℕ} (zero : Fin n) (c : ℕ) (refs : Fin c → Fin n) (r : ℕ → ℕ)
    (hr : ∀ j : Fin c, (refs j).val = r j.val) :
    encX (row zero c refs) =
      ((List.range c).map (fun j => ((false, true, if j = 0 then zero.val else n + j - 1, r j) :
          GateP)),
        [if c = 0 then zero.val else n + c - 1]) := by
  induction c with
  | zero => simp [row, encX, encProg, XorProgram.toProgram, XorCircuit.toCircuit]
  | succ c ih =>
    have ih' := ih (fun i => refs i.castSucc) (fun j => hr j.castSucc)
    have h2 := congrArg Prod.snd ih'
    have hg := row_gates zero c (fun i => refs i.castSucc)
    simp only [encX, encProg, XorProgram.toProgram, List.ofFn_succ, List.ofFn_zero] at h2
    simp only [List.cons.injEq, and_true] at h2
    have h1 := congrArg Prod.fst ih'
    simp only [encX, encProg, XorProgram.toProgram] at h1
    simp only [row, encX, encProg, XorProgram.toProgram, XorCircuit.toCircuit, encCirc_snoc, h1,
      encGate, Fin.coe_castAdd, hr, Fin.val_last, h2, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, Prod.mk.injEq, List.ofFn_succ, List.ofFn_zero, hg]
    refine ⟨trivial, ?_⟩
    simp

theorem encX_rows {n : ℕ} (zero : Fin n) (c m : ℕ) (refs : Fin m → Fin c → Fin n)
    (R : ℕ → ℕ → ℕ) (hR : ∀ (i : Fin m) (j : Fin c), (refs i j).val = R i.val j.val) :
    encX (rows zero c m refs) =
      ((List.range (m * c)).map (fun g => ((false, true,
          if g % c = 0 then zero.val else n + g - 1, R (g / c) (g % c)) : GateP)),
        (List.range m).map (fun i => if c = 0 then zero.val else n + (i + 1) * c - 1)) := by
  induction m with
  | zero => simp [rows, encX, encProg, XorProgram.toProgram, XorCircuit.toCircuit]
  | succ m ih =>
    have ih' := ih (fun i => refs i.castSucc) (fun i j => hR i.castSucc j)
    have hrow := encX_row zero c (refs (Fin.last m)) (R m) (fun j => hR (Fin.last m) j)
    have hg := rows_gates zero c m (fun i => refs i.castSucc)
    have hz := zero.isLt
    have hlt : ∀ j < c, R m j < n := fun j hj => by
      have := hR (Fin.last m) ⟨j, hj⟩; simp only [Fin.val_last] at this
      rw [← this]; exact Fin.isLt _
    simp only [rows, parallel, encX_keepFollow, encX_rewire, ih', hrow, tab_castAdd, hg]
    simp only [tabGates, tabWires, List.map_map, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [show (m + 1) * c = m * c + c by ring, List.range_add, List.map_append, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have hjc : (m * c + j) % c = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      have hjd : (m * c + j) / c = m := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]
      simp only [Function.comp_apply, gmapW, Bool.false_eq_true, ↓reduceIte, tableWire_range,
        shiftWire, hjc, hjd, Prod.mk.injEq, true_and]
      refine ⟨?_, ?_⟩
      · by_cases h0 : j = 0
        · simp [h0, hz]
        · simp only [h0, ↓reduceIte]
          rw [if_neg (by omega)]
          omega
      · rw [if_pos (hlt j hj)]
    · rw [List.range_succ, List.map_append]
      congr 1
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, Function.comp_apply,
        tableWire_range, shiftWire]
      by_cases h0 : c = 0
      · simp [h0, hz]
      · simp only [h0, ↓reduceIte]
        rw [if_neg (by omega)]
        ring_nf; omega

/-- **The row emitter on plain data.** -/
theorem encX_emitKeepZero (n m c : ℕ) (refs : Fin m → Fin c → Fin (n + 1)) (R : ℕ → ℕ → ℕ)
    (hR : ∀ (i : Fin m) (j : Fin c), (refs i j).val = R i.val j.val) :
    encX (emitKeepZero n m c refs) = emitP n m c R := by
  have hrows := encX_rows (Fin.last n) c m refs R hR
  simp only [emitKeepZero, encX_keepFollow, hrows]
  simp only [seedZero, encX, encProg, XorProgram.toProgram, XorCircuit.toCircuit, encCirc_snoc,
    encCirc_nil, encGate, List.nil_append, List.ofFn_succ, List.ofFn_zero, Fin.val_last, emitP,
    List.singleton_append, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · congr 1
    apply List.map_congr_left
    intro g _
    simp only [gateP]
    split_ifs <;> simp <;> omega
  · congr 1
    apply List.map_congr_left
    intro i _
    split_ifs with h <;> simp [h] <;> omega

end QecReliability.Trans.HashCallees
