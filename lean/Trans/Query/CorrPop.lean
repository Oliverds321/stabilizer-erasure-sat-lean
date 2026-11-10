import Trans.Query.CorrBasic

/-!
# Trans.Query.CorrPop: ripple adder, adder tree, population counter, weight block

`encProg (ripple k x y c) = Plain.ripple v …`, `encProg (countTree k xs z) = Plain.countTree v …`,
`encProg (population n) = Plain.population n`, and
`encBlock (weightBlock causeWire j) = Plain.weightBlock r (keySize n r + w) j`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.Query
open QecReliability.SharedCircuit QecReliability.PrefixCNF QecReliability.OracleCost
open Plain

theorem gatesS_zero (a : ℕ) (gs : List GateP) : gatesS (a, 0) gs = gs := by
  unfold gatesS
  rw [show (fun g => gateS (a, 0) g) = id from
    funext (fun g => by rw [gateS_eq, gmap_congr (shiftWire_zero a), gmap_id]; rfl), List.map_id]

theorem wiresS_zero (a : ℕ) (ws : List ℕ) : wiresS (a, 0) ws = ws := by
  unfold wiresS
  rw [show (fun w => shiftWire (a, 0) w) = id from funext (fun w => shiftWire_zero a w), List.map_id]

@[simp] theorem program_pure_gates {n k : ℕ} (f : Fin k → Fin n) : (Program.pure f).gates = 0 := rfl

theorem ofFn_take_add {α : Type} {a b : ℕ} (f : Fin (a + b) → α) :
    (List.ofFn f).take a = List.ofFn (fun i => f (Fin.castAdd b i)) := by
  rw [List.ofFn_add, List.take_left' (by simp)]; rfl

theorem ofFn_drop_add {α : Type} {a b : ℕ} (f : Fin (a + b) → α) :
    (List.ofFn f).drop a = List.ofFn (fun i => f (Fin.natAdd a i)) := by
  rw [List.ofFn_add, List.drop_left' (by simp)]

/-! ## Ripple adder -/

theorem encProg_fullAdder_rewire {v : ℕ} (x y c : Fin v) :
    encProg (fullAdder.rewire ![x, y, c]) = (adderGates v x.val y.val c.val, [v + 1, v + 4]) := by
  rfl

theorem fullAdder_rewire_gates {v : ℕ} (f : Fin 3 → Fin v) : (fullAdder.rewire f).gates = 5 := rfl

theorem encProg_ripple {v : ℕ} (k : ℕ) (x y : Fin k → Fin v) (c : Fin v) :
    encProg (SharedCircuit.ripple k x y c) =
      Plain.ripple v (List.ofFn (fun i => (x i).val)) (List.ofFn (fun i => (y i).val)) c.val := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    have hF := encProg_fullAdder_rewire (x 0) (y 0) c
    have ho0 : ((fullAdder.rewire ![x 0, y 0, c]).output 0).val = v + 1 := by
      have := congrArg (fun p => p.2) hF
      simp only [encProg] at this
      exact congrArg (fun l => l.getD 0 0) this
    have ho1 : ((fullAdder.rewire ![x 0, y 0, c]).output 1).val = v + 4 := by
      have := congrArg (fun p => p.2) hF
      simp only [encProg] at this
      exact congrArg (fun l => l.getD 1 0) this
    simp only [SharedCircuit.ripple]
    rw [encProg_follow, encProg_outputCast, encProg_parallel, encProg_pure, ih, hF]
    simp only [fullAdder_rewire_gates, List.ofFn_succ, Plain.ripple, ho0, ho1, Fin.coe_castAdd,
      List.nil_append, List.ofFn_zero, List.singleton_append, program_pure_gates]
    rw [gatesS_zero, wiresS_zero]

/-! ## Adder tree -/

theorem encProg_countTree {v : ℕ} (k : ℕ) (xs : Fin (leaves k) → Fin v) (z : Fin v) :
    encProg (countTree k xs z) = Plain.countTree v k (List.ofFn (fun i => (xs i).val)) z.val := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    set xl : Fin (leaves k) → Fin v := fun i => xs (Fin.castAdd (leaves k) i) with hxl
    set xr : Fin (leaves k) → Fin v := fun i => xs (Fin.natAdd (leaves k) i) with hxr
    have hlen : (List.ofFn (fun i => (xs i).val)).length / 2 = leaves k := by
      simp only [List.length_ofFn, leaves]; omega
    have htake : (List.ofFn (fun i => (xs i).val)).take (leaves k) = List.ofFn (fun i => (xl i).val) :=
      ofFn_take_add (a := leaves k) (b := leaves k) (fun i => (xs i).val)
    have hdrop : (List.ofFn (fun i => (xs i).val)).drop (leaves k) = List.ofFn (fun i => (xr i).val) :=
      ofFn_drop_add (a := leaves k) (b := leaves k) (fun i => (xs i).val)
    have hgl : (countTree k xl z).gates = (Plain.countTree v k (List.ofFn (fun i => (xl i).val)) z.val).1.length := by
      rw [← ih, encProg_gates_length]
    set P := (countTree k xl z).parallel (countTree k xr z) with hP
    have hPe : encProg P = ((Plain.countTree v k (List.ofFn (fun i => (xl i).val)) z.val).1 ++
        gatesS (v, (Plain.countTree v k (List.ofFn (fun i => (xl i).val)) z.val).1.length)
          (Plain.countTree v k (List.ofFn (fun i => (xr i).val)) z.val).1,
        (Plain.countTree v k (List.ofFn (fun i => (xl i).val)) z.val).2 ++
        wiresS (v, (Plain.countTree v k (List.ofFn (fun i => (xl i).val)) z.val).1.length)
          (Plain.countTree v k (List.ofFn (fun i => (xr i).val)) z.val).2) := by
      rw [hP, encProg_parallel, ih, ih, hgl]
    have hPg : P.gates = (encProg P).1.length := (encProg_gates_length P).symm
    have hl : List.ofFn (fun i => (P.output (Fin.castAdd (k + 1) i)).val) = (encProg P).2.take (k + 1) := by
      rw [show (encProg P).2 = List.ofFn (fun i => (P.output i).val) from rfl, ofFn_take_add]
    have hr : List.ofFn (fun i => (P.output (Fin.natAdd (k + 1) i)).val) = (encProg P).2.drop (k + 1) := by
      rw [show (encProg P).2 = List.ofFn (fun i => (P.output i).val) from rfl, ofFn_drop_add]
    change encProg (P.follow (SharedCircuit.ripple (k + 1) (fun i => P.output (Fin.castAdd (k + 1) i))
        (fun i => P.output (Fin.natAdd (k + 1) i)) (Fin.castAdd P.gates z))) = _
    rw [encProg_follow, encProg_ripple, hl, hr, Fin.coe_castAdd, hPg, hPe]
    simp only [Plain.countTree, hlen, htake, hdrop]

/-! ## Population counter -/

theorem size_eq_log2_succ {m : ℕ} (hm : m ≠ 0) : m.size = Nat.log2 m + 1 := by
  apply le_antisymm
  · rw [Nat.size_le]; exact Nat.lt_log2_self
  · rw [Nat.succ_le_iff, Nat.lt_size]; exact Nat.log2_self_le hm

theorem counterDepth_eq (n : ℕ) : counterDepth n = (max 1 n).size := by
  rw [counterDepth, size_eq_log2_succ (by omega)]

theorem leaves_counterDepth (n : ℕ) : leaves (counterDepth n) = pow2Size (max 1 n) := by
  rw [leaves_pow, counterDepth_eq, pow2Size]

theorem le_pow2Size (n : ℕ) : n ≤ pow2Size (max 1 n) := by
  unfold pow2Size
  have := Nat.lt_size_self (max 1 n)
  omega

theorem ofFn_paddedWire (n : ℕ) :
    List.ofFn (fun i => (paddedWire n i).val) = paddedWires n := by
  have hL := le_pow2Size n
  apply List.ext_getElem
  · simp [paddedWires, leaves_counterDepth]; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, paddedWire, paddedWires]
    rw [List.getElem_append]
    split_ifs with h3 h4 h4
    · simp
    · simp at h4; omega
    · simp at h4; omega
    · simp

theorem encProg_population (n : ℕ) : encProg (population n) = Plain.population n := by
  rw [SharedCircuit.population, encProg_follow, encProg_constant, encProg_countTree, ofFn_paddedWire]
  simp only [Plain.population, Fin.val_last, counterDepth_eq]
  rfl

/-! ## Weight block -/

theorem ofFn_targetBits (k j : ℕ) : List.ofFn (targetBits k j) = QueryCodec.word k j := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [targetBits, QueryCodec.word, List.ofFn_succ, ← ih]

theorem encBlock_weight (n r w j : ℕ) :
    encBlock (weightBlock (LatentEncoding.causeWire (n := n) (r := r) (w := w)) j) =
      Plain.weightBlock r (r + (n + n) + w) j := by
  have hl : liftσ (LatentEncoding.causeWire (n := n) (r := r) (w := w)) =
      shiftWire (r, r + (n + n) + w - r) := by
    rw [liftσ_shift (LatentEncoding.causeWire (n := n) (r := r) (w := w)) (fun i => rfl)
      (by simp [LatentEncoding.keySize]; omega)]
  rw [SharedCircuit.weightBlock, encBlock_matchBlock, encProg_rewire, encProg_population, hl, ofFn_targetBits,
    counterDepth_eq]
  rfl

end QecReliability.Trans.Query
