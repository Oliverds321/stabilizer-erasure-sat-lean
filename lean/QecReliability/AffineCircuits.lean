import QecReliability.CodeHashStages

/-! Explicit shared circuits for independently seeded local affine bits. -/
namespace QecReliability.SharedCircuit
open scoped BigOperators

def Program.xorInput {v : ℕ} (P : Program v 1) (x : Fin v) : Program v 1 where
  gates := P.gates + 1
  circuit := P.circuit.snoc (.xorGate (Fin.castAdd P.gates x) (P.output 0))
  output _ := Fin.last (v + P.gates)

theorem Program.xorInput_eval {v : ℕ} (P : Program v 1) (x : Fin v) (a : BitModels v) :
    (P.xorInput x).eval a 0 = xor (a x) (P.eval a 0) := by
  change (P.circuit.snoc _).run a (Fin.last _) = _
  apply (Circuit.snoc_output P.circuit (.xorGate (Fin.castAdd P.gates x) (P.output 0)) a).trans
  change xor (P.circuit.run a (Fin.castAdd P.gates x)) (P.eval a 0) = _
  rw [Circuit.run_primary]

def affineBit {v : ℕ} : (t : ℕ) → BitModels t → Bool → (Fin t → Fin v) → Program v 1
  | 0, _, b, _ => Program.constant v b
  | t + 1, c, b, xs =>
      let P := affineBit t (Fin.tail c) b (Fin.tail xs)
      if c 0 then P.xorInput (xs 0) else P

theorem affineBit_gates {v : ℕ} (t : ℕ) (c : BitModels t) (b : Bool) (xs : Fin t → Fin v) :
    (affineBit t c b xs).gates ≤ t + 1 := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    simp only [affineBit]
    split
    · change (affineBit t (Fin.tail c) b (Fin.tail xs)).gates + 1 ≤ t + 1 + 1
      exact Nat.add_le_add_right (ih _ _) 1
    · exact (ih _ _).trans (by omega)

theorem affineBit_correct {v : ℕ} (t : ℕ) (c : BitModels t) (b : Bool)
    (xs : Fin t → Fin v) (a : BitModels v) :
    boolBit ((affineBit t c b xs).eval a 0) =
      (∑ j, boolBit (c j) * boolBit (a (xs j))) + boolBit b := by
  induction t with
  | zero => simp [affineBit, Program.constant_eval]
  | succ t ih =>
    rw [Fin.sum_univ_succ]
    cases hc : c 0 <;> simp only [affineBit, hc, Bool.false_eq_true, ↓reduceIte]
    · rw [ih]
      simp [boolBit, Fin.tail]
    · rw [Program.xorInput_eval, boolBit_xor, ih]
      simp only [boolBit, ↓reduceIte, one_mul, Fin.tail]
      ring

def bundle {v : ℕ} : (m : ℕ) → (Fin m → Program v 1) → Program v m
  | 0, _ => Program.pure Fin.elim0
  | m + 1, P => ((P 0).parallel (bundle m (Fin.tail P))).outputCast (by omega)

theorem bundle_gates {v : ℕ} (m : ℕ) (P : Fin m → Program v 1) :
    (bundle m P).gates = ∑ i, (P i).gates := by
  induction m with
  | zero => simp [bundle, Program.pure]
  | succ m ih => simp [bundle, Program.outputCast, Program.parallel, ih, Fin.sum_univ_succ, Fin.tail]

theorem bundle_eval {v : ℕ} (m : ℕ) (P : Fin m → Program v 1) (a : BitModels v) :
    (bundle m P).eval a = fun i => (P i).eval a 0 := by
  induction m with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
    funext i
    change ((P 0).parallel (bundle m (Fin.tail P))).eval a (Fin.cast _ i) = _
    rw [Program.parallel_eval, ih]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · have hj : Fin.cast (show 1 + m = m + 1 by omega).symm j.succ = Fin.natAdd 1 j := by
        apply Fin.ext; simp; omega
      rw [hj, Fin.append_right]
      rfl

def localAffine {m t : ℕ} (s : CodeHash.Seed m t) : Program (m * t) m :=
  bundle m (fun i => affineBit t (fun j => Binary.bitBool ((s i).1 j))
    (Binary.bitBool (s i).2) (fun j => finProdFinEquiv (i, j)))

theorem localAffine_gates {m t : ℕ} (s : CodeHash.Seed m t) :
    (localAffine s).gates ≤ m * (t + 1) := by
  rw [localAffine, bundle_gates]
  calc
    _ ≤ ∑ _ : Fin m, (t + 1) := Finset.sum_le_sum (fun i _ => affineBit_gates _ _ _ _)
    _ = _ := by simp

theorem localAffine_correct {m t : ℕ} (s : CodeHash.Seed m t) (a : BitModels (m * t)) (i : Fin m) :
    boolBit ((localAffine s).eval a i) =
      CodeHash.affine (fun j => boolBit (a (finProdFinEquiv (i, j)))) (s i) := by
  rw [localAffine, bundle_eval, affineBit_correct]
  simp only [BadEncoding.boolBit_bitBool]
  rfl

end QecReliability.SharedCircuit
