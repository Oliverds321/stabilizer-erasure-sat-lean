import QecReliability.WalkCodingBridge

/-! One shared zero wire serves both kinds of padding. -/
namespace QecReliability.UniformAdapter
open CodeHash SharedCircuit ExpanderWalk

/-- Executable input dimension transport; proof erasure adds no circuit gates. -/
def inputCast {n n' k : ℕ} (P : Program n k) (h : n = n') : Program n' k := by
  subst n'
  exact P

@[simp] theorem inputCast_gates {n n' k : ℕ} (P : Program n k) (h : n = n') :
    (inputCast P h).gates = P.gates := by cases h; rfl

theorem inputCast_eval {n n' k : ℕ} (P : Program n k) (h : n = n') (a : BitModels n') :
    (inputCast P h).eval a = P.eval (fun i => a (Fin.cast h i)) := by cases h; rfl

/-- Only the result dimension is transported; the actual DAG is retained. -/
theorem outputCast_eval {n k k' : ℕ} (P : Program n k) (h : k = k') (a : BitModels n) :
    (P.outputCast h).eval a = fun i => P.eval a (Fin.cast h.symm i) := rfl

def padBits {q : ℕ} (a : ℕ) (x : BitModels q) : BitModels a :=
  fun i => if hi : i.val < q then x ⟨i.val, hi⟩ else false

def zeroInput (q a : ℕ) : Fin a → Fin (q+1) :=
  fun i => if hi : i.val < q then Fin.castSucc ⟨i.val, hi⟩ else Fin.last q

theorem zeroInput_run {q a : ℕ} (x : BitModels q) :
    (Program.constant q false).circuit.run x ∘ zeroInput q a = padBits a x := by
  funext i
  by_cases hi : i.val < q
  · simp only [Function.comp_apply, zeroInput, padBits, dif_pos hi]
    exact Circuit.snoc_old Circuit.nil (.constGate false) x ⟨i.val, hi⟩
  · simp only [Function.comp_apply, zeroInput, padBits, dif_neg hi]
    exact Circuit.snoc_output Circuit.nil (.constGate false) x

/-- Preserve the last primary input as every newly appended zero output.
This performs no computation and adds no gates. -/
def keepZeroOutputs {q N : ℕ} (P : Program (q+1) N) (z : ℕ) : Program (q+1) (N+z) where
  gates := P.gates
  circuit := P.circuit
  output := Fin.append P.output (fun _ => Fin.castAdd P.gates (Fin.last q))

theorem keepZeroOutputs_eval {q N : ℕ} (P : Program (q+1) N) (z : ℕ)
    (x : BitModels (q+1)) :
    (keepZeroOutputs P z).eval x = Fin.append (P.eval x) (fun _ => x (Fin.last q)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [keepZeroOutputs, Program.eval]
  · simp only [keepZeroOutputs, Program.eval, Fin.append_right]
    exact Circuit.run_primary P.circuit x (Fin.last q)

/-- Input padding and output padding share exactly ONE newly created false gate. -/
def padInputsAndAppend {a N : ℕ} (P : Program a N) (q z : ℕ) : Program q (N+z) :=
  (Program.constant q false).follow
    (keepZeroOutputs (P.rewire (zeroInput q a)) z)

@[simp] theorem padInputsAndAppend_gates {a N : ℕ} (P : Program a N) (q z : ℕ) :
    (padInputsAndAppend P q z).gates = 1 + P.gates := rfl

theorem padInputsAndAppend_eval {a N : ℕ} (P : Program a N) (q z : ℕ)
    (x : BitModels q) :
    (padInputsAndAppend P q z).eval x = Fin.append (P.eval (padBits a x)) (fun _ => false) := by
  rw [padInputsAndAppend, Program.follow_eval, keepZeroOutputs_eval, Program.rewire_eval,
    zeroInput_run]
  congr 1
  funext i
  exact Circuit.snoc_output Circuit.nil (.constGate false) x

theorem bitsVector_padBits {q a : ℕ} (hqa : q ≤ a) (x : BitModels q) :
    bitsVector (padBits a x) = pad hqa (bitsVector x) := by
  funext i
  by_cases hi : i.val < q <;> simp [bitsVector, padBits, pad, hi, boolBit]

noncomputable def paddedEncoder {q a N : ℕ} (E : Word a →ₗ[F] Word N)
    (hqa : q ≤ a) (z : ℕ) : Word q →ₗ[F] Word (N+z) :=
  appendZeros (E.comp (pad hqa)) z

theorem paddedEncoder_correct {q a N : ℕ} (P : Program a N)
    (E : Word a →ₗ[F] Word N)
    (hP : ∀ x i, boolBit (P.eval x i) = E (bitsVector x) i)
    (hqa : q ≤ a) (z : ℕ) (x : BitModels q) (i : Fin (N+z)) :
    boolBit ((padInputsAndAppend P q z).eval x i) = paddedEncoder E hqa z (bitsVector x) i := by
  rw [padInputsAndAppend_eval]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    rw [hP, bitsVector_padBits hqa]
    simp [paddedEncoder, appendZeros]
  · simp [paddedEncoder, appendZeros, Fin.append_right, boolBit]

theorem paddedEncoder_distance {q a N : ℕ} (E : Word a →ₗ[F] Word N)
    {α : ℝ} (hα : 0 ≤ α)
    (hE : ∀ x, x ≠ 0 → α*N ≤ (weight (E x) : ℝ))
    (hqa : q ≤ a) (z : ℕ) (hz : z ≤ N) (x : Word q) (hx : x ≠ 0) :
    (α/2)*(N+z) ≤ (weight (paddedEncoder E hqa z x) : ℝ) := by
  apply appendZeros_distance (E.comp (pad hqa)) hα hz _ x hx
  intro y hy
  apply hE
  intro he
  apply hy
  exact pad_injective hqa (he.trans (pad hqa).map_zero.symm)

/-- Semantic output transport to an arbitrary containing graph order. -/
noncomputable def outputCastLinear {q N m : ℕ} (E : Word q →ₗ[F] Word N)
    (h : N = m) : Word q →ₗ[F] Word m := by
  subst m
  exact E

theorem outputCastLinear_apply {q N m : ℕ} (E : Word q →ₗ[F] Word N)
    (h : N = m) (x : Word q) (i : Fin m) :
    outputCastLinear E h x i = E x (Fin.cast h.symm i) := by cases h; rfl

theorem outputCastLinear_weight {q N m : ℕ} (E : Word q →ₗ[F] Word N)
    (h : N = m) (x : Word q) : weight (outputCastLinear E h x) = weight (E x) := by
  cases h
  rfl

def padInputsAndOutputs {a N : ℕ} (P : Program a N) (q m : ℕ) (hNm : N ≤ m) : Program q m :=
  (padInputsAndAppend P q (m-N)).outputCast (Nat.add_sub_of_le hNm)

@[simp] theorem padInputsAndOutputs_gates {a N : ℕ} (P : Program a N)
    (q m : ℕ) (hNm : N ≤ m) :
    (padInputsAndOutputs P q m hNm).gates = 1 + P.gates := rfl

noncomputable def padEncoderTo {q a N m : ℕ} (E : Word a →ₗ[F] Word N)
    (hqa : q ≤ a) (hNm : N ≤ m) : Word q →ₗ[F] Word m :=
  outputCastLinear (paddedEncoder E hqa (m-N)) (Nat.add_sub_of_le hNm)

theorem padEncoderTo_correct {q a N m : ℕ} (P : Program a N)
    (E : Word a →ₗ[F] Word N)
    (hP : ∀ x i, boolBit (P.eval x i) = E (bitsVector x) i)
    (hqa : q ≤ a) (hNm : N ≤ m) (x : BitModels q) (i : Fin m) :
    boolBit ((padInputsAndOutputs P q m hNm).eval x i) = padEncoderTo E hqa hNm (bitsVector x) i := by
  change boolBit ((padInputsAndAppend P q (m-N)).eval x
    (Fin.cast (Nat.add_sub_of_le hNm).symm i)) = _
  rw [paddedEncoder_correct P E hP hqa]
  exact (outputCastLinear_apply _ _ _ _).symm

theorem padEncoderTo_distance {q a N m : ℕ} (E : Word a →ₗ[F] Word N)
    {α : ℝ} (hα : 0 ≤ α)
    (hE : ∀ x, x ≠ 0 → α*N ≤ (weight (E x) : ℝ))
    (hqa : q ≤ a) (hNm : N ≤ m) (hm : m ≤ 2*N) (x : Word q) (hx : x ≠ 0) :
    (α/2)*m ≤ (weight (padEncoderTo E hqa hNm x) : ℝ) := by
  have hh := paddedEncoder_distance E hα hE hqa (m-N) (by omega) x hx
  unfold padEncoderTo
  rw [outputCastLinear_weight]
  have he : (m:ℝ) = (N:ℝ) + ((m-N:ℕ):ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le hNm).symm
  simpa only [Nat.cast_add, he] using hh

end QecReliability.UniformAdapter
