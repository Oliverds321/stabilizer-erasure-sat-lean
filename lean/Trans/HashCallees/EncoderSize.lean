import Trans.HashCallees.EncoderCorr

/-!
# Trans.HashCallees.EncoderSize: size invariants of the encoder programs

The size facts needed for closed-form cost bounds of the encoder oracle, for the
concrete constants `E = (D, 384, A.code.val)` and the output length `N = 128 D 2^ell`
of `(data hD hd A).program ell = encP E (ell + 1)`:

* `encP_gates_le`: at most `2 D N` gates (`DyadicXorData.gates_le`, linear in `N`);
* `encP_outputs_length`: exactly `N` outputs;
* `encP_wires_lt`: every wire index of every gate and every output is `< N / 4 + gates + 2`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.HashCallees
open QecReliability.SharedCircuit QecReliability.Trans.Query.Plain QecReliability.Trans.Hash
open FiniteLocalSelectorCandidate QecReliability.SharedCircuit.FixedLocalEmitter.AllLength

/-- Every wire of an encoded circuit on `n` inputs with `g` gates is `< n + g + 2`. -/
theorem encCirc_wires_lt {n : ℕ} : ∀ {g : ℕ} (C : Circuit n g), ∀ x ∈ Query.encCirc C,
    x.2.2.1 < n + g + 2 ∧ x.2.2.2 < n + g + 2
  | _, .nil => by simp
  | _, .snoc C gate => by
    intro x hx
    simp only [Query.encCirc_snoc, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · have := encCirc_wires_lt C x hx; omega
    · cases gate with
      | andGate a b => simp only [Query.encGate]; omega
      | xorGate a b => simp only [Query.encGate]; omega
      | notGate a => simp only [Query.encGate]; omega
      | constGate b => simp only [Query.encGate, constGate]; split <;> omega

theorem encProg_wires_lt {n k : ℕ} (P : Program n k) :
    (∀ x ∈ (Query.encProg P).1, x.2.2.1 < n + (Query.encProg P).1.length + 2 ∧
      x.2.2.2 < n + (Query.encProg P).1.length + 2) ∧
    ∀ o ∈ (Query.encProg P).2, o < n + (Query.encProg P).1.length := by
  refine ⟨fun x hx => ?_, fun o ho => ?_⟩
  · simp only [Query.encProg, Query.encCirc_length] at hx ⊢
    exact encCirc_wires_lt P.circuit x hx
  · simp only [Query.encProg, List.mem_ofFn, Query.encCirc_length] at ho ⊢
    obtain ⟨i, rfl⟩ := ho
    exact (P.output i).isLt

theorem data_base {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) : (data hD hd A).base = 128 * D := by
  change 2 * (64 * D) = 128 * D; ring

/-- **Gate count**: linear in the output length `N = 128 D 2^ell`. -/
theorem encP_gates_le {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : ℕ) :
    (encP (D, 384, A.code.val) (ell + 1)).1.length ≤ 2 * D * (128 * D * 2 ^ ell) := by
  rw [← encProg_dataProgram hD hd A ell]
  simp only [Query.encProg, Query.encCirc_length]
  have h := (data hD hd A).gates_le ell
  have e : (data hD hd A).gateConstant * ((data hD hd A).base * 2 ^ ell) =
      2 * D * (128 * D * 2 ^ ell) := by
    rw [data_base hD hd A]; rfl
  exact h.trans (le_of_eq e)

theorem encP_outputs_length {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : ℕ) :
    (encP (D, 384, A.code.val) (ell + 1)).2.length = 128 * D * 2 ^ ell := by
  rw [← encProg_dataProgram hD hd A ell]
  simp only [Query.encProg, List.length_ofFn]
  rw [data_base hD hd A]

/-- **Wire bound**: every wire of every gate and every output is below
`N / 4 + gates + 2` (`N / 4` inputs). -/
theorem encP_wires_lt {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (ell : ℕ) :
    (∀ x ∈ (encP (D, 384, A.code.val) (ell + 1)).1,
      x.2.2.1 < 128 * D * 2 ^ ell / 4 + (encP (D, 384, A.code.val) (ell + 1)).1.length + 2 ∧
      x.2.2.2 < 128 * D * 2 ^ ell / 4 + (encP (D, 384, A.code.val) (ell + 1)).1.length + 2) ∧
    ∀ o ∈ (encP (D, 384, A.code.val) (ell + 1)).2,
      o < 128 * D * 2 ^ ell / 4 + (encP (D, 384, A.code.val) (ell + 1)).1.length := by
  rw [← encProg_dataProgram hD hd A ell]
  have h := encProg_wires_lt ((data hD hd A).program ell)
  have hb := data_base hD hd A
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx => ?_, fun o ho => ?_⟩
  · have := h1 x hx; simp only [hb] at this; exact this
  · have := h2 o ho; simp only [hb] at this; exact this

end QecReliability.Trans.HashCallees
