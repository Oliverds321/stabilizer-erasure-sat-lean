import Trans.HashCallees.EncoderCorrPow

/-!
# Trans.HashCallees.EncoderCorr: the encoder family on plain data

* `encX_eightBase`, `encX_baseProgram`: the base program is `baseP D code`;
* `encX_amplifierProgram` (generic graph), `encX_firstProgram`, `encX_secondProgram`: the
  amplifiers are `ampP D 384 code T` (`T = 2 mw`, `4 mw`);
* `encX_encoder`: the recursive encoder is `encP (D, 384, code)`;
* **`encProg_dataProgram`**: `encProg ((data hD hd A).program ell) = encP (D, 384, A.code.val) (ell+1)`.

`D`, `t` and the certificate stay symbolic; `code = A.code.val` is never evaluated.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace QecReliability.Trans.HashCallees
open QecReliability.SharedCircuit QecReliability.Trans.Query QecReliability.Trans.Query.Plain
open QecReliability.Trans.Hash QecReliability.ExpanderWalk
open FiniteXorRowEmitter FixedLocalEmitter SerializedDyadicEncoder

/-! ## Helpers -/

theorem addCases_val {m n : ℕ} {α : Type*} (f : Fin m → α) (g : Fin n → α) (x : Fin (m + n)) :
    Fin.addCases (motive := fun _ => α) f g x =
      if h : x.val < m then f ⟨x.val, h⟩ else g ⟨x.val - m, by omega⟩ := by
  by_cases h : x.val < m
  · obtain ⟨j, rfl⟩ : ∃ j : Fin m, x = Fin.castAdd n j := ⟨⟨x.val, h⟩, Fin.ext rfl⟩
    rw [Fin.addCases_left, dif_pos h]; rfl
  · obtain ⟨j, rfl⟩ : ∃ j : Fin n, x = Fin.natAdd m j :=
      ⟨⟨x.val - m, by omega⟩, Fin.ext (by simp; omega)⟩
    rw [Fin.addCases_right, dif_neg h]
    congr 1; ext; simp

theorem ofFn_val_eq_range (n : ℕ) : List.ofFn (fun i : Fin n => i.val) = List.range n := by
  apply List.ext_getElem <;> simp

theorem val_of_tab {n m : ℕ} (f : Fin n → Fin m) (l : List ℕ) (h : tab f = l) (x : Fin n) :
    (f x).val = l.getD x.val 0 := by
  rw [← h, tab_getD f x.val x.isLt]

theorem ceilSquare_eq_squareSide (L : ℕ) (hL : 0 < L) :
    UniformAdapter.ceilSquare L = QuantumExpander.squareSide L := by
  obtain ⟨h1, h2, h3⟩ := UniformAdapter.ceilSquare_spec L hL
  have c1 := QuantumExpander.squareSide_covers L hL
  have c2 := QuantumExpander.squareSide_predecessor_sq_lt L hL
  have hs : 1 ≤ QuantumExpander.squareSide L := by unfold QuantumExpander.squareSide; omega
  rcases lt_trichotomy (UniformAdapter.ceilSquare L) (QuantumExpander.squareSide L) with h | h | h
  · exfalso
    have hle : UniformAdapter.ceilSquare L ≤ QuantumExpander.squareSide L - 1 := by omega
    have := Nat.mul_le_mul hle hle
    rw [pow_two] at c2
    omega
  · exact h
  · exfalso
    have := h3 _ hs h
    omega

/-! ## Base program -/

theorem encX_eightBase {k h : ℕ} (coeff : Coefficients k h) (zeros : ℕ) (cf : ℕ → ℕ → Bool)
    (hcf : ∀ (r : Fin h) (j : Fin k), coeff r j = cf r.val j.val) :
    encX (eightBaseProgram coeff zeros) =
      ((emitP (8 * k) (8 * h) k (fun i j => if cf (i % h) j then j + k * (i / h) else 8 * k)).1,
        List.range (8 * k) ++ (List.range (8 * h)).map (fun i => 8 * k + (i + 1) * k) ++
          List.replicate zeros (8 * k)) := by
  have hP := encX_emitKeepZero (8 * k) (8 * h) k
    (fun out col => if coeff (finProdFinEquiv.symm out).2 col then
      eightReferences k (finProdFinEquiv.symm out).1 col else Fin.last (8 * k))
    (fun i j => if cf (i % h) j then j + k * (i / h) else 8 * k)
    (fun i j => by
      simp only [finProdFinEquiv_symm_apply, hcf, Fin.coe_modNat]
      split_ifs <;> simp [eightReferences, finProdFinEquiv_apply_val, Fin.coe_divNat])
  have hout := congrArg Prod.snd hP
  simp only [encX_snd, emitP] at hout
  simp only [eightBaseProgram, emitBlocksKeepZero, encX, encProg, XorProgram.toProgram]
  have hP1 := congrArg Prod.fst hP
  simp only [encX, encProg, XorProgram.toProgram] at hP1
  refine Prod.ext hP1 ?_
  · simp only
    rw [ofFn_add' (m := 8 * k), ofFn_add' (m := 8 * h) (n := zeros)]
    simp only [Fin.addCases_left, Fin.addCases_right, Fin.coe_castAdd, List.append_assoc]
    rw [ofFn_val_eq_range]
    congr 1
    congr 1
    · apply List.ext_getElem
      · simp
      · intro i h1 h2
        have hi : i < 8 * h := by simpa using h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        rw [val_of_tab _ _ hout]
        simp [List.getD_eq_getElem?_getD, Fin.coe_natAdd, Nat.add_comm 1 i, hi]
    · rw [List.ofFn_const, val_of_tab _ _ hout]
      simp

theorem encX_baseProgram {D t : ℕ} (hD4 : 4 ∣ D) (hd : D = 256 * t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512 * t) (64 * t) t) :
    encX (baseProgram hD4 hd A) = baseP D A.code.val := by
  have hk : 512 * t = D + D := by omega
  simp only [baseProgram, encX_outputCast, encX_inputCast]
  rw [encX_eightBase (degreeCoefficients hd A) (46 * D) (coeffP A.code.val (D + D))
    (fun r j => by
      simp only [degreeCoefficients, castCoefficients, FiniteLocalSelectorCandidate.matrixEntry,
        coeffP, Fin.coe_cast, hk])]
  rfl

/-! ## Amplifiers -/

theorem encX_amplifierProgram {V d T : ℕ} (G : PortGraph V d) (hIn : T ≤ V * d)
    (hOut : V * (d / 4) ≤ T / 2) (coeff : Coefficients (d + d) (d / 4)) (cf : ℕ → ℕ → Bool)
    (hcf : ∀ (r : Fin (d / 4)) (j : Fin (d + d)), coeff r j = cf r.val j.val)
    (rot : ℕ → ℕ → ℕ × ℕ)
    (hrot : ∀ v i, (G.rotation (v, i)).1.val = (rot v.val i.val).1 ∧
      (G.rotation (v, i)).2.val = (rot v.val i.val).2) :
    encX (amplifierProgram G hIn hOut coeff) =
      ((emitP T (V * (d / 4)) (d + d) (fun i j => if cf (i % (d / 4)) j then
          (if j < d then padRef T (j + d * (i / (d / 4)))
            else padRef T ((rot (i / (d / 4)) (j - d)).2 + d * (rot (i / (d / 4)) (j - d)).1))
          else T)).1,
        (List.range (T / 2)).map (fun j => if j < V * (d / 4) then T + (j + 1) * (d + d) else T)) := by
  have hE := encX_emitKeepZero T (V * (d / 4)) (d + d)
    (fun out col => if coeff (finProdFinEquiv.symm out).2 col then
      portReferences G (finProdFinEquiv.symm out).1 col else Fin.last T)
    (fun i j => if cf (i % (d / 4)) j then
          (if j < d then padRef T (j + d * (i / (d / 4)))
            else padRef T ((rot (i / (d / 4)) (j - d)).2 + d * (rot (i / (d / 4)) (j - d)).1))
          else T)
    (fun i j => by
      simp only [finProdFinEquiv_symm_apply, hcf, Fin.coe_modNat]
      split_ifs with h1 h2
      · simp only [portReferences, addCases_val, dif_pos h2, paddedReference, padRef,
          finProdFinEquiv_apply_val, Fin.coe_divNat]
        split_ifs <;> simp
      · simp only [portReferences, addCases_val, dif_neg h2, paddedReference, padRef,
          finProdFinEquiv_apply_val, Fin.coe_divNat, (hrot _ _).1, (hrot _ _).2]
        split_ifs <;> simp
      · simp)
  have hout := congrArg Prod.snd hE
  simp only [encX_snd, emitP] at hout
  simp only [amplifierProgram, amplifierKeepZero, emitBlocksKeepZero, encX, encProg,
    XorProgram.toProgram]
  have hE1 := congrArg Prod.fst hE
  simp only [encX, encProg, XorProgram.toProgram] at hE1
  refine Prod.ext hE1 ?_
  · simp only
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      split_ifs with hj
      · rw [val_of_tab _ _ hout]
        simp [List.getD_eq_getElem?_getD, Fin.coe_natAdd, Nat.add_comm 1 j, hj,
          List.getElem?_range]
      · rw [val_of_tab _ _ hout]
        simp

theorem portRef_eq (D K T s v j : ℕ) :
    (if j < D then padRef T (j + D * v)
      else padRef T ((powRotP s K v (j - D)).2 + D * (powRotP s K v (j - D)).1)) =
      portRef D K T s v j := rfl

theorem encX_sourceAmp {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512 * t) (64 * t) t) (T out : ℕ)
    (hdiv : D ∣ T) (hlarge : 8 * D ≤ T) (hout : T / 2 = out) :
    encX (sourceProgram (FixedWitnessEncoder.paddedSource D hD T out hdiv hlarge hout)
      (degreeCoefficients hd A)) = ampP D 384 A.code.val T := by
  have hk : 512 * t = D + D := by omega
  have hL : 0 < T / D := by
    have := SelectedSparseAmplifier.quotient_large
      (hD.symm ▸ SelectedSparseAmplifier.fixed_degree_pos) hdiv hlarge
    omega
  simp only [sourceProgram, encX_outputCast, FixedWitnessEncoder.paddedSource]
  rw [encX_amplifierProgram _ _ _ _ (coeffP A.code.val (D + D))
    (fun r j => by
      simp only [degreeCoefficients, castCoefficients, FiniteLocalSelectorCandidate.matrixEntry,
        coeffP, Fin.coe_cast, hk])
    (powRotP (QuantumExpander.squareSide (T / D)) 384)
    (fun v i => ampGraph_rotation D hD T hdiv hlarge v i)]
  simp only [ampP, ceilSquare_eq_squareSide _ hL, portRef_eq]
  rfl

theorem encX_firstProgram {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512 * t) (64 * t) t) (ell : ℕ) :
    encX (firstProgram hD hd A ell) = ampP D 384 A.code.val (2 * mwP D ell) := by
  rw [firstProgram, FixedWitnessEncoder.firstSource, encX_sourceAmp, mwP, messageWidth_formula]

theorem encX_secondProgram {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512 * t) (64 * t) t) (ell : ℕ) :
    encX (secondProgram hD hd A ell) = ampP D 384 A.code.val (4 * mwP D ell) := by
  rw [secondProgram, FixedWitnessEncoder.secondSource, encX_sourceAmp, mwP, messageWidth_formula]

/-! ## The recursion -/

theorem encX_encoder {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512 * t) (64 * t) t) (ell : ℕ) :
    encX (encoder (baseProgram (FixedWitnessEncoder.degree_four hD) hd A)
      (firstProgram hD hd A) (secondProgram hD hd A) ell) = encP (D, 384, A.code.val) ell := by
  induction ell with
  | zero => exact encX_baseProgram _ hd A
  | succ ell ih =>
    rw [encoder, encX_outputCast, encX_oneCopy, ih, encX_firstProgram, encX_secondProgram, encP,
      messageWidth_formula, mwP, show 16 * D * 2 ^ (ell + 1) = 2 * (16 * D * 2 ^ ell) by ring]

open FixedLocalEmitter.AllLength in
/-- **The encoder family on plain data**: the program of index `ell` of
`data hD hd A = (concreteDyadicData hD hd A).shift` is `encP (D, 384, A.code.val) (ell + 1)`. -/
theorem encProg_dataProgram {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512 * t) (64 * t) t) (ell : ℕ) :
    encProg ((data hD hd A).program ell) = encP (D, 384, A.code.val) (ell + 1) := by
  change encProg ((concreteDyadicData hD hd A).shiftedProgram ell) = _
  rw [UniformAdapter.DyadicXorData.shiftedProgram, encProg_castProgram]
  change encX (concreteExactEncoder hD hd A (ell + 1)) = _
  rw [concreteExactEncoder, exactEncoder, encX_outputCast, encX_inputCast, encX_encoder]

end QecReliability.Trans.HashCallees
