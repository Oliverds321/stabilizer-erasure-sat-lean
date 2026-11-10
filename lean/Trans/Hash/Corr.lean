import Trans.Hash.CorrParts

/-!
# Trans.Hash.Corr: the hash program is `hashPlain` of its plain data

* `encProg_walkProgram`: for any `WalkCode W` and supplied circuits `K`, the encoded hash
  program `(K.forward e).compiled.implementation.program r s` is assembled from
  `encProg K.binary`, `encProg K.code`, the neighbor map of `W.graph` and `encProg (localAffine s)`;
* `encProg_hashProgram`: for `DyadicXorData.walkCircuits` and a seed given by its bits,
  it equals `hashPlain X.base X.den q (encProg ∘ X.program) (gNbr G) r bits`;
* `encProg_positiveProgram`: the instance used by the algorithm
  (`positiveCircuits hD hd A k`, `q = keySize (k+1) (k+1)`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace QecReliability.Trans.Hash
open QecReliability.SharedCircuit QecReliability.Trans.Query QecReliability.Trans.Query.Plain
open QecReliability.CodeHash QecReliability.ExpanderWalk QecReliability.UniformAdapter

/-- The neighbor map of a port graph on values (`0` off the domain). -/
noncomputable def nbV {m d : ℕ} (Gr : PortGraph m d) (v i : ℕ) : ℕ :=
  if h : v < m ∧ i < d then (Gr.neighbor ⟨v, h.1⟩ ⟨i, h.2⟩).val else 0

theorem nbV_spec {m d : ℕ} (Gr : PortGraph m d) (v : Fin m) (i : Fin d) :
    nbV Gr v.val i.val = (Gr.neighbor v i).val := by
  simp [nbV, v.isLt, i.isLt]

theorem pselect_pselect (P : ProgP) (a b : List ℕ) (h : ∀ j ∈ b, j < a.length) :
    pselect (pselect P a) b = pselect P (b.map (fun i => a.getD i 0)) := by
  simp only [pselect, List.map_map, Prod.mk.injEq, true_and]
  apply List.map_congr_left
  intro j hj
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h j hj)]

theorem tab_lt {n m : ℕ} (f : Fin n → Fin m) : ∀ j ∈ tab f, j < m := by
  intro j hj
  simp only [tab, List.mem_ofFn] at hj
  obtain ⟨i, rfl⟩ := hj
  exact (f i).isLt

theorem tab_castLE {a b : ℕ} (h : a ≤ b) : tab (Fin.castLE h : Fin a → Fin b) = List.range a := by
  apply List.ext_getElem <;> simp [tab]

theorem encoder_index {m d k L : ℕ} (Gr : PortGraph m d) (hM : 0 < m * d ^ k) :
    (tab (repeatWires (m * d ^ k) L (k + 1) hM)).map (fun i =>
        (tab (fun i : Fin ((m * d ^ k) * (k + 1)) =>
          let ij := finProdFinEquiv.symm i
          let walk := walkLabel m d k ij.1
          Gr.visits walk.1 walk.2 ij.2)).getD i 0) =
      (List.range (L * (k + 1))).map (encIndex (nbV Gr) d (d ^ k) (m * d ^ k) (k + 1)) := by
  apply List.ext_getElem
  · simp
  · intro x h1 h2
    simp only [List.length_map, tab_length] at h1
    simp only [List.getElem_map, List.getElem_range]
    have hx : (tab (repeatWires (m * d ^ k) L (k + 1) hM))[x]'(by simpa using h1) =
        (repeatWires (m * d ^ k) L (k + 1) hM ⟨x, h1⟩).val := by simp [tab]
    rw [hx]
    have hy : (repeatWires (m * d ^ k) L (k + 1) hM ⟨x, h1⟩).val =
        x % (k + 1) + (k + 1) * (x / (k + 1) % (m * d ^ k)) := by
      simp [repeatWires, cyclicRepeat, finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat]
    have hlt := (repeatWires (m * d ^ k) L (k + 1) hM ⟨x, h1⟩).isLt
    rw [tab_getD _ _ hlt]
    simp only [Fin.eta]
    rw [visits_val Gr (nbV Gr) (nbV_spec Gr) k _ _
      ((repeatWires (m * d ^ k) L (k + 1) hM ⟨x, h1⟩).val / (k + 1) % d ^ k)]
    · simp only [encIndex, ← hy, walkLabel, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
        Equiv.prodCongr_apply, Prod.map, finProdFinEquiv_symm_apply, Fin.coe_divNat,
        Fin.coe_modNat, Equiv.refl_symm, Equiv.refl_apply]
    · intro j
      simp [walkLabel, finFunctionFinEquiv_symm_apply_val, Fin.coe_modNat,
        finProdFinEquiv_symm_apply, Fin.coe_divNat]

/-- The hash program of any walk code, on plain data. -/
theorem encProg_walkProgram {q : ℕ} (W : WalkCode q) (K : W.Circuits) {A : Type*}
    (e : A ≃ BitModels q) (r : Fin (q + 1)) (s : Seed W.L (W.steps + 1)) :
    encProg ((K.forward e).compiled.implementation.program r s) =
      pselect (pcompose q (pcompose q
        (pselect (encProg K.binary) ((List.range (W.L * (W.steps + 1))).map
          (encIndex (nbV W.graph) W.d (W.d ^ W.steps) (W.m * W.d ^ W.steps) (W.steps + 1))))
        (encProg (localAffine s)))
        (pselect (transP W.c (encProg K.code)) (List.range q))) (List.range r.val) := by
  simp only [Implementation.program, Implementation.full, CodingCircuits.implementation,
    ForwardCodingCircuits.compiled, WalkCode.Circuits.forward, PortGraph.symbolProgram]
  rw [encProg_select, encProg_compose, encProg_compose, encProg_select, encProg_select,
    encProg_select, encProg_transposed, tab_castLE, tab_castLE,
    pselect_pselect _ _ _ (fun j hj => by simpa using tab_lt _ j hj)]
  congr 4
  exact encoder_index W.graph _

theorem gNbr_eq (G : MGGInput) (s : ℕ) (hs : 3 ≤ s) : gNbr G s = nbV (G.graph s hs) := by
  funext v i
  simp only [gNbr, nbV]
  by_cases h : v < s * s ∧ i < 16
  · rw [dif_pos ⟨hs, h⟩, dif_pos h]
  · rw [dif_neg (fun h' => h h'.2), dif_neg h]

theorem encProg_castProgram {a b a' b' : ℕ} (P : Program a b) (ha : a = a') (hb : b = b') :
    encProg (castProgram P ha hb) = encProg P := by
  cases ha; cases hb; rfl

/-- **The hash program of `DyadicXorData.walkCircuits` on plain data.** -/
theorem encProg_hashProgram (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ)
    {A : Type*} (e : A ≃ BitModels q) (r : Fin (q + 1)) (bits : List Bool)
    (hbits : bits.length = seedBits (X.walkCode hb G q).L ((X.walkCode hb G q).steps + 1)) :
    encProg (((X.walkCircuits hb G q).forward e).compiled.implementation.program r
        (seedOfBits (X.walkCode hb G q).L ((X.walkCode hb G q).steps + 1) bits)) =
      hashPlain X.base X.den q (fun ell => encProg (X.program ell)) (gNbr G) r.val bits := by
  rw [encProg_walkProgram, encProg_localAffine _ _ _ (by rw [hbits, seedBits]; ring_nf; omega)]
  have hL : (X.walkCode hb G q).L = (params X.base X.den q).L :=
    (X.walkCode_length hb G q).trans rfl
  simp only [hashPlain, DyadicXorData.walkCircuits, DyadicXorData.binaryProgram,
    encProg_padInputsAndOutputs, DyadicXorData.selectedProgram, encProg_castProgram, hL]
  rw [show nbV (X.walkCode hb G q).graph = gNbr G (params X.base X.den q).s from
    (gNbr_eq G _ (X.side_ge_three hb q)).symm]
  have hc : (X.walkCode hb G q).c = (X.walkCode hb G q).L / 4 := rfl
  erw [encProg_padInputsAndOutputs]
  rw [hc, hL]
  rfl

end QecReliability.Trans.Hash
