import Trans.HashCallees.EncoderCorrX

/-!
# Trans.HashCallees.EncoderCorrPow: the rotation of a port power on values

For a degree-16 port graph `G` whose rotation is `lazyRotP s` on values, the rotation of
`G.power K` is `powRotP s K` on values (`power_rotation`): follow the `K` base-16 digits of the
port, collecting the reverse ports in reverse order (Horner). Instances: the powered lazy MGG
square graphs used by the amplifiers (`ampGraph_rotation`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.HashCallees
open QecReliability.ExpanderWalk QecReliability.ExpanderWalk.PortGraph
open scoped BigOperators

/-- Value of a port word (base 16, digit `j` of weight `16 ^ j`). -/
def wordVal {K : ℕ} (a : Fin K → Fin 16) : ℕ := (finFunctionFinEquiv a : Fin (16 ^ K)).val

theorem wordVal_cons {K : ℕ} (y : Fin 16) (b : Fin K → Fin 16) :
    wordVal (Fin.cons y b : Fin (K + 1) → Fin 16) = y.val + 16 * wordVal b := by
  simp only [wordVal, finFunctionFinEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem wordVal_eq_head_tail {K : ℕ} (a : Fin (K + 1) → Fin 16) :
    wordVal a = (a 0).val + 16 * wordVal (Fin.tail a) := by
  rw [← wordVal_cons, cons_head_tail]

theorem wordVal_snoc {K : ℕ} (b : Fin K → Fin 16) (x : Fin 16) :
    wordVal (snocWord b x) = wordVal b + x.val * 16 ^ K := by
  induction K with
  | zero =>
    simp only [wordVal, snocWord]
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    simp
  | succ K ih =>
    simp only [snocWord]
    rw [wordVal_cons, ih, wordVal_eq_head_tail b, pow_succ]
    ring

/-- The plain step ignores the list element. -/
def powStep0 (st : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := powStep st 0

theorem foldl_powStep (l : List ℕ) (st : ℕ × ℕ × ℕ × ℕ) :
    l.foldl powStep st = powStep0^[l.length] st := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, List.length_cons, Function.iterate_succ_apply]; exact ih _

variable {m : ℕ}

/-- The walk on values: `K` steps of `powStep` follow `reverseWalk`. -/
theorem powStep_iterate (G : PortGraph m 16) (s : ℕ)
    (hG : ∀ v i, (G.rotation (v, i)).1.val = (lazyRotP s v.val i.val).1 ∧
      (G.rotation (v, i)).2.val = (lazyRotP s v.val i.val).2) :
    ∀ (K : ℕ) (v : Fin m) (a : Fin K → Fin 16) (w acc : ℕ),
      (∀ j : Fin K, w / 16 ^ j.val % 16 = (a j).val) →
      powStep0^[K] (s, v.val, w, acc) =
        (s, (G.reverseWalk K (v, a)).1.val, w / 16 ^ K,
          acc * 16 ^ K + wordVal (G.reverseWalk K (v, a)).2) := by
  intro K
  induction K with
  | zero =>
    intro v a w acc _
    simp [wordVal, finFunctionFinEquiv_apply, reverseWalk]
  | succ K ih =>
    intro v a w acc hw
    have h0 : w % 16 = (a 0).val := by simpa using hw 0
    have hq := hG v (a 0)
    rw [Function.iterate_succ_apply]
    have e : powStep0 (s, v.val, w, acc) =
        (s, (G.rotation (v, a 0)).1.val, w / 16, acc * 16 + (G.rotation (v, a 0)).2.val) := by
      simp only [powStep0, powStep, h0, hq.1, hq.2]
    rw [e]
    have hw' : ∀ j : Fin K, w / 16 / 16 ^ j.val % 16 = (Fin.tail a j).val := by
      intro j
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      exact hw j.succ
    rw [ih _ (Fin.tail a) (w / 16) _ hw']
    simp only [reverseWalk, Prod.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · rw [Nat.div_div_eq_div_mul, ← pow_succ']
    · rw [wordVal_snoc, pow_succ]
      ring

/-- **The rotation of a port power on values.** -/
theorem power_rotation (G : PortGraph m 16) (s : ℕ)
    (hG : ∀ v i, (G.rotation (v, i)).1.val = (lazyRotP s v.val i.val).1 ∧
      (G.rotation (v, i)).2.val = (lazyRotP s v.val i.val).2)
    (K : ℕ) (v : Fin m) (i : Fin (16 ^ K)) :
    ((G.power K).rotation (v, i)).1.val = (powRotP s K v.val i.val).1 ∧
    ((G.power K).rotation (v, i)).2.val = (powRotP s K v.val i.val).2 := by
  have h := powStep_iterate G s hG K v (portWordEquiv 16 K i) i.val 0
    (fun j => (finFunctionFinEquiv_symm_apply_val i j).symm)
  simp only [powRotP, foldl_powStep, List.length_range, h, zero_mul, zero_add]
  refine ⟨rfl, ?_⟩
  change (finFunctionFinEquiv (G.reverseWalk K (v, portWordEquiv 16 K i)).2).val = _
  rfl

/-! ## The amplifier graphs -/

theorem castGraphDegree_rotation {n d e : ℕ} (h : d = e) (G : PortGraph n d) (v : Fin n)
    (i : Fin e) :
    ((ExpanderWalk.SelectedSparseAmplifier.castGraphDegree h G).rotation (v, i)).1.val =
      (G.rotation (v, Fin.cast h.symm i)).1.val ∧
    ((ExpanderWalk.SelectedSparseAmplifier.castGraphDegree h G).rotation (v, i)).2.val =
      (G.rotation (v, Fin.cast h.symm i)).2.val := by
  subst h; exact ⟨rfl, rfl⟩

set_option maxRecDepth 8000 in
/-- **The rotation of the amplifier graph on values**: the `384`-step power of the lazy MGG
graph of side `squareSide (T / D)`, degree cast to `D = 16 ^ 384`. (The elaborator unfolds the
power `16 ^ 384` while matching the degree cast; this is a cheap 384-step unfolding.) -/
theorem ampGraph_rotation (D : ℕ) (hD : D = 16 ^ 384) (T : ℕ) (hdiv : D ∣ T) (hlarge : 8 * D ≤ T)
    (v : Fin (QuantumExpander.squareSide (T / D) * QuantumExpander.squareSide (T / D)))
    (i : Fin D) :
    ((SelectedSparseAmplifier.graph D hD T hdiv hlarge).rotation (v, i)).1.val =
      (powRotP (QuantumExpander.squareSide (T / D)) 384 v.val i.val).1 ∧
    ((SelectedSparseAmplifier.graph D hD T hdiv hlarge).rotation (v, i)).2.val =
      (powRotP (QuantumExpander.squareSide (T / D)) 384 v.val i.val).2 := by
  have hL : 8 ≤ T / D := SelectedSparseAmplifier.quotient_large
      (hD.symm ▸ SelectedSparseAmplifier.fixed_degree_pos) hdiv hlarge
  have hc := castGraphDegree_rotation hD.symm (((squarePortGraph (T / D) hL).power 384)) v i
  have hp := power_rotation (squarePortGraph (T / D) hL) (QuantumExpander.squareSide (T / D))
    (lazyMGG_rotation _ _) 384 v (Fin.cast hD i)
  exact ⟨hc.1.trans hp.1, hc.2.trans hp.2⟩

end QecReliability.Trans.HashCallees
