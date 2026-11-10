import Mathlib.Algebra.BigOperators.Fin
import QecReliability.CenteredPowerCandidate

/-!




The graph-data definitions below are outside a noncomputable section and use
only explicit finite-word operations and finFunctionFinEquiv, the same radix
equivalence already used by walkLabel.
-/

namespace QecReliability.ExpanderWalk
open scoped BigOperators
namespace PortGraph

variable {m d : ℕ} (G : PortGraph m d)

/-- Append one letter; recursion avoids dependence on a separate snoc API. -/
def snocWord {α : Type*} : {k : ℕ} → (Fin k → α) → α → (Fin (k + 1) → α)
  | 0, _, x => fun _ => x
  | _ + 1, a, x => Fin.cons (a 0) (snocWord (Fin.tail a) x)

theorem snocWord_cons {α : Type*} {k : ℕ} (x y : α) (a : Fin k → α) :
    snocWord (Fin.cons x a) y = Fin.cons x (snocWord a y) := by
  simp only [snocWord, Fin.cons_zero, Fin.tail_cons]

theorem cons_head_tail {α : Type*} {k : ℕ} (a : Fin (k + 1) → α) :
    Fin.cons (a 0) (Fin.tail a) = a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Follow all ports, return the terminal vertex and reverse-port word in
reverse chronological order. The final snoc, not cons, is essential. -/
def reverseWalk (G : PortGraph m d) : (k : ℕ) →
    (Fin m × (Fin k → Fin d)) → (Fin m × (Fin k → Fin d))
  | 0, p => p
  | k + 1, p =>
    let q := G.rotation (p.1, p.2 0)
    let r := G.reverseWalk k (q.1, Fin.tail p.2)
    (r.1, snocWord r.2 q.2)

theorem reverseWalk_snoc (k : ℕ) (v : Fin m) (a : Fin k → Fin d) (i : Fin d) :
    G.reverseWalk (k + 1) (v, snocWord a i) =
      let p := G.reverseWalk k (v, a)
      let q := G.rotation (p.1, i)
      (q.1, Fin.cons q.2 p.2) := by
  induction k generalizing v with
  | zero =>
    apply Prod.ext
    · rfl
    · funext j
      refine Fin.cases ?_ (fun z => Fin.elim0 z) j
      rfl
  | succ k ih =>
    let q := G.rotation (v, a 0)
    let p := G.reverseWalk k (q.1, Fin.tail a)
    change
      ((G.reverseWalk (k + 1) (q.1, snocWord (Fin.tail a) i)).1,
        snocWord (G.reverseWalk (k + 1) (q.1, snocWord (Fin.tail a) i)).2 q.2) =
      ((G.rotation (p.1, i)).1,
        Fin.cons (G.rotation (p.1, i)).2 (snocWord p.2 q.2))
    rw [ih]
    simp only [snocWord_cons]
    rfl

theorem reverseWalk_involutive (k : ℕ) : Function.Involutive (G.reverseWalk k) := by
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    rintro ⟨v, a⟩
    change G.reverseWalk (k + 1)
      ((G.reverseWalk k ((G.rotation (v, a 0)).1, Fin.tail a)).1,
        snocWord (G.reverseWalk k ((G.rotation (v, a 0)).1, Fin.tail a)).2
          (G.rotation (v, a 0)).2) = (v, a)
    rw [G.reverseWalk_snoc]
    simp only [Prod.mk.eta]
    rw [ih ((G.rotation (v, a 0)).1, Fin.tail a)]
    simp only [Prod.mk.eta, G.reverse_reverse (v, a 0), cons_head_tail]

def wordRotation (k : ℕ) :
    (Fin m × (Fin k → Fin d)) ≃ (Fin m × (Fin k → Fin d)) where
  toFun := G.reverseWalk k
  invFun := G.reverseWalk k
  left_inv := G.reverseWalk_involutive k
  right_inv := G.reverseWalk_involutive k

/-- Explicit mixed-radix codec; no Fintype.equivFin or choice of a labeling. -/
def portWordEquiv (d k : ℕ) : Fin (d ^ k) ≃ (Fin k → Fin d) :=
  finFunctionFinEquiv.symm

def powerCodec (k : ℕ) :
    (Fin m × Fin (d ^ k)) ≃ (Fin m × (Fin k → Fin d)) :=
  Equiv.prodCongr (Equiv.refl (Fin m)) (portWordEquiv d k)

def powerRotation (k : ℕ) : (Fin m × Fin (d ^ k)) ≃ (Fin m × Fin (d ^ k)) :=
  ((powerCodec (m := m) (d := d) k).trans (G.wordRotation k)).trans
    (powerCodec (m := m) (d := d) k).symm

theorem powerRotation_involutive (k : ℕ) : Function.Involutive (G.powerRotation k) := by
  intro p
  change (powerCodec (m := m) (d := d) k).symm
    (G.reverseWalk k ((powerCodec (m := m) (d := d) k)
      ((powerCodec (m := m) (d := d) k).symm
        (G.reverseWalk k ((powerCodec (m := m) (d := d) k) p))))) = p
  rw [Equiv.apply_symm_apply, G.reverseWalk_involutive, Equiv.symm_apply_apply]

/-- k-step port power, including k=0 (degree 1, one holding port). -/
def power (k : ℕ) : PortGraph m (d ^ k) where
  vertices_pos := G.vertices_pos
  degree_pos := pow_pos G.degree_pos k
  rotation := G.powerRotation k
  reverse_reverse := G.powerRotation_involutive k

def walkEnd (k : ℕ) (v : Fin m) (a : Fin k → Fin d) : Fin m :=
  (G.reverseWalk k (v, a)).1

@[simp] theorem walkEnd_zero (v : Fin m) (a : Fin 0 → Fin d) :
    G.walkEnd 0 v a = v := rfl

@[simp] theorem walkEnd_cons (k : ℕ) (v : Fin m) (i : Fin d) (a : Fin k → Fin d) :
    G.walkEnd (k + 1) v (Fin.cons i a) =
      G.walkEnd k (G.neighbor v i) a := by
  simp only [walkEnd, reverseWalk, Fin.cons_zero, Fin.tail_cons, neighbor]

@[simp] theorem power_neighbor (k : ℕ) (v : Fin m) (i : Fin (d ^ k)) :
    (G.power k).neighbor v i = G.walkEnd k v (portWordEquiv d k i) := rfl

noncomputable section

/-- Endpoint sum over all words, not over the set of distinct endpoints. -/
theorem walkEnd_mass (k : ℕ) (v : Fin m) (f : RVec m) :
    (∑ a : Fin k → Fin d, f (G.walkEnd k v a)) =
      (d : ℝ) ^ k * G.transitionPow k f v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin d)).sum_comp
      (fun a => f (G.walkEnd (k + 1) v a)), Fintype.sum_prod_type]
    change (∑ i : Fin d, ∑ a : Fin k → Fin d,
      f (G.walkEnd (k + 1) v (Fin.cons i a))) = _
    simp only [G.walkEnd_cons, ih, ← Finset.mul_sum, G.transitionPow_succ]
    change (d : ℝ) ^ k * (∑ i, G.transitionPow k f (G.neighbor v i)) =
      (d : ℝ) ^ (k + 1) * ((∑ i, G.transitionPow k f (G.neighbor v i)) / (d : ℝ))
    have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.degree_pos)
    rw [pow_succ]
    field_simp

/-- Normalization is exactly d^k, including all repeated arcs and loops. -/
theorem power_transition (k : ℕ) (f : RVec m) :
    (G.power k).transition f = G.transitionPow k f := by
  ext v
  change (∑ i : Fin (d ^ k), f ((G.power k).neighbor v i)) /
    ((d ^ k : ℕ) : ℝ) = G.transitionPow k f v
  simp only [G.power_neighbor]
  rw [(portWordEquiv d k).sum_comp (fun a => f (G.walkEnd k v a)),
    G.walkEnd_mass, Nat.cast_pow]
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.degree_pos)
  field_simp

theorem power_transition_sum (k : ℕ) (f : RVec m) :
    (∑ v, (G.power k).transition f v) = ∑ v, f v :=
  (G.power k).transition_sum f

theorem power_even_positive (k : ℕ) (f : RVec m) :
    0 ≤ dot f ((G.power (2 * k)).transition f) := by
  rw [G.power_transition, G.transitionPow_even_quadratic]
  exact energy_nonneg _

theorem power384_centered (hg : G.PositiveGap (1 / 32))
    (f : RVec m) (hf : (∑ i, f i) = 0) :
    dot f ((G.power 384).transition f) ≤ (1 / 4096 : ℝ) * energy f := by
  rw [G.power_transition]
  exact G.transitionPow_384_centered hg f hf

theorem power384_positiveGap (hg : G.PositiveGap (1 / 32)) :
    (G.power 384).PositiveGap (4095 / 4096) := by
  apply (G.power 384).positiveGap_of_centered
    (by norm_num : (0 : ℝ) < 4095 / 4096)
    (by norm_num : (4095 / 4096 : ℝ) ≤ 1)
  · have hk : 2 * 192 = 384 := by decide
    have hp := G.power_even_positive 192
    rw [hk] at hp
    exact hp
  · intro f hf
    have h := G.power384_centered hg f hf
    have hc : (1 - 4095 / 4096 : ℝ) = 1 / 4096 := by norm_num
    simpa only [hc] using h

end
end PortGraph
end QecReliability.ExpanderWalk
