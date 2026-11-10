import QecReliability.TensorLayers
import QecReliability.QuantumLatentEncoder
import QecReliability.SimultaneousConfidence

/-! Distinct multiclass cause/Pauli pairs, exact normalized coefficients, and
one joint counting event. The counting interface here is discharged by the
concrete CNF queries in TensorQuantumEncoder; no runtime bound is asserted. -/

noncomputable section
namespace QecReliability.TensorCoefficientCounting
open TensorBernstein TensorLatent Binary
open SharedCircuit.LatentEncoding
open scoped BigOperators

abbrev Index (ds : List ℕ) := Bool × Grid ds
abbrev Key (n : ℕ) (ds : List ℕ) := CausesGrid ds × Pauli n

def keyBits (n : ℕ) (ds : List ℕ) : Key n ds ≃ BitModels (keySize n ds.sum) :=
  ((flattenCauses ds).prodCongr (Equiv.refl (Pauli n))).trans
    (SharedCircuit.LatentEncoding.keyBits n ds.sum)

theorem index_card (ds : List ℕ) :
    Fintype.card (Index ds) = 2 * (ds.map (fun r => r+1)).prod := by
  simp only [Index,Fintype.card_prod,Fintype.card_bool,grid_card]

def coefficientPredicate {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (side : Bool) (b : CausesGrid ds) (z : Pauli n) : Prop :=
  if side then Good (F := Bit) (symplectic n) S (supported (C b)) z
  else Bad (F := Bit) (symplectic n) S (supported (C b)) z

def coefficientModels {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (i : Index ds) : Finset (Key n ds) := by
  classical
  exact Finset.univ.filter (fun bz => layerIndex ds bz.1 = i.2 ∧
    bz.2 ∈ normalizer (F := Bit) (symplectic n) S ∧ coefficientPredicate S C i.1 bz.1 bz.2)

def goodCoefficient {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) : ℕ :=
  Nat.card {bz : Layer ds j × normalizer (F := Bit) (symplectic n) S //
    Good (F := Bit) (symplectic n) S (supported (C bz.1.val)) bz.2}

def badCoefficient {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) : ℕ :=
  Nat.card {bz : Layer ds j × normalizer (F := Bit) (symplectic n) S //
    Bad (F := Bit) (symplectic n) S (supported (C bz.1.val)) bz.2}

theorem coefficientModels_card {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (i : Index ds) :
    (coefficientModels S C i).card = if i.1 then goodCoefficient S C i.2 else badCoefficient S C i.2 := by
  classical
  let T := {bz : Layer ds i.2 × normalizer (F := Bit) (symplectic n) S //
    coefficientPredicate S C i.1 bz.1.val bz.2}
  let e : ↥(coefficientModels S C i) ≃ T :=
    { toFun := fun bz =>
        have h := (Finset.mem_filter.mp bz.property).2
        ⟨(⟨bz.val.1,h.1⟩,⟨bz.val.2,h.2.1⟩),h.2.2⟩
      invFun := fun bz => ⟨(bz.val.1.val,bz.val.2.val),by
        simp only [coefficientModels,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨bz.val.1.property,bz.val.2.property,bz.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Nat.card_congr e
  rw [Nat.card_eq_finsetCard] at h
  cases hs : i.1 <;> simpa [T,coefficientPredicate,hs,goodCoefficient,badCoefficient] using h

theorem coefficientModels_bound {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (i : Index ds) :
    (coefficientModels S C i).card ≤ 2 ^ keySize n ds.sum := by
  have h := Finset.card_le_univ (coefficientModels S C i)
  rw [Fintype.card_congr (keyBits n ds)] at h
  simpa [BitModels,Fintype.card_fun] using h

theorem coefficient_partition {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) :
    goodCoefficient S C j + badCoefficient S C j =
      layerSize ds j * Nat.card (normalizer (F := Bit) (symplectic n) S) := by
  have h := latent_pair_partition C (layerIndex ds) j
    (fun E (z : normalizer (F := Bit) (symplectic n) S) =>
      Good (F := Bit) (symplectic n) S (supported E) z)
    (fun E (z : normalizer (F := Bit) (symplectic n) S) =>
      Bad (F := Bit) (symplectic n) S (supported E) z)
    (fun E z => bad_iff_not_good (F := Bit) (symplectic n) (symplectic_nondegenerate n)
      (symplectic_refl n) S (supported E) z)
  change goodCoefficient S C j + badCoefficient S C j =
    Nat.card (Layer ds j) * Nat.card (normalizer (F := Bit) (symplectic n) S) at h
  simpa only [layer_card] using h

theorem good_coefficient_normalized {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) :
    (goodCoefficient S C j : ℝ) /
      ((layerSize ds j : ℝ) * Nat.card (normalizer (F := Bit) (symplectic n) S)) =
      observedCoefficients C (score S) j := by
  classical
  unfold goodCoefficient
  rw [pair_predicate_card (fun (b : Layer ds j) (z : normalizer (F := Bit) (symplectic n) S) =>
    Good (F := Bit) (symplectic n) S (supported (C b.val)) z),Nat.cast_sum]
  rw [mul_comm (layerSize ds j : ℝ),div_mul_eq_div_div,Finset.sum_div]
  rw [observedCoefficients,layerCoefficients_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact score_eq_good_fraction S hS (C b.val)

theorem coefficient_total_pos {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) :
    0 < (goodCoefficient S C j : ℝ) + badCoefficient S C j := by
  rw [← Nat.cast_add,coefficient_partition,Nat.cast_mul,normalizer_card]
  have hj : 0 < (layerSize ds j : ℝ) := by exact_mod_cast layerSize_pos ds j
  positivity

theorem coefficient_normalized {n : ℕ} {ds : List ℕ} (S : Submodule Bit (Pauli n))
    (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : CausesGrid ds → Finset (Fin n)) (j : Grid ds) :
    (goodCoefficient S C j : ℝ) / ((goodCoefficient S C j : ℝ)+badCoefficient S C j) =
      observedCoefficients C (score S) j := by
  rw [← Nat.cast_add,coefficient_partition,Nat.cast_mul]
  exact good_coefficient_normalized S hS C j

def estimates {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
    {S : Submodule Bit (Pauli n)} {C : CausesGrid ds → Finset (Fin n)}
    {H : HashStages Ω (Key n ds) (keySize n ds.sum)}
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ)
    (ω : Fin (2*m+1) → Ω) (j : Grid ds) : ℝ :=
  ExactTrialOracle.amplified O B m ω (true,j) /
    (ExactTrialOracle.amplified O B m ω (true,j)+ExactTrialOracle.amplified O B m ω (false,j))

/-- All classes, all coefficient tuples, and both count sides share one event. -/
theorem count_confidence {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
    (S : Submodule Bit (Pauli n)) (C : CausesGrid ds → Finset (Fin n))
    (H : HashStages Ω (Key n ds) (keySize n ds.sum))
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ) (hB : 0 < B)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hcell : 16 ≤ (ε/3)^2*(B:ℝ))
    (hrepeat : (Fintype.card (Index ds):ℝ)*(1/2:ℝ)^(m+2) ≤ δ) :
    1-δ ≤ (repeatedLaw H.law m).prob (fun ω => ∀ i,
      |ExactTrialOracle.amplified O B m ω i - ((coefficientModels S C i).card:ℝ)| ≤
        (ε/3)*((coefficientModels S C i).card:ℝ)) := by
  exact ExactTrialOracle.simultaneous_count_confidence O B m hB
    (coefficientModels_bound S C) (by linarith) (by linarith) hcell hrepeat

/-- Normalized coefficient estimates satisfy both-tail accuracy simultaneously.
The explicit hash and counting interfaces remain visible in this theorem. -/
theorem coefficients_confidence {Ω : Type*} [Fintype Ω] {n : ℕ} {ds : List ℕ}
    (S : Submodule Bit (Pauli n)) (hS : S ≤ normalizer (F := Bit) (symplectic n) S)
    (C : CausesGrid ds → Finset (Fin n))
    (H : HashStages Ω (Key n ds) (keySize n ds.sum))
    (O : ∀ i, ExactTrialOracle H (coefficientModels S C i)) (B m : ℕ) (hB : 0 < B)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hcell : 16 ≤ (ε/3)^2*(B:ℝ))
    (hrepeat : (Fintype.card (Index ds):ℝ)*(1/2:ℝ)^(m+2) ≤ δ) :
    1-δ ≤ (repeatedLaw H.law m).prob (fun ω => ∀ j,
      RelPair ε (observedCoefficients C (score S) j) (estimates O B m ω j) ∧
      0 ≤ estimates O B m ω j ∧ estimates O B m ω j ≤ 1) := by
  apply (count_confidence S C H O B m hB hε hε1 hcell hrepeat).trans
  apply FiniteProbability.prob_mono
  intro ω hω j
  have hg := hω (true,j)
  have hb := hω (false,j)
  simp only [coefficientModels_card,Bool.true_eq,↓reduceIte] at hg
  simp only [coefficientModels_card,Bool.false_eq_true,↓reduceIte] at hb
  have h := normalize_counts hε.le hε1 (Nat.cast_nonneg (goodCoefficient S C j))
    (Nat.cast_nonneg (badCoefficient S C j)) (coefficient_total_pos S C j) hg hb
  rw [coefficient_normalized S hS C j] at h
  exact ⟨h.2.2.2,h.2.1,h.2.2.1⟩

end QecReliability.TensorCoefficientCounting
