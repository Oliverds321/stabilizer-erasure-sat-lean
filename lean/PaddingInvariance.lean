import PhysicalBridge.GeneralStabilizer
import PhysicalBridge.PhysicalBernstein
import QecReliability.SparseNormalizer

set_option autoImplicit false

/-!
# Padding with single-qubit Z checks preserves the erasure reliability curve

Adjoining `m` fresh qubits, each stabilized by its own single-qubit `Z`, changes neither the
erasure ambiguity of any erased set (only its restriction to the original qubits matters) nor
the iid flagged-erasure fidelity curve.
-/

noncomputable section

namespace QecReliability.Padding

open Module
open scoped BigOperators
open QecReliability.Binary
open QecPhysical
open QecPhysical.Stabilizer
open QecPhysical.BinaryPauli

variable {n m : ℕ}

/-! ## Restriction and zero extension -/

/-- Restriction of a Pauli on `n+m` qubits to the first `n` qubits. -/
def oldPart (m : ℕ) : Pauli (n + m) →ₗ[Bit] Pauli n where
  toFun v := (fun i => v.1 (Fin.castAdd m i), fun i => v.2 (Fin.castAdd m i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem oldPart_apply (v : Pauli (n + m)) :
    oldPart m v = (fun i => v.1 (Fin.castAdd m i), fun i => v.2 (Fin.castAdd m i)) := rfl

/-- Zero extension of a Pauli on `n` qubits to `n+m` qubits. -/
def embed (m : ℕ) : Pauli n →ₗ[Bit] Pauli (n + m) where
  toFun u := (Fin.append u.1 0, Fin.append u.2 0)
  map_add' u u' := by
    ext k <;> induction k using Fin.addCases <;> simp
  map_smul' c u := by
    ext k <;> induction k using Fin.addCases <;> simp

@[simp] theorem embed_apply (u : Pauli n) :
    embed m u = (Fin.append u.1 0, Fin.append u.2 0) := rfl

@[simp] theorem oldPart_embed (u : Pauli n) : oldPart m (embed m u) = u := by
  ext i <;> simp

theorem castAdd_ne_natAdd (i : Fin n) (j : Fin m) : Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := i.isLt
  simp at h1
  omega

/-! ## The padded stabilizer space -/

/-- `S` on the first `n` qubits, and a single-qubit `Z` check on each of the `m` new qubits:
the restriction lies in `S` and the `x`-part vanishes on the new qubits. -/
def pad (m : ℕ) (S : Submodule Bit (Pauli n)) : Submodule Bit (Pauli (n + m)) where
  carrier := {v | oldPart m v ∈ S ∧ ∀ j : Fin m, v.1 (Fin.natAdd n j) = 0}
  zero_mem' := ⟨by rw [map_zero]; exact S.zero_mem, fun _ => rfl⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨?_, fun j => ?_⟩
    · rw [map_add]
      exact S.add_mem ha.1 hb.1
    · simp [ha.2 j, hb.2 j]
  smul_mem' := by
    intro c a ha
    refine ⟨?_, fun j => ?_⟩
    · rw [map_smul]
      exact S.smul_mem c ha.1
    · simp [ha.2 j]

@[simp] theorem mem_pad (S : Submodule Bit (Pauli n)) (v : Pauli (n + m)) :
    v ∈ pad m S ↔ oldPart m v ∈ S ∧ ∀ j : Fin m, v.1 (Fin.natAdd n j) = 0 := Iff.rfl

theorem embed_mem_pad {S : Submodule Bit (Pauli n)} {s : Pauli n} (hs : s ∈ S) :
    embed m s ∈ pad m S :=
  ⟨by simpa using hs, fun j => by simp⟩

theorem oldPart_zUnit_new (j : Fin m) : oldPart m (zUnit (Fin.natAdd n j)) = 0 := by
  ext i <;> simp [zUnit, castAdd_ne_natAdd]

theorem zUnit_new_mem_pad (S : Submodule Bit (Pauli n)) (j : Fin m) :
    zUnit (Fin.natAdd n j) ∈ pad m S := by
  refine ⟨?_, fun j' => ?_⟩
  · rw [oldPart_zUnit_new]
    exact S.zero_mem
  · simp [zUnit]

theorem symplectic_split (v w : Pauli (n + m)) :
    symplectic (n + m) v w = symplectic n (oldPart m v) (oldPart m w) +
      ∑ j : Fin m, (v.1 (Fin.natAdd n j) * w.2 (Fin.natAdd n j) +
        v.2 (Fin.natAdd n j) * w.1 (Fin.natAdd n j)) := by
  rw [symplectic_apply, symplectic_apply, Fin.sum_univ_add]
  rfl

theorem pad_isotropic {S : Submodule Bit (Pauli n)}
    (hS : S ≤ normalizer (symplectic n) S) :
    pad m S ≤ normalizer (symplectic (n + m)) (pad m S) := by
  intro w hw v hv
  change symplectic (n + m) v w = 0
  rw [symplectic_split]
  have h1 : symplectic n (oldPart m v) (oldPart m w) = 0 := hS hw.1 _ hv.1
  rw [h1, zero_add]
  simp [hv.2, hw.2]

/-- The symplectic complement of the padded space. -/
theorem mem_normalizer_pad (S : Submodule Bit (Pauli n)) (w : Pauli (n + m)) :
    w ∈ normalizer (symplectic (n + m)) (pad m S) ↔
      oldPart m w ∈ normalizer (symplectic n) S ∧ ∀ j : Fin m, w.1 (Fin.natAdd n j) = 0 := by
  constructor
  · intro hw
    refine ⟨fun s hs => ?_, fun j => ?_⟩
    · have h : symplectic (n + m) (embed m s) w = 0 := hw (embed m s) (embed_mem_pad hs)
      change symplectic n s (oldPart m w) = 0
      rw [symplectic_split] at h
      simpa using h
    · have h : symplectic (n + m) (zUnit (Fin.natAdd n j)) w = 0 :=
        hw _ (zUnit_new_mem_pad S j)
      rw [(symplectic_symm _).eq] at h
      simpa using h
  · rintro ⟨h1, h2⟩ v hv
    change symplectic (n + m) v w = 0
    rw [symplectic_split]
    have h3 : symplectic n (oldPart m v) (oldPart m w) = 0 := h1 _ hv.1
    rw [h3, zero_add]
    simp [hv.2, h2]

/-! ## Erased sets -/

/-- The erased original qubits. -/
def oldSet (m : ℕ) (E' : Finset (Fin (n + m))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Fin.castAdd m i ∈ E')

/-- The erased new qubits. -/
def newSet (n : ℕ) (E' : Finset (Fin (n + m))) : Finset (Fin m) :=
  Finset.univ.filter (fun j => Fin.natAdd n j ∈ E')

@[simp] theorem mem_oldSet (E' : Finset (Fin (n + m))) (i : Fin n) :
    i ∈ oldSet m E' ↔ Fin.castAdd m i ∈ E' := by simp [oldSet]

@[simp] theorem mem_newSet (E' : Finset (Fin (n + m))) (j : Fin m) :
    j ∈ newSet n E' ↔ Fin.natAdd n j ∈ E' := by simp [newSet]

theorem oldSet_eq_preimage (E' : Finset (Fin (n + m))) :
    oldSet m E' = E'.preimage (Fin.castAdd m) (Fin.castAdd_injective _ _).injOn := by
  ext i
  simp

theorem oldPart_mem_supported {E' : Finset (Fin (n + m))} {v : Pauli (n + m)}
    (hv : v ∈ supported E') : oldPart m v ∈ supported (oldSet m E') := by
  intro i hi
  exact hv _ (by simpa using hi)

theorem embed_mem_supported {E' : Finset (Fin (n + m))} {u : Pauli n}
    (hu : u ∈ supported (oldSet m E')) : embed m u ∈ supported E' := by
  intro k hk
  induction k using Fin.addCases with
  | left i =>
    have := hu i (by simpa using hk)
    simpa using this
  | right j => simp

/-! ## Rank–nullity along the restriction -/

theorem finrank_eq_map_add_inf_ker {V W : Type*} [AddCommGroup V] [Module Bit V]
    [FiniteDimensional Bit V] [AddCommGroup W] [Module Bit W]
    (f : V →ₗ[Bit] W) (P : Submodule Bit V) :
    finrank Bit P = finrank Bit (P.map f) +
      finrank Bit (P ⊓ LinearMap.ker f : Submodule Bit V) := by
  have h := (f.domRestrict P).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have e : finrank Bit ((LinearMap.ker f).comap P.subtype) =
      finrank Bit (P ⊓ LinearMap.ker f : Submodule Bit V) := by
    rw [← Submodule.map_comap_subtype]
    exact LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective _ P.injective_subtype _)
  omega

theorem map_localized_pad (S : Submodule Bit (Pauli n)) (E' : Finset (Fin (n + m))) :
    (localized (symplectic (n + m)) (pad m S) (supported E')).map (oldPart m) =
      localized (symplectic n) S (supported (oldSet m E')) := by
  ext u
  simp only [Submodule.mem_map, localized, Submodule.mem_inf]
  constructor
  · rintro ⟨v, ⟨hvN, hvU⟩, rfl⟩
    exact ⟨((mem_normalizer_pad S v).1 hvN).1, oldPart_mem_supported hvU⟩
  · rintro ⟨huN, huU⟩
    refine ⟨embed m u, ⟨(mem_normalizer_pad S _).2 ⟨?_, fun j => by simp⟩,
      embed_mem_supported huU⟩, oldPart_embed u⟩
    simpa using huN

theorem map_inf_pad (S : Submodule Bit (Pauli n)) (E' : Finset (Fin (n + m))) :
    (pad m S ⊓ supported E').map (oldPart m) = S ⊓ supported (oldSet m E') := by
  ext u
  simp only [Submodule.mem_map, Submodule.mem_inf]
  constructor
  · rintro ⟨v, ⟨hvS, hvU⟩, rfl⟩
    exact ⟨hvS.1, oldPart_mem_supported hvU⟩
  · rintro ⟨huS, huU⟩
    exact ⟨embed m u, ⟨embed_mem_pad huS, embed_mem_supported huU⟩, oldPart_embed u⟩

theorem localized_inf_ker (S : Submodule Bit (Pauli n)) (E' : Finset (Fin (n + m))) :
    (localized (symplectic (n + m)) (pad m S) (supported E') ⊓ LinearMap.ker (oldPart m) :
        Submodule Bit (Pauli (n + m))) =
      (pad m S ⊓ supported E' ⊓ LinearMap.ker (oldPart m) :
        Submodule Bit (Pauli (n + m))) := by
  ext v
  simp only [localized, Submodule.mem_inf, LinearMap.mem_ker, mem_normalizer_pad, mem_pad]
  constructor
  · rintro ⟨⟨⟨_, h2⟩, h3⟩, h4⟩
    exact ⟨⟨⟨by rw [h4]; exact S.zero_mem, h2⟩, h3⟩, h4⟩
  · rintro ⟨⟨⟨_, h2⟩, h3⟩, h4⟩
    exact ⟨⟨⟨by rw [h4]; exact Submodule.zero_mem _, h2⟩, h3⟩, h4⟩

/-- **Core.** The erasure ambiguity of the padded code at `E'` is that of the original code at
the erased original qubits. No isotropy hypothesis is needed. -/
theorem ambiguity_pad (S : Submodule Bit (Pauli n)) (E' : Finset (Fin (n + m))) :
    ambiguity (symplectic (n + m)) (pad m S) (supported E') =
      ambiguity (symplectic n) S (supported (oldSet m E')) := by
  unfold ambiguity
  rw [finrank_eq_map_add_inf_ker (oldPart m) (localized _ _ _),
    finrank_eq_map_add_inf_ker (oldPart m) (pad m S ⊓ supported E'),
    map_localized_pad, map_inf_pad, localized_inf_ker]
  omega

theorem erasureScore_pad (S : Submodule Bit (Pauli n)) (E' : Finset (Fin (n + m))) :
    erasureScore (pad m S) E' = erasureScore S (oldSet m E') := by
  unfold erasureScore
  rw [ambiguity_pad]

/-! ## The iid sum -/

/-- Erased sets on `n+m` qubits are pairs (old part, new part). -/
def splitEquiv (n m : ℕ) : Finset (Fin n) × Finset (Fin m) ≃ Finset (Fin (n + m)) where
  toFun AB := Finset.univ.filter (fun k => Fin.addCases (motive := fun _ => Bool)
    (fun i => decide (i ∈ AB.1)) (fun j => decide (j ∈ AB.2)) k = true)
  invFun E' := (oldSet m E', newSet n E')
  left_inv := by
    rintro ⟨A, B⟩
    ext i <;> simp
  right_inv := by
    intro E'
    ext k
    induction k using Fin.addCases <;> simp

theorem card_split (E' : Finset (Fin (n + m))) :
    E'.card = (oldSet m E').card + (newSet n E').card := by
  have h := Fin.sum_univ_add (fun k : Fin (n + m) => if k ∈ E' then 1 else 0)
  rw [oldSet, newSet, Finset.card_filter, Finset.card_filter, ← h]
  simp

theorem causeMass_split (p : ℝ) (E' : Finset (Fin (n + m))) :
    causeMass p E' = causeMass p (oldSet m E') * causeMass p (newSet n E') := by
  unfold causeMass
  have hc := card_split E'
  have ha : (oldSet m E').card ≤ n := by
    simpa using Finset.card_le_univ (oldSet m E')
  have hb : (newSet n E').card ≤ m := by
    simpa using Finset.card_le_univ (newSet n E')
  have he : n + m - E'.card = (n - (oldSet m E').card) + (m - (newSet n E').card) := by
    omega
  rw [he, hc, pow_add, pow_add]
  ring

/-- **Finite-sum identity.** For every real `p` and every score `f` on erased original qubits,
summing over erased sets of the padded register gives the original iid sum. -/
theorem causeMass_sum_pad (p : ℝ) (f : Finset (Fin n) → ℝ) :
    ∑ E' : Finset (Fin (n + m)), causeMass p E' * f (oldSet m E') =
      ∑ E : Finset (Fin n), causeMass p E * f E := by
  rw [← Equiv.sum_comp (splitEquiv n m), Fintype.sum_prod_type]
  have hinv : ∀ AB, (oldSet m (splitEquiv n m AB), newSet n (splitEquiv n m AB)) = AB :=
    fun AB => (splitEquiv n m).left_inv AB
  apply Finset.sum_congr rfl
  intro A _
  have h : ∀ B : Finset (Fin m), causeMass p (splitEquiv n m (A, B)) *
      f (oldSet m (splitEquiv n m (A, B))) = causeMass p A * f A * causeMass p B := by
    intro B
    have h1 := hinv (A, B)
    simp only [Prod.mk.injEq] at h1
    rw [causeMass_split, h1.1, h1.2]
    ring
  simp only [h]
  rw [← Finset.mul_sum, causeMass_sum, mul_one]

theorem erasureSum_pad (S : Submodule Bit (Pauli n)) (p : ℝ) :
    ∑ E' : Finset (Fin (n + m)), causeMass p E' * erasureScore (pad m S) E' =
      ∑ E : Finset (Fin n), causeMass p E * erasureScore S E := by
  simp only [erasureScore_pad]
  exact causeMass_sum_pad p (erasureScore S)

/-! ## Channel level -/

/-- **Curve invariance.** For any lifts of `S` and of its padding, the optimal fidelity of the
iid flagged erasure channel is the same for every `p ∈ [0,1]`. -/
theorem iidErasure_fidelity_pad {S : Submodule Bit (Pauli n)} (L : Lift S)
    (L' : Lift (pad m S)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementFidelity (L'.erasureFlagDecoder.comp
        (L'.iidLatentErasure (id : Causes (n + m) → Finset (Fin (n + m))) p hp0 hp1)).map =
      entanglementFidelity (L.erasureFlagDecoder.comp
        (L.iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0 hp1)).map := by
  unfold Lift.iidLatentErasure
  rw [(L'.latentErasure_optimum _ _ _ _).1, (L.latentErasure_optimum _ _ _ _).1]
  exact erasureSum_pad S p

/-- The same statement for the canonical lifts of isotropic spaces. -/
theorem isotropicLift_fidelity_pad {S : Submodule Bit (Pauli n)}
    (hS : S ≤ normalizer (symplectic n) S) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementFidelity ((isotropicLift (pad m S) (pad_isotropic hS)).erasureFlagDecoder.comp
        ((isotropicLift (pad m S) (pad_isotropic hS)).iidLatentErasure
          (id : Causes (n + m) → Finset (Fin (n + m))) p hp0 hp1)).map =
      entanglementFidelity ((isotropicLift S hS).erasureFlagDecoder.comp
        ((isotropicLift S hS).iidLatentErasure (id : Causes n → Finset (Fin n)) p hp0 hp1)).map :=
  iidErasure_fidelity_pad _ _ p hp0 hp1

/-! ## Row-level form -/

section Rows

open QecReliability.SharedCircuit

/-- Old coordinates embedded into the padded register. -/
def embedCoord (m : ℕ) : PauliCoord n → PauliCoord (n + m) :=
  Sum.map (Fin.castAdd m) (Fin.castAdd m)

/-- The old rows with embedded coordinates, followed by one single-`Z` row per new qubit. -/
def padRows (m : ℕ) (rows : List (List (PauliCoord n))) : List (List (PauliCoord (n + m))) :=
  rows.map (List.map (embedCoord m)) ++
    (List.finRange m).map (fun j => [Sum.inr (Fin.natAdd n j)])

theorem rowIncidences_padRows (rows : List (List (PauliCoord n))) :
    rowIncidences (padRows m rows) = rowIncidences rows + m := by
  simp [rowIncidences, padRows, List.map_map, Function.comp_def]

theorem embed_xUnit (i : Fin n) : embed m (xUnit i) = xUnit (Fin.castAdd m i) := by
  ext k <;> induction k using Fin.addCases <;>
    simp [xUnit, Pi.single_apply, (castAdd_ne_natAdd _ _).symm]

theorem embed_zUnit (i : Fin n) : embed m (zUnit i) = zUnit (Fin.castAdd m i) := by
  ext k <;> induction k using Fin.addCases <;>
    simp [zUnit, Pi.single_apply, (castAdd_ne_natAdd _ _).symm]

theorem decodeRow_embed (row : List (PauliCoord n)) :
    decodeRow (row.map (embedCoord m)) = embed m (decodeRow row) := by
  unfold decodeRow
  rw [map_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  cases c
  · exact (embed_xUnit _).symm
  · exact (embed_zUnit _).symm

theorem pad_decompose {S : Submodule Bit (Pauli n)} {v : Pauli (n + m)} (hv : v ∈ pad m S) :
    v = embed m (oldPart m v) + ∑ j : Fin m, v.2 (Fin.natAdd n j) • zUnit (Fin.natAdd n j) := by
  ext k <;> induction k using Fin.addCases <;>
    simp [zUnit, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply,
      castAdd_ne_natAdd, hv.2]

theorem rowSpace_padRows (rows : List (List (PauliCoord n))) :
    rowSpace (padRows m rows) = pad m (rowSpace rows) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [padRows, List.map_append, List.mem_append, List.map_map, Set.mem_ofPred_eq,
      List.mem_map, Function.comp_apply, List.mem_finRange, true_and] at hx
    rcases hx with ⟨row, hrow, rfl⟩ | ⟨j, rfl⟩
    · rw [decodeRow_embed]
      exact embed_mem_pad (Submodule.subset_span (List.mem_map.mpr ⟨row, hrow, rfl⟩))
    · have hz : decodeRow [(Sum.inr (Fin.natAdd n j) : PauliCoord (n + m))] =
          zUnit (Fin.natAdd n j) := by
        simp [decodeRow, coordPauli]
      rw [hz]
      exact zUnit_new_mem_pad _ j
  · intro v hv
    rw [pad_decompose hv]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    · have hmap : (rowSpace rows).map (embed m) ≤ rowSpace (padRows m rows) := by
        rw [rowSpace, Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
        rw [← decodeRow_embed]
        simp only [padRows, List.map_append, Set.mem_ofPred_eq, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨row.map (embedCoord m),
          List.mem_map.mpr ⟨row, hrow, rfl⟩, rfl⟩)
      exact hmap ⟨oldPart m v, hv.1, rfl⟩
    · apply Submodule.subset_span
      simp only [padRows, List.map_append, Set.mem_ofPred_eq, List.mem_append]
      refine Or.inr (List.mem_map.mpr ⟨[Sum.inr (Fin.natAdd n j)],
        List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩, ?_⟩)
      simp [decodeRow, coordPauli]

end Rows

end QecReliability.Padding

#print axioms QecReliability.Padding.pad_isotropic
#print axioms QecReliability.Padding.erasureScore_pad
#print axioms QecReliability.Padding.erasureSum_pad
#print axioms QecReliability.Padding.iidErasure_fidelity_pad
#print axioms QecReliability.Padding.isotropicLift_fidelity_pad
#print axioms QecReliability.Padding.rowSpace_padRows
#print axioms QecReliability.Padding.rowIncidences_padRows
