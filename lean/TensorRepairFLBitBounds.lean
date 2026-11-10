import TensorRepairFLKeyBounds

/-! Bit-size invariants and compiled primitive resource bounds for rational
poset repair. Binary numerator/denominator sizes, rather than their numerical
magnitudes, govern all ratio arithmetic below. -/
set_option autoImplicit false

namespace QecReliability.TensorMachine.RepairFL
open FL FL.Lib FL.Lib.LinearRepairFL Trans.Wire
open Trans.Query.Bound Trans.BoundsQH
open Trans.Control (bodySig_cost bodySig_depth bodySig_msize)

/-- One common envelope for the three compositional FL resources. -/
def ResBound {a b : Ty} (F : FnSig a b) (x : a.den) (R : ℕ) : Prop :=
  F.cost x ≤ R ∧ F.depth x ≤ R ∧ F.msize x ≤ R

theorem ResBound.mono {a b : Ty} {F : FnSig a b} {x : a.den} {R S : ℕ}
    (h : ResBound F x R) (hrs : R ≤ S) : ResBound F x S :=
  ⟨h.1.trans hrs,h.2.1.trans hrs,h.2.2.trans hrs⟩

def comparisonBitsBudget (B : ℕ) : ℕ := 400 * (4*B+1) * (4*B+1) + 100*(B+1)

theorem lesser_resources (i : ℕ) (x y : RawRatio) (B : ℕ)
    (hx : RB B x) (hy : RB B y) : ResBound (lesserF i) (x,y) (comparisonBitsBudget B) := by
  have hc := lesser_cost_le i (x,y) (4*B) (by
    have := hx.1; have := hx.2; have := hy.1; have := hy.2;
    simp only; omega)
  obtain ⟨hx1,hx2⟩ := hx
  obtain ⟨hy1,hy2⟩ := hy
  refine ⟨hc.trans (by unfold comparisonBitsBudget; omega),?_,?_⟩
  · simp only [lesserF_depth,comparisonBitsBudget]
    omega
  · simp only [lesserF_msize,comparisonBitsBudget]
    omega

theorem greater_resources (i : ℕ) (x y : RawRatio) (B : ℕ)
    (hx : RB B x) (hy : RB B y) : ResBound (greaterF i) (x,y) (comparisonBitsBudget B) :=
  lesser_resources i x y B hx hy

theorem counts_resources (i a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    ResBound (countsF i) (a,b) (100*(B+1)) := by
  simp only [ResBound,countsF_cost,countsF_depth,countsF_msize]
  omega

theorem ratio_encoded_size (B : ℕ) (x : RawRatio) (hx : RB B x) :
    (TRatio.enc x).size ≤ 8*B+3 := by
  have h1 := Enc.nat_size_le x.1
  have h2 := Enc.nat_size_le x.2
  have := hx.1; have := hx.2
  simp only [TRatio,Ty.enc_prod,Ty.enc_nat,Val.size_cons]
  omega

def EntryBound (D B : ℕ) (x : RawEntry) : Prop := mag TKey x.1 ≤ D ∧ RB B x.2

def TableBound (D B : ℕ) (xs : RawTable) : Prop := ∀ x ∈ xs, EntryBound D B x

theorem key_encoded_size {D : ℕ} {key : Key} (h : mag TKey key ≤ D) :
    (TKey.enc key).size ≤ 5*D+1 := (size_le_mag TKey key).trans (by omega)

theorem entry_encoded_size {D B : ℕ} {x : RawEntry} (h : EntryBound D B x) :
    (TEntry.enc x).size ≤ 5*D+8*B+5 := by
  have hk := key_encoded_size h.1
  have hr := ratio_encoded_size B x.2 h.2
  simp only [TEntry,TRatio,Ty.enc_prod,Ty.enc_nat,Val.size_cons] at hr ⊢
  omega

theorem table_encoded_size {D B : ℕ} {xs : RawTable} (h : TableBound D B xs) :
    (TTable.enc xs).size ≤ (5*D+8*B+6)*xs.length+1 := by
  induction xs with
  | nil => simp [TTable,Ty.enc,Enc.list]
  | cons x xs ih =>
    have hx := entry_encoded_size (h x (by simp))
    have ht := ih (fun y hy => h y (by simp [hy]))
    rw [Ty.sz_list_cons]
    simp only [List.length_cons]
    nlinarith

theorem lowerR_bits {D B : ℕ} (hB : 1 ≤ B) {xs : RawTable}
    (h : TableBound D B xs) (j : Key) : RB B (lowerR xs j) := by
  induction xs with
  | nil => simp only [lowerR,RB,Nat.size_one]; exact ⟨hB,hB⟩
  | cons x xs ih =>
    have ht := ih (fun y hy => h y (by simp [hy]))
    have hx := (h x (by simp)).2
    rw [lowerR]
    split <;> first | exact lesserR_RB hx ht | exact ht

theorem upperR_bits {D B : ℕ} (hB : 1 ≤ B) {xs : RawTable}
    (h : TableBound D B xs) (j : Key) : RB B (upperR xs j) := by
  induction xs with
  | nil => simp only [upperR,RB,Nat.size_zero,Nat.size_one]; exact ⟨Nat.zero_le _,hB⟩
  | cons x xs ih =>
    have ht := ih (fun y hy => h y (by simp [hy]))
    have hx := (h x (by simp)).2
    rw [upperR]
    split <;> first | exact greaterR_RB hx ht | exact ht

theorem anchorR_bits {D B : ℕ} {xs : RawTable} (h : TableBound D B xs)
    (j : Key) (fallback : RawRatio) (hf : RB B fallback) : RB B (anchorR xs j fallback) := by
  induction xs with
  | nil => exact hf
  | cons x xs ih =>
    have ht := ih (fun y hy => h y (by simp [hy]))
    have hx := (h x (by simp)).2
    rw [anchorR]
    split <;> assumption

theorem substituteR_bound {D B : ℕ} {xs anchors : RawTable}
    (hx : TableBound D B xs) (ha : TableBound D B anchors) :
    TableBound D B (substituteR xs anchors) := by
  intro y hy
  obtain ⟨x,hxmem,rfl⟩ := List.mem_map.mp hy
  exact ⟨(hx x hxmem).1,anchorR_bits ha x.1 x.2 (hx x hxmem).2⟩

theorem pointR_bits {D B : ℕ} (hB : 1 ≤ B) {xs anchors : RawTable}
    (hx : TableBound D B xs) (ha : TableBound D B anchors) (j : Key) :
    RB B (pointR xs anchors j) :=
  greaterR_RB (upperR_bits hB ha j) (lowerR_bits hB hx j)

theorem repairR_bits {D B : ℕ} (hB : 1 ≤ B) {xs anchors : RawTable}
    (hx : TableBound D B xs) (ha : TableBound D B anchors) :
    ∀ x ∈ repairR xs anchors, RB B x := by
  intro x hmem
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hmem
  exact pointR_bits hB (substituteR_bound hx ha) ha j.1

/-- A single uniform comparator envelope for every key of magnitude at most D.
Key magnitude depends only on class sizes and key length, never on ratios. -/
theorem key_resources (L : Lib) (i : Indices) : ∃ k c, ∀ (D : ℕ) (a b : Key),
    mag TKey a ≤ D → mag TKey b ≤ D →
    ResBound (keyLeF L i) (a,b) (G k c (2*D+1)) ∧
    ResBound (keyEqF L i) (a,b) (G k c (2*D+1)) := by
  obtain ⟨k1,c1,h1⟩ := keyLeF_poly L i
  obtain ⟨k2,c2,h2⟩ := keyEqF_poly L i
  refine ⟨k1+k2,c1+c2,?_⟩
  intro D a b ha hb
  have hab : mag (.prod TKey TKey) (a,b) ≤ 2*D+1 := by
    change mag TKey a + mag TKey b + 1 ≤ _
    omega
  have hle := G_mono (k := k1) (c := c1) (by omega : k1 ≤ k1+k2)
    (by omega : c1 ≤ c1+c2) hab
  have heq := G_mono (k := k2) (c := c2) (by omega : k2 ≤ k1+k2)
    (by omega : c2 ≤ c1+c2) hab
  obtain ⟨hc1,hd1,hm1,_⟩ := h1 (a,b)
  obtain ⟨hc2,hd2,hm2,_⟩ := h2 (a,b)
  exact ⟨⟨hc1.trans hle,hd1.trans hle,hm1.trans hle⟩,
    ⟨hc2.trans heq,hd2.trans heq,hm2.trans heq⟩⟩

end QecReliability.TensorMachine.RepairFL
