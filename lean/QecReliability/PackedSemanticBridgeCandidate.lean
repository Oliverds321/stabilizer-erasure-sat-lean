/-
Packed binary words and row-major Boolean matrices, with equivalences to the
semantic words and matrices of `FiniteLocalCountingCandidate`.





-/
import QecReliability.FiniteLocalCountingCandidate
import QecReliability.FiniteLocalSelectorCandidate
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace PackedSemanticBridgeCandidate

open FiniteLocalCountingCandidate FiniteLocalSelectorCandidate

abbrev F := ZMod 2
abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Packed (n : ℕ) := Fin (2 ^ n)
abbrev BoolMat (k h : ℕ) := Fin h → Fin k → Bool

/-! ## Explicit binary recursion; coordinate zero is the least significant bit -/

def packNat : (n : ℕ) → Bits n → ℕ
  | 0, _ => 0
  | n + 1, x => Nat.bit (x 0) (packNat n (fun i => x i.succ))

/-- The decoder uses primitive division rather than unary `Nat.boddDiv2`.
It pads to exactly n coordinates, including leading zero bits. -/
def unpackNat : (n : ℕ) → ℕ → Bits n
  | 0, _ => Fin.elim0
  | n + 1, a => Fin.cases (a.testBit 0) (unpackNat n (a / 2))

theorem packNat_lt (n : ℕ) (x : Bits n) : packNat n x < 2 ^ n := by
  induction n with
  | zero => simp [packNat]
  | succ n ih =>
    exact Nat.bit_lt_two_pow_succ_iff.mpr (ih (fun i => x i.succ))

theorem unpackNat_eq_testBit (n a : ℕ) (i : Fin n) :
    unpackNat n a i = a.testBit i.val := by
  induction n generalizing a with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change unpackNat n (a / 2) j = a.testBit (j.val + 1)
      rw [ih]
      have h := Nat.testBit_bit_succ j.val (Nat.bodd a) (Nat.div2 a)
      rw [Nat.bit_bodd_div2, Nat.div2_val] at h
      exact h.symm

theorem packNat_testBit (n : ℕ) (x : Bits n) (i : Fin n) :
    (packNat n x).testBit i.val = x i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (Nat.bit (x 0) (packNat n (fun j => x j.succ))).testBit 0 = x 0
      exact Nat.testBit_bit_zero _ _
    · change (Nat.bit (x 0) (packNat n (fun j => x j.succ))).testBit
        (j.val + 1) = x j.succ
      rw [Nat.testBit_bit_succ]
      exact ih (fun j => x j.succ) j

def pack {n : ℕ} (x : Bits n) : Packed n := ⟨packNat n x, packNat_lt n x⟩

def unpack {n : ℕ} (a : Packed n) : Bits n := unpackNat n a.val

@[simp] theorem unpack_apply {n : ℕ} (a : Packed n) (i : Fin n) :
    unpack a i = a.val.testBit i.val := unpackNat_eq_testBit n a.val i

@[simp] theorem unpack_pack {n : ℕ} (x : Bits n) : unpack (pack x) = x := by
  funext i
  exact (unpack_apply (pack x) i).trans (packNat_testBit n x i)

@[simp] theorem pack_unpack {n : ℕ} (a : Packed n) : pack (unpack a) = a := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact (packNat_testBit n (unpack a) ⟨i, hi⟩).trans (unpack_apply a ⟨i, hi⟩)
  · have hpow : 2 ^ n ≤ (2 : ℕ) ^ i :=
      pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) (by omega)
    rw [Nat.testBit_eq_false_of_lt ((pack (unpack a)).isLt.trans_le hpow),
      Nat.testBit_eq_false_of_lt (a.isLt.trans_le hpow)]

/-- Neither direction uses enumeration or choice; both are the recursions above. -/
def packedBitsEquiv (n : ℕ) : Packed n ≃ Bits n where
  toFun := unpack
  invFun := pack
  left_inv := pack_unpack
  right_inv := unpack_pack

/-! ## Explicit row-major flattening; no positive-width assumption is necessary -/

def flatIndex {k h : ℕ} (i : Fin h) (j : Fin k) : Fin (h * k) :=
  ⟨i.val * k + j.val, by
    calc
      i.val * k + j.val < i.val * k + k := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * k := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ h * k := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr i.isLt)⟩

/-- `Fin.divNat` and `Fin.modNat` are total. If k=0, the source Fin(h*k)
is empty, so no arbitrary row or column is supplied. -/
def unflatIndex {k h : ℕ} (q : Fin (h * k)) : Fin h × Fin k :=
  (q.divNat, q.modNat)

@[simp] theorem unflat_flat {k h : ℕ} (i : Fin h) (j : Fin k) :
    unflatIndex (flatIndex i j) = (i, j) := by
  have hk : 0 < k := Nat.zero_lt_of_lt j.isLt
  apply Prod.ext <;> apply Fin.ext
  · change (i.val * k + j.val) / k = i.val
    rw [Nat.add_comm, Nat.mul_comm i.val k, Nat.add_mul_div_left _ _ hk,
      Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  · change (i.val * k + j.val) % k = j.val
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

@[simp] theorem flat_unflat {k h : ℕ} (q : Fin (h * k)) :
    flatIndex (unflatIndex q).1 (unflatIndex q).2 = q := by
  apply Fin.ext
  exact Nat.div_add_mod' q.val k

def rowMajorEquiv (k h : ℕ) : (Fin h × Fin k) ≃ Fin (h * k) where
  toFun p := flatIndex p.1 p.2
  invFun := unflatIndex
  left_inv p := unflat_flat p.1 p.2
  right_inv := flat_unflat

def flatten {k h : ℕ} (A : BoolMat k h) : Bits (h * k) :=
  fun q => A (unflatIndex q).1 (unflatIndex q).2

def unflatten {k h : ℕ} (x : Bits (h * k)) : BoolMat k h :=
  fun i j => x (flatIndex i j)

@[simp] theorem unflatten_flatten {k h : ℕ} (A : BoolMat k h) :
    unflatten (flatten A) = A := by
  funext i j
  simp only [unflatten, flatten, unflat_flat]

@[simp] theorem flatten_unflatten {k h : ℕ} (x : Bits (h * k)) :
    flatten (unflatten x) = x := by
  funext q
  simp only [flatten, unflatten, flat_unflat]

def flattenEquiv (k h : ℕ) : BoolMat k h ≃ Bits (h * k) where
  toFun := flatten
  invFun := unflatten
  left_inv := unflatten_flatten
  right_inv := flatten_unflatten

/-! ## The two-element alphabet, with executable inverses -/

def bitF (b : Bool) : F := if b then 1 else 0
def fieldBit (z : F) : Bool := decide (z ≠ 0)

@[simp] theorem bitF_false : bitF false = 0 := rfl
@[simp] theorem bitF_true : bitF true = 1 := rfl

@[simp] theorem bitF_ne_zero (b : Bool) : bitF b ≠ 0 ↔ b = true := by
  cases b <;> simp [bitF]

@[simp] theorem fieldBit_bitF (b : Bool) : fieldBit (bitF b) = b := by
  cases b <;> decide

/-- This decision enumerates exactly TWO alphabet elements, never words or matrices. -/
@[simp] theorem bitF_fieldBit : ∀ z : F, bitF (fieldBit z) = z := by decide

theorem bitF_xor (a b : Bool) : bitF (Bool.xor a b) = bitF a + bitF b := by
  cases a <;> cases b <;> decide

theorem bitF_and (a b : Bool) : bitF (a && b) = bitF a * bitF b := by
  cases a <;> cases b <;> decide

def boolFieldEquiv : Bool ≃ F where
  toFun := bitF
  invFun := fieldBit
  left_inv := fieldBit_bitF
  right_inv := bitF_fieldBit

def semanticWord (n a : ℕ) : FiniteLocalCountingCandidate.Word n := fun i => bitF (a.testBit i.val)

def wordDecode {n : ℕ} (a : Packed n) : FiniteLocalCountingCandidate.Word n := semanticWord n a.val

def wordEncode {n : ℕ} (x : FiniteLocalCountingCandidate.Word n) : Packed n := pack (fun i => fieldBit (x i))

@[simp] theorem wordDecode_encode {n : ℕ} (x : FiniteLocalCountingCandidate.Word n) :
    wordDecode (wordEncode x) = x := by
  funext i
  change bitF ((packNat n (fun j => fieldBit (x j))).testBit i.val) = x i
  rw [packNat_testBit, bitF_fieldBit]

@[simp] theorem wordEncode_decode {n : ℕ} (a : Packed n) :
    wordEncode (wordDecode a) = a := by
  have hb : (fun i => fieldBit (wordDecode a i)) = unpack a := by
    funext i
    simp only [wordDecode, semanticWord, fieldBit_bitF, unpack_apply]
  change pack (fun i => fieldBit (wordDecode a i)) = a
  rw [hb, pack_unpack]

def packedWordEquiv (n : ℕ) : Packed n ≃ FiniteLocalCountingCandidate.Word n where
  toFun := wordDecode
  invFun := wordEncode
  left_inv := wordEncode_decode
  right_inv := wordDecode_encode

@[simp] theorem semanticWord_zero (n : ℕ) : semanticWord n 0 = 0 := by
  funext i
  simp [semanticWord]

theorem wordDecode_zero_iff {n : ℕ} (a : Packed n) :
    wordDecode a = 0 ↔ a.val = 0 := by
  let z : Packed n := ⟨0, by positivity⟩
  have hz : wordDecode z = 0 := semanticWord_zero n
  constructor
  · intro ha
    have heq := (packedWordEquiv n).injective (ha.trans hz.symm)
    exact congrArg Fin.val heq
  · intro ha
    exact (congrArg (semanticWord n) ha).trans (semanticWord_zero n)

def semanticMatrix (k h a : ℕ) : FiniteLocalCountingCandidate.Mat k h :=
  fun i j => bitF (a.testBit (i.val * k + j.val))

def matrixDecode {k h : ℕ} (a : Packed (h * k)) : FiniteLocalCountingCandidate.Mat k h :=
  semanticMatrix k h a.val

def matrixEncode {k h : ℕ} (A : FiniteLocalCountingCandidate.Mat k h) : Packed (h * k) :=
  pack (flatten (fun i j => fieldBit (A i j)))

@[simp] theorem matrixDecode_encode {k h : ℕ} (A : FiniteLocalCountingCandidate.Mat k h) :
    matrixDecode (matrixEncode A) = A := by
  funext i j
  change bitF ((packNat (h * k) (flatten (fun i j => fieldBit (A i j)))).testBit
    (flatIndex i j).val) = A i j
  rw [packNat_testBit]
  simp only [flatten, unflat_flat, bitF_fieldBit]

@[simp] theorem matrixEncode_decode {k h : ℕ} (a : Packed (h * k)) :
    matrixEncode (matrixDecode a) = a := by
  have hb : flatten (fun i j => fieldBit (matrixDecode a i j)) = unpack a := by
    funext q
    change fieldBit (bitF (a.val.testBit
      (flatIndex (unflatIndex q).1 (unflatIndex q).2).val)) = unpack a q
    rw [flat_unflat, fieldBit_bitF, unpack_apply]
  change pack (flatten (fun i j => fieldBit (matrixDecode a i j))) = a
  rw [hb, pack_unpack]

def packedMatrixEquiv (k h : ℕ) : Packed (h * k) ≃ FiniteLocalCountingCandidate.Mat k h where
  toFun := matrixDecode
  invFun := matrixEncode
  left_inv := matrixEncode_decode
  right_inv := matrixDecode_encode

/-! ## Reflection of the existing packed checker, not a replacement checker -/

theorem wordWeight_eq_sum (n a : ℕ) :
    FiniteLocalSelectorCandidate.wordWeight n a = ∑ i : Fin n, if a.testBit i.val then 1 else 0 := by
  induction n with
  | zero => simp [FiniteLocalSelectorCandidate.wordWeight]
  | succ n ih =>
    simpa only [FiniteLocalSelectorCandidate.wordWeight, Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last]
      using congrArg (fun v => v + if a.testBit n then 1 else 0) ih

theorem weight_bitF {ι : Type*} [Fintype ι] (x : ι → Bool) :
    FiniteLocalCountingCandidate.weight (fun i => bitF (x i)) = ∑ i, if x i then 1 else 0 := by
  classical
  rw [FiniteLocalCountingCandidate.weight, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp [bitF]

theorem wordWeight_refines (n a : ℕ) :
    FiniteLocalSelectorCandidate.wordWeight n a = FiniteLocalCountingCandidate.weight (semanticWord n a) := by
  rw [wordWeight_eq_sum]
  exact (weight_bitF (fun i : Fin n => a.testBit i.val)).symm

/-- The stride stays k throughout; the prefix length j alone is recursive. -/
theorem rowPrefix_refines (k a x row j : ℕ) :
    bitF (FiniteLocalSelectorCandidate.rowPrefix k a x row j) =
      ∑ c : Fin j, bitF (a.testBit (row * k + c.val)) * bitF (x.testBit c.val) := by
  induction j with
  | zero => simp [FiniteLocalSelectorCandidate.rowPrefix]
  | succ j ih =>
    simpa only [FiniteLocalSelectorCandidate.rowPrefix, bitF_xor, bitF_and, Fin.sum_univ_castSucc,
      Fin.coe_castSucc, Fin.val_last] using
      congrArg (fun v => v + bitF (a.testBit (row * k + j)) * bitF (x.testBit j)) ih

theorem rowPrefix_evalHom (k h a x : ℕ) (i : Fin h) :
    bitF (FiniteLocalSelectorCandidate.rowPrefix k a x i.val k) =
      FiniteLocalCountingCandidate.evalHom (semanticWord k x) (semanticMatrix k h a) i := by
  exact rowPrefix_refines k a x i.val k

theorem parityWeight_eq_sum (k a x h : ℕ) :
    FiniteLocalSelectorCandidate.parityWeight k a x h =
      ∑ i : Fin h, if FiniteLocalSelectorCandidate.rowPrefix k a x i.val k then 1 else 0 := by
  induction h with
  | zero => simp [FiniteLocalSelectorCandidate.parityWeight]
  | succ h ih =>
    simpa only [FiniteLocalSelectorCandidate.parityWeight, Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last]
      using congrArg (fun v => v + if FiniteLocalSelectorCandidate.rowPrefix k a x h k then 1 else 0) ih

theorem parityWeight_refines (k h a x : ℕ) :
    FiniteLocalSelectorCandidate.parityWeight k a x h =
      FiniteLocalCountingCandidate.weight (FiniteLocalCountingCandidate.evalHom (semanticWord k x) (semanticMatrix k h a)) := by
  have heq : (fun i : Fin h => bitF (FiniteLocalSelectorCandidate.rowPrefix k a x i.val k)) =
      FiniteLocalCountingCandidate.evalHom (semanticWord k x) (semanticMatrix k h a) := by
    funext i
    exact rowPrefix_evalHom k h a x i
  rw [← heq, weight_bitF, parityWeight_eq_sum]

theorem systematicWeight_refines (k h a x : ℕ) :
    FiniteLocalSelectorCandidate.systematicWeight k h a x = FiniteLocalCountingCandidate.weight (semanticWord k x) +
      FiniteLocalCountingCandidate.weight (FiniteLocalCountingCandidate.evalHom (semanticWord k x) (semanticMatrix k h a)) := by
  rw [FiniteLocalSelectorCandidate.systematicWeight, wordWeight_refines, parityWeight_refines]

def Good {k h : ℕ} (r : ℕ) (A : FiniteLocalCountingCandidate.Mat k h) : Prop :=
  ∀ x : FiniteLocalCountingCandidate.Word k, x ≠ 0 → r ≤ FiniteLocalCountingCandidate.weight x + FiniteLocalCountingCandidate.weight (FiniteLocalCountingCandidate.evalHom x A)

theorem checkMatrix_semantic {k h r : ℕ} (a : Packed (h * k)) :
    FiniteLocalSelectorCandidate.checkMatrix k h r a.val = true ↔ Good r (matrixDecode a) := by
  rw [FiniteLocalSelectorCandidate.checkMatrix_spec]
  constructor
  · intro ha x hx
    let q := wordEncode x
    have hdecode : semanticWord k q.val = x := wordDecode_encode x
    have hq : q.val ≠ 0 := by
      intro hq0
      apply hx
      rw [← hdecode, hq0, semanticWord_zero]
    have h := ha q.val q.isLt hq
    rw [systematicWeight_refines, hdecode] at h
    exact h
  · intro ha x hlt hx
    have hx' : semanticWord k x ≠ 0 := by
      intro hz
      exact hx ((wordDecode_zero_iff (⟨x, hlt⟩ : Packed k)).mp hz)
    rw [systematicWeight_refines]
    exact ha (semanticWord k x) hx'

theorem packed_exists_of_semantic {k h r : ℕ}
    (hex : ∃ A : FiniteLocalCountingCandidate.Mat k h, Good r A) :
    ∃ a, a < 2 ^ (h * k) ∧ FiniteLocalSelectorCandidate.checkMatrix k h r a = true := by
  obtain ⟨A, hA⟩ := hex
  refine ⟨(matrixEncode A).val, (matrixEncode A).isLt, ?_⟩
  apply (checkMatrix_semantic (matrixEncode A)).mpr
  simpa only [matrixDecode_encode] using hA

theorem checkMatrix_systematic {k h r : ℕ} (a : Packed (h * k)) :
    FiniteLocalSelectorCandidate.checkMatrix k h r a.val = true ↔
      ∀ x : FiniteLocalCountingCandidate.Word k, x ≠ 0 →
        r ≤ FiniteLocalCountingCandidate.weight
          (FiniteLocalCountingCandidate.systematicLinear (matrixDecode a) x) := by
  rw [checkMatrix_semantic]
  constructor
  · intro h x hx
    change r ≤ FiniteLocalCountingCandidate.weight
      (Sum.elim x (FiniteLocalCountingCandidate.evalHom x (matrixDecode a)))
    rw [FiniteLocalCountingCandidate.weight_sumElim]
    exact h x hx
  · intro h x hx
    have h' := h x hx
    change r ≤ FiniteLocalCountingCandidate.weight
      (Sum.elim x (FiniteLocalCountingCandidate.evalHom x (matrixDecode a))) at h'
    rw [FiniteLocalCountingCandidate.weight_sumElim] at h'
    exact h'

/-- Generic, constructive DATA. The semantic existential is eliminated only
inside a proposition proof passed to the existing bounded scanner. -/
def certifiedFromExistence {k h r : ℕ} (hex : ∃ A : FiniteLocalCountingCandidate.Mat k h, Good r A) :
    FiniteLocalSelectorCandidate.CertifiedParity k h r :=
  FiniteLocalSelectorCandidate.selectCertified k h r (packed_exists_of_semantic hex)

/-! ## The SAME selected table, linear map, and distance certificate -/

def certifiedMatrix {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r) : FiniteLocalCountingCandidate.Mat k h :=
  matrixDecode A.code

@[simp] theorem certifiedMatrix_entry {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r)
    (i : Fin h) (j : Fin k) : certifiedMatrix A i j = bitF (FiniteLocalSelectorCandidate.matrixEntry A i j) := rfl

theorem certifiedMatrix_good {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r) :
    Good r (certifiedMatrix A) := by
  apply (checkMatrix_semantic A.code).mp
  exact (FiniteLocalSelectorCandidate.checkMatrix_spec k h r A.code.val).mpr A.distance

def certifiedLinear {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r) :
    FiniteLocalCountingCandidate.Word k →ₗ[F] ((Fin k ⊕ Fin h) → F) :=
  FiniteLocalCountingCandidate.systematicLinear (certifiedMatrix A)

theorem certifiedLinear_distance {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r)
    (x : FiniteLocalCountingCandidate.Word k) (hx : x ≠ 0) : r ≤ FiniteLocalCountingCandidate.weight (certifiedLinear A x) := by
  change r ≤ FiniteLocalCountingCandidate.weight (Sum.elim x (FiniteLocalCountingCandidate.evalHom x (certifiedMatrix A)))
  rw [FiniteLocalCountingCandidate.weight_sumElim]
  exact certifiedMatrix_good A x hx

theorem certifiedLinear_left {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r)
    (x : FiniteLocalCountingCandidate.Word k) (i : Fin k) : certifiedLinear A x (Sum.inl i) = x i := rfl

theorem certifiedLinear_injective {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r) :
    Function.Injective (certifiedLinear A) := by
  intro x y hxy
  funext i
  exact congrFun hxy (Sum.inl i)

/-- This equality is the consumer-facing parity refinement. It refers to A.code
on both sides, not to a newly chosen good semantic matrix. -/
theorem certifiedLinear_right {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r)
    (x : Packed k) (i : Fin h) :
    certifiedLinear A (wordDecode x) (Sum.inr i) =
      bitF (FiniteLocalSelectorCandidate.rowPrefix k A.code.val x.val i.val k) :=
  (rowPrefix_evalHom k h A.code.val x.val i).symm

theorem trueEntryCount_refines {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r) :
    FiniteLocalSelectorCandidate.trueEntryCount A =
      (Finset.univ.filter (fun p : Fin h × Fin k => FiniteLocalSelectorCandidate.matrixEntry A p.1 p.2 = true)).card := by
  rw [FiniteLocalSelectorCandidate.trueEntryCount, wordWeight_eq_sum, Finset.card_filter]
  exact (Fintype.sum_equiv (rowMajorEquiv k h)
    (fun p : Fin h × Fin k => if FiniteLocalSelectorCandidate.matrixEntry A p.1 p.2 = true then 1 else 0)
    (fun q : Fin (h * k) => if A.code.val.testBit q.val then 1 else 0)
    (fun p => rfl)).symm

theorem trueEntryCount_fieldSupport {k h r : ℕ} (A : FiniteLocalSelectorCandidate.CertifiedParity k h r) :
    FiniteLocalSelectorCandidate.trueEntryCount A =
      FiniteLocalCountingCandidate.weight (fun p : Fin h × Fin k => certifiedMatrix A p.1 p.2) := by
  simpa only [FiniteLocalCountingCandidate.weight, certifiedMatrix_entry, bitF_ne_zero]
    using trueEntryCount_refines A

/-! ## Symbolic local/fixed specialization; NEVER evaluate these definitions -/

theorem local_packed_exists (t : ℕ) (ht : 0 < t) :
    ∃ a, a < 2 ^ ((64 * t) * (512 * t)) ∧
      FiniteLocalSelectorCandidate.checkMatrix (512 * t) (64 * t) t a = true :=
  packed_exists_of_semantic (FiniteLocalCountingCandidate.local_systematic_matrix_exists t ht)

def localCertified (t : ℕ) (ht : 0 < t) :
    FiniteLocalSelectorCandidate.CertifiedParity (512 * t) (64 * t) t :=
  FiniteLocalSelectorCandidate.selectCertified (512 * t) (64 * t) t (local_packed_exists t ht)

/-- Explicit runtime entry point for the fixed scale. The equality is erased;
the scale itself remains a runtime input to the bounded scanner. There is no
closed selected value or default argument for a module initializer to compute. -/
def fixedCertified (runtimeT : ℕ) (hT : runtimeT = 2 ^ 1528) :
    FiniteLocalSelectorCandidate.CertifiedParity (512 * 2 ^ 1528) (64 * 2 ^ 1528) (2 ^ 1528) :=
  let ht : 0 < runtimeT := hT.symm ▸ pow_pos (by decide : (0 : ℕ) < 2) 1528
  hT ▸ localCertified runtimeT ht

theorem fixedCertified_distance (runtimeT : ℕ) (hT : runtimeT = 2 ^ 1528)
    (x : FiniteLocalCountingCandidate.Word (512 * 2 ^ 1528)) (hx : x ≠ 0) :
    2 ^ 1528 ≤ FiniteLocalCountingCandidate.weight
      (certifiedLinear (fixedCertified runtimeT hT) x) :=
  certifiedLinear_distance _ x hx

theorem localCertified_distance (t : ℕ) (ht : 0 < t)
    (x : FiniteLocalCountingCandidate.Word (512 * t)) (hx : x ≠ 0) :
    t ≤ FiniteLocalCountingCandidate.weight (certifiedLinear (localCertified t ht) x) :=
  certifiedLinear_distance _ x hx

/-! ## Boundary cases: no positivity premises are hidden in the bridge -/

theorem checkMatrix_r0 (k h a : ℕ) : FiniteLocalSelectorCandidate.checkMatrix k h 0 a = true := by
  apply (FiniteLocalSelectorCandidate.checkMatrix_spec k h 0 a).mpr
  intro x _ _
  exact Nat.zero_le _

theorem checkMatrix_k0 (h r a : ℕ) : FiniteLocalSelectorCandidate.checkMatrix 0 h r a = true := by
  apply (FiniteLocalSelectorCandidate.checkMatrix_spec 0 h r a).mpr
  intro x hlt hx
  have hlt' : x < 1 := by simpa only [pow_zero] using hlt
  have hx0 : x = 0 := by omega
  exact False.elim (hx hx0)

theorem systematicWeight_h0 (k a x : ℕ) :
    FiniteLocalSelectorCandidate.systematicWeight k 0 a x = FiniteLocalSelectorCandidate.wordWeight k x := by
  simp [FiniteLocalSelectorCandidate.systematicWeight, FiniteLocalSelectorCandidate.parityWeight]

theorem checkMatrix_h0 (k r a : ℕ) :
    FiniteLocalSelectorCandidate.checkMatrix k 0 r a = true ↔
      ∀ x, x < 2 ^ k → x ≠ 0 → r ≤ FiniteLocalSelectorCandidate.wordWeight k x := by
  simpa only [systematicWeight_h0] using FiniteLocalSelectorCandidate.checkMatrix_spec k 0 r a

theorem wordWeight_pos {n x : ℕ} (hlt : x < 2 ^ n) (hx : x ≠ 0) :
    0 < FiniteLocalSelectorCandidate.wordWeight n x := by
  classical
  have hw : semanticWord n x ≠ 0 := by
    intro hz
    exact hx ((wordDecode_zero_iff (⟨x, hlt⟩ : Packed n)).mp hz)
  have hi : ∃ i, semanticWord n x i ≠ 0 := by
    by_contra! hi
    exact hw (funext hi)
  obtain ⟨i, hi⟩ := hi
  rw [wordWeight_refines, FiniteLocalCountingCandidate.weight]
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

theorem one_lt_two_pow_succ (n : ℕ) : 1 < (2 : ℕ) ^ (n + 1) := by
  have hp : (0 : ℕ) < 2 ^ n := pow_pos (by decide) n
  rw [pow_succ]
  omega

theorem wordWeight_one_succ (n : ℕ) :
    FiniteLocalSelectorCandidate.wordWeight (n + 1) 1 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change FiniteLocalSelectorCandidate.wordWeight (n + 1) 1 +
      (if (1 : ℕ).testBit (n + 1) then 1 else 0) = 1
    rw [ih, Nat.testBit_eq_false_of_lt (one_lt_two_pow_succ n)]
    rfl

/-- With no parity rows the systematic identity code has distance one, unless
there are no messages. This also checks the corner k=h=0 at arbitrary r. -/
theorem checkMatrix_h0_sharp (k r a : ℕ) :
    FiniteLocalSelectorCandidate.checkMatrix k 0 r a = true ↔ k = 0 ∨ r ≤ 1 := by
  cases k with
  | zero => simp [checkMatrix_k0]
  | succ k =>
    rw [checkMatrix_h0]
    constructor
    · intro h
      right
      simpa only [wordWeight_one_succ] using h 1 (one_lt_two_pow_succ k) (by decide)
    · rintro (hzero | hr)
      · omega
      · intro x hlt hx
        exact hr.trans (Nat.succ_le_iff.mpr (wordWeight_pos hlt hx))

end PackedSemanticBridgeCandidate
