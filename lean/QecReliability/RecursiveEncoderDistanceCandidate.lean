import QecReliability.XorTranspose
import QecReliability.SerializedEncoderWiringCandidateReviewed
import QecReliability.PaddedSparseCandidate

/-!


This module proves properties of the ACTUAL `SerializedDyadicEncoder.encoder`
defined by the one-copy wiring module. It does not replace that
constructor by a separately supplied good encoder.




Concrete graph/local-matrix construction, circuit compilation equalities, and
machine-time certificates remain separate lower-level binding obligations.
-/

set_option autoImplicit false
noncomputable section

namespace QecReliability.SharedCircuit
open CodeHash
open scoped BigOperators
open ExpanderWalk.SparseAmplifierCandidate

namespace EncoderSemantics

/-- Transport only; indices retain their natural-number values. -/
def castWord {n m : Nat} (h : n = m) : Word n →ₗ[F] Word m where
  toFun x i := x (Fin.cast h.symm i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem weight_castWord {n m : Nat} (h : n = m) (x : Word n) :
    weight (castWord h x) = weight x := by
  cases h
  rfl

@[simp] theorem castWord_rfl {n : Nat} (x : Word n) : castWord rfl x = x := rfl

@[simp] theorem castWord_symm {n m : Nat} (h : n = m) (x : Word n) :
    castWord h.symm (castWord h x) = x := by
  cases h
  rfl

theorem castWord_injective {n m : Nat} (h : n = m) :
    Function.Injective (castWord h) := by
  intro x y hxy
  simpa only [castWord_symm] using congrArg (castWord h.symm) hxy

theorem weight_pos_of_ne_zero {n : Nat} {x : Word n} (hx : x ≠ 0) :
    0 < weight x := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  exact Finset.card_pos.mpr ⟨i, by simp [weight, hi]⟩

theorem ne_zero_of_weight_pos {n : Nat} {x : Word n} (hx : 0 < weight x) :
    x ≠ 0 := by
  intro hz
  subst x
  simpa [weight] using hx

theorem bitsVector_append {n m : Nat} (x : BitModels n) (y : BitModels m) :
    bitsVector (Fin.append x y) = Fin.append (bitsVector x) (bitsVector y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [bitsVector]

@[simp] theorem bitsVector_wordBits {n : Nat} (x : Word n) :
    bitsVector (wordBits n x) = x := by
  funext i
  exact BadEncoding.boolBit_bitBool (x i)

end EncoderSemantics

namespace XorCircuit

/-- Evaluate the same typed DAG over F₂. No tree expansion and no extra gate. -/
def fieldRun {n : Nat} : {g : Nat} → XorCircuit n g → Word n → Word (n + g)
  | _, .nil, x => x
  | _, .zero C, x => Fin.snoc (C.fieldRun x) 0
  | _, .xor C a b, x => Fin.snoc (C.fieldRun x) (C.fieldRun x a + C.fieldRun x b)

theorem fieldRun_add {n g : Nat} (C : XorCircuit n g) (x y : Word n) :
    C.fieldRun (x + y) = C.fieldRun x + C.fieldRun y := by
  induction C with
  | nil => rfl
  | zero C ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [fieldRun, ih]
  | xor C a b ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [fieldRun, ih, add_assoc, add_comm, add_left_comm]
    · simp [fieldRun, ih]

theorem fieldRun_smul {n g : Nat} (C : XorCircuit n g) (c : F) (x : Word n) :
    C.fieldRun (c • x) = c • C.fieldRun x := by
  induction C with
  | nil => rfl
  | zero C ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [fieldRun, ih]
  | xor C a b ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [fieldRun, ih, smul_add, mul_add]

theorem fieldRun_bool {n g : Nat} (C : XorCircuit n g) (x : BitModels n) :
    C.fieldRun (bitsVector x) = bitsVector (C.toCircuit.run x) := by
  induction C with
  | nil => rfl
  | zero C ih =>
    change Fin.snoc (C.fieldRun (bitsVector x)) 0 =
      bitsVector (Fin.snoc (C.toCircuit.run x) false)
    simp only [bitsVector_snoc, ih, boolBit, Bool.false_eq_true, ↓reduceIte]
  | xor C a b ih =>
    change Fin.snoc (C.fieldRun (bitsVector x))
      (C.fieldRun (bitsVector x) a + C.fieldRun (bitsVector x) b) =
      bitsVector (Fin.snoc (C.toCircuit.run x)
        (Bool.xor (C.toCircuit.run x a) (C.toCircuit.run x b)))
    rw [bitsVector_snoc, ih, boolBit_xor]
    rfl

end XorCircuit

namespace XorProgram
open EncoderSemantics

/-- The linear map of the supplied program, not an assumed semantic witness. -/
def toLinear {n m : Nat} (P : XorProgram n m) : Word n →ₗ[F] Word m where
  toFun x i := P.circuit.fieldRun x (P.output i)
  map_add' x y := by
    funext i
    simp only [XorCircuit.fieldRun_add, Pi.add_apply]
  map_smul' c x := by
    funext i
    simp only [XorCircuit.fieldRun_smul, Pi.smul_apply, RingHom.id_apply]

theorem toLinear_bool {n m : Nat} (P : XorProgram n m) (x : BitModels n) :
    P.toLinear (bitsVector x) = bitsVector (P.toProgram.eval x) := by
  funext i
  exact congrFun (P.circuit.fieldRun_bool x) (P.output i)

theorem toLinear_wordBits {n m : Nat} (P : XorProgram n m) (x : Word n) :
    P.toLinear x = bitsVector (P.toProgram.eval (wordBits n x)) := by
  simpa only [bitsVector_wordBits] using P.toLinear_bool (wordBits n x)

theorem oneCopy_linear {n a h d : Nat} (R₁ : XorProgram n a)
    (H : XorProgram a h) (R₂ : XorProgram h d) (x : Word n) :
    (oneCopy R₁ H R₂).toLinear x =
      Fin.append x (Fin.append (H.toLinear (R₁.toLinear x))
        (R₂.toLinear (H.toLinear (R₁.toLinear x)))) := by
  rw [toLinear_wordBits, oneCopy_eval, bitsVector_append, bitsVector_append]
  simp only [← toLinear_bool, bitsVector_wordBits]

@[simp] theorem outputCast_linear {n m k : Nat} (P : XorProgram n m)
    (h : m = k) (x : Word n) :
    (P.outputCast h).toLinear x = castWord h (P.toLinear x) := rfl

@[simp] theorem inputCast_linear {n m k : Nat} (P : XorProgram n k)
    (h : n = m) (x : Word m) :
    (P.inputCast h).toLinear x = P.toLinear (castWord h.symm x) := by
  cases h
  rfl

end XorProgram

namespace EncoderSemantics

def theta : ℝ := 1 / 2359296
def alpha : ℝ := 1 / 16777216

theorem alpha_eq_two_pow : alpha = (2 : ℝ) ^ (-24 : ℤ) := by
  norm_num [alpha]

theorem four_alpha_le_theta : 4 * alpha ≤ theta := by norm_num [alpha, theta]
theorem two_alpha_le_theta : 2 * alpha ≤ theta := by norm_num [alpha, theta]
theorem alpha_pos : 0 < alpha := by norm_num [alpha]
theorem theta_nonneg : 0 ≤ theta := by norm_num [theta]

/-- This is a local amplifier property, never a desired encoder-distance premise. -/
def SparseSpec {n m : Nat} (R : XorProgram n m) : Prop :=
  ∀ x : Word n, 0 < weight x → (weight x : ℝ) ≤ theta * (n : ℝ) →
    weight x < weight (R.toLinear x)

/-- Actual finite graph/padding data. Output casts preserve order and weight. -/
structure PaddedSource (d T out : Nat) where
  vertices : Nat
  graph : ExpanderWalk.PortGraph vertices d
  input_capacity : T ≤ vertices * d
  output_capacity : vertices * (d / 4) ≤ T / 2
  output_eq : T / 2 = out

def PaddedSource.linear {d T out : Nat} (S : PaddedSource d T out)
    (A : Word (d + d) →ₗ[F] Word (d / 4)) : Word T →ₗ[F] Word out :=
  (castWord S.output_eq).comp
    (paddedAmplifier S.graph S.input_capacity S.output_capacity A)

/-- Exact square-padding source constructor. Divisibility is used before
rounding, and all capacities are derived rather than silently floor-rounded. -/
def PaddedSource.ofSquare {d T out s : Nat}
    (G : ExpanderWalk.PortGraph (s * s) d)
    (hd : 0 < d) (hd4 : 4 ∣ d) (hdiv : d ∣ T) (hlarge : 8 * d ≤ T)
    (hcover : T / d ≤ s * s) (hminimal : (s - 1) * (s - 1) < T / d)
    (hout : T / 2 = out) : PaddedSource d T out := by
  have hb := square_padding_bounds (d := d) hd hdiv hlarge hcover hminimal
  have hin : T ≤ (s * s) * d := by simpa only [Nat.mul_comm] using hb.2.1
  have hM : (s * s) * d ≤ 2 * T := by simpa only [Nat.mul_comm] using hb.2.2
  exact ⟨s * s, G, hin, (parity_capacity hd4 hM).2, hout⟩

/-- Concrete binding of the already derived padded sparse theorem. The only
semantic premise identifies this program with the defined padded linear map. -/
theorem sparseSpec_of_padded {d T out : Nat} (P : XorProgram T out)
    (S : PaddedSource d T out) (A : Word (d + d) →ₗ[F] Word (d / 4))
    (hprogram : P.toLinear = S.linear A)
    (hlocal : ∀ z : Word (d + d), z ≠ 0 →
      (d : ℝ) / 256 ≤ (weight z : ℝ) + (weight (A z) : ℝ))
    (hspectral : ∀ f : ExpanderWalk.RVec S.vertices, (∑ v, f v) = 0 →
      ExpanderWalk.dot f (S.graph.transition f) ≤
        (1 / 4096 : ℝ) * ExpanderWalk.energy f) : SparseSpec P := by
  intro x hx hs
  rw [hprogram]
  change weight x < weight (castWord S.output_eq
    (paddedAmplifier S.graph S.input_capacity S.output_capacity A x))
  rw [weight_castWord]
  exact padded_sparse_amplification S.graph S.input_capacity S.output_capacity A
    hlocal (by norm_num) (by norm_num) hspectral x hx hs

/-! The fixed base: exactly eight local systematic words and padded zeros. -/

def localBlock {k : Nat} (x : Word (8 * k)) (v : Fin 8) : Word k :=
  fun i => x (finProdFinEquiv (v, i))

def eightParity {k h : Nat} (A : Word k →ₗ[F] Word h) :
    Word (8 * k) →ₗ[F] Word (8 * h) where
  toFun x j := A (localBlock x (finProdFinEquiv.symm j).1)
    (finProdFinEquiv.symm j).2
  map_add' x y := by
    funext j
    change A (localBlock x _ + localBlock y _) _ = _
    simp only [map_add, Pi.add_apply]
  map_smul' c x := by
    funext j
    change A (c • localBlock x _) _ = _
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

def eightBase {k h : Nat} (A : Word k →ₗ[F] Word h) (zeros : Nat) :
    Word (8 * k) →ₗ[F] Word (8 * k + (8 * h + zeros)) where
  toFun x := Fin.append x (Fin.append (eightParity A x) (0 : Word zeros))
  map_add' x y := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [map_add]
  map_smul' c x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [map_smul]

theorem input_weight_blocks {k : Nat} (x : Word (8 * k)) :
    weight x = ∑ v : Fin 8, weight (localBlock x v) := by
  calc
    weight x = supportWeight (fun p : Fin 8 × Fin k => x (finProdFinEquiv p)) :=
      ((supportWeight_equiv finProdFinEquiv x).trans (supportWeight_fin x)).symm
    _ = ∑ v : Fin 8, weight (localBlock x v) := supportWeight_prod _

theorem parity_weight_blocks {k h : Nat} (A : Word k →ₗ[F] Word h)
    (x : Word (8 * k)) :
    weight (eightParity A x) = ∑ v : Fin 8, weight (A (localBlock x v)) := by
  rw [← supportWeight_fin,
    ← supportWeight_equiv (finProdFinEquiv : (Fin 8 × Fin h) ≃ Fin (8 * h)),
    supportWeight_prod]
  simp only [eightParity, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply]

theorem eightBase_weight {k h : Nat} (A : Word k →ₗ[F] Word h)
    (zeros : Nat) (x : Word (8 * k)) :
    weight (eightBase A zeros x) =
      ∑ v : Fin 8, (weight (localBlock x v) + weight (A (localBlock x v))) := by
  change weight (Fin.append x (Fin.append (eightParity A x) (0 : Word zeros))) = _
  rw [weight_append, weight_append_zero, input_weight_blocks, parity_weight_blocks,
    Finset.sum_add_distrib]

theorem nonzero_localBlock {k : Nat} (x : Word (8 * k)) (hx : x ≠ 0) :
    ∃ v : Fin 8, localBlock x v ≠ 0 := by
  by_contra h
  push_neg at h
  apply hx
  funext i
  have hi := congrFun (h (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2
  change x (finProdFinEquiv (finProdFinEquiv.symm i)) = 0 at hi
  change x i = 0
  simpa only [Equiv.apply_symm_apply] using hi

theorem eightBase_distance {k h : Nat} (A : Word k →ₗ[F] Word h)
    (zeros : Nat) (r : ℝ)
    (hlocal : ∀ z : Word k, z ≠ 0 → r ≤ (weight z : ℝ) + (weight (A z) : ℝ))
    (x : Word (8 * k)) (hx : x ≠ 0) : r ≤ (weight (eightBase A zeros x) : ℝ) := by
  classical
  obtain ⟨v, hv⟩ := nonzero_localBlock x hx
  have hsum : weight (localBlock x v) + weight (A (localBlock x v)) ≤
      ∑ j : Fin 8, (weight (localBlock x j) + weight (A (localBlock x j))) :=
    Finset.single_le_sum (f := fun j : Fin 8 =>
      weight (localBlock x j) + weight (A (localBlock x j)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have hs : (weight (localBlock x v) : ℝ) + (weight (A (localBlock x v)) : ℝ) ≤
      (weight (eightBase A zeros x) : ℝ) := by
    rw [eightBase_weight]
    exact_mod_cast hsum
  exact (hlocal _ hv).trans hs

theorem base_input_dim (d : Nat) : 16 * d = 8 * (d + d) := by omega

theorem base_output_dim {d : Nat} (hd : 4 ∣ d) :
    8 * (d + d) + (8 * (d / 4) + 46 * d) = 64 * d := by
  have he := Nat.div_mul_cancel hd
  omega

/-- All original inputs first, then eight parity blocks, then 46d zeros. -/
def localBase {d : Nat} (hd : 4 ∣ d)
    (A : Word (d + d) →ₗ[F] Word (d / 4)) : Word (16 * d) →ₗ[F] Word (64 * d) :=
  (castWord (base_output_dim hd)).comp
    ((eightBase A (46 * d)).comp (castWord (base_input_dim d)))

theorem localBase_distance {d : Nat} (hd : 4 ∣ d)
    (A : Word (d + d) →ₗ[F] Word (d / 4))
    (hlocal : ∀ z : Word (d + d), z ≠ 0 →
      (d : ℝ) / 256 ≤ (weight z : ℝ) + (weight (A z) : ℝ))
    (x : Word (16 * d)) (hx : x ≠ 0) :
    (d : ℝ) / 256 ≤ (weight (localBase hd A x) : ℝ) := by
  have hx' : castWord (base_input_dim d) x ≠ 0 := by
    intro hz
    apply hx
    exact castWord_injective _ (hz.trans (map_zero _).symm)
  change (d : ℝ) / 256 ≤ (weight (castWord (base_output_dim hd)
    (eightBase A (46 * d) (castWord (base_input_dim d) x))) : ℝ)
  rw [weight_castWord]
  exact eightBase_distance A _ _ hlocal _ hx'

theorem localBase_systematic {d : Nat} (hd : 4 ∣ d)
    (A : Word (d + d) →ₗ[F] Word (d / 4))
    (x : Word (16 * d)) (i : Fin (16 * d)) :
    localBase hd A x ⟨i.val, by omega⟩ = x i := by
  let j : Fin (8 * (d + d)) := Fin.cast (base_input_dim d) i
  have hidx : Fin.cast (base_output_dim hd).symm
      (⟨i.val, by omega⟩ : Fin (64 * d)) = Fin.castAdd (8 * (d / 4) + 46 * d) j := by
    apply Fin.ext
    rfl
  change eightBase A (46 * d) (castWord (base_input_dim d) x)
    (Fin.cast (base_output_dim hd).symm ⟨i.val, by omega⟩) = x i
  rw [hidx]
  change (Fin.append (castWord (base_input_dim d) x)
    (Fin.append (eightParity A (castWord (base_input_dim d) x)) (0 : Word (46 * d))))
      (Fin.castAdd (8 * (d / 4) + 46 * d) j) = x i
  simp only [Fin.append_left]
  rfl

end EncoderSemantics

namespace SerializedDyadicEncoder
open EncoderSemantics

theorem messageWidth_dvd (D ell : Nat) : D ∣ messageWidth D ell := by
  rw [messageWidth_formula]
  exact ⟨16 * 2 ^ ell, by ring⟩

theorem messageWidth_ge_base (D ell : Nat) : 16 * D ≤ messageWidth D ell := by
  induction ell with
  | zero => rfl
  | succ ell ih => simp only [messageWidth]; omega

/-- The two actual amplifier lengths meet the exact divisibility/size inputs.
At the first recursive step, R₁ has 32D inputs, not an undersized base case. -/
theorem amplifier_dimensions (D ell : Nat) :
    D ∣ 2 * messageWidth D ell ∧ D ∣ 4 * messageWidth D ell ∧
    32 * D ≤ 2 * messageWidth D ell ∧ 64 * D ≤ 4 * messageWidth D ell ∧
    (2 * messageWidth D ell) / 2 = messageWidth D ell ∧
    (4 * messageWidth D ell) / 2 = 2 * messageWidth D ell := by
  obtain ⟨k, hk⟩ := messageWidth_dvd D ell
  have hw := messageWidth_ge_base D ell
  refine ⟨⟨2 * k, by rw [hk]; ring⟩, ⟨4 * k, by rw [hk]; ring⟩, ?_⟩
  omega

theorem successor_dimensions (D ell : Nat) :
    let N := (64 * D) * 2 ^ (ell + 1)
    N / 4 = 2 * messageWidth D ell ∧
    N / 8 = messageWidth D ell ∧
    N / 2 = 4 * messageWidth D ell ∧
    8 ∣ N := by
  dsimp
  have hN : (64 * D) * 2 ^ (ell + 1) = 8 * messageWidth D ell := by
    rw [messageWidth_formula, pow_succ]
    ring
  rw [hN]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · exact dvd_mul_right 8 _

theorem base_encoder_output_dim (D : Nat) : 64 * D = 4 * messageWidth D 0 := by
  simp only [messageWidth]
  omega

/-- Same eight-block base, with the constructor's exact output dimension. -/
def baseForEncoder {D : Nat} (hD4 : 4 ∣ D)
    (A : Word (D + D) →ₗ[F] Word (D / 4)) :
    Word (messageWidth D 0) →ₗ[F] Word (4 * messageWidth D 0) :=
  (castWord (base_encoder_output_dim D)).comp (localBase hD4 A)

theorem baseForEncoder_weight {D : Nat} (hD4 : 4 ∣ D)
    (A : Word (D + D) →ₗ[F] Word (D / 4)) (x : Word (messageWidth D 0)) :
    weight (baseForEncoder hD4 A x) = weight (localBase hD4 A x) := by
  change weight (castWord (base_encoder_output_dim D) (localBase hD4 A x)) = _
  exact weight_castWord _ _

theorem baseForEncoder_distance {D : Nat} (hD4 : 4 ∣ D)
    (A : Word (D + D) →ₗ[F] Word (D / 4))
    (hlocal : ∀ z : Word (D + D), z ≠ 0 →
      (D : ℝ) / 256 ≤ (weight z : ℝ) + (weight (A z) : ℝ))
    (x : Word (messageWidth D 0)) (hx : x ≠ 0) :
    alpha * ((4 * messageWidth D 0 : Nat) : ℝ) ≤
      (weight (baseForEncoder hD4 A x) : ℝ) := by
  rw [baseForEncoder_weight]
  have hbase := localBase_distance hD4 A hlocal x hx
  have hDnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  rw [← base_encoder_output_dim]
  push_cast
  dsimp [alpha]
  nlinarith

theorem baseForEncoder_systematic {D : Nat} (hD4 : 4 ∣ D)
    (A : Word (D + D) →ₗ[F] Word (D / 4))
    (x : Word (messageWidth D 0)) (i : Fin (messageWidth D 0)) :
    baseForEncoder hD4 A x ⟨i.val, by omega⟩ = x i := by
  have hidx : Fin.cast (base_encoder_output_dim D).symm
      (⟨i.val, by omega⟩ : Fin (4 * messageWidth D 0)) =
      (⟨i.val, by simpa only [messageWidth] using (show i.val < 64 * D by
        have hi := i.isLt
        simp only [messageWidth] at hi
        omega)⟩ : Fin (64 * D)) := by
    apply Fin.ext
    rfl
  change localBase hD4 A x
    (Fin.cast (base_encoder_output_dim D).symm ⟨i.val, by omega⟩) = x i
  rw [hidx]
  exact localBase_systematic hD4 A x i

variable {D : Nat}
  (base : XorProgram (messageWidth D 0) (4 * messageWidth D 0))
  (R₁ : (ell : Nat) → XorProgram (2 * messageWidth D ell) (messageWidth D ell))
  (R₂ : (ell : Nat) → XorProgram (4 * messageWidth D ell) (2 * messageWidth D ell))

/-- Exact disjoint output-position weight identity for the SAME constructor.
Aliased wire values do not cancel: outputs are concatenated, never added. -/
theorem encoder_weight_step (ell : Nat) (x : Word (messageWidth D (ell + 1))) :
    weight ((encoder base R₁ R₂ (ell + 1)).toLinear x) =
      weight x + (weight ((encoder base R₁ R₂ ell).toLinear ((R₁ ell).toLinear x)) +
        weight ((R₂ ell).toLinear ((encoder base R₁ R₂ ell).toLinear ((R₁ ell).toLinear x)))) := by
  simp only [encoder, XorProgram.outputCast_linear, weight_castWord]
  have h := congrArg (fun y => weight y)
    (XorProgram.oneCopy_linear (R₁ ell) (encoder base R₁ R₂ ell) (R₂ ell) x)
  exact h.trans ((weight_append x
    (Fin.append ((encoder base R₁ R₂ ell).toLinear ((R₁ ell).toLinear x))
      ((R₂ ell).toLinear ((encoder base R₁ R₂ ell).toLinear ((R₁ ell).toLinear x))))).trans
    (congrArg (fun z => weight x + z)
      (weight_append ((encoder base R₁ R₂ ell).toLinear ((R₁ ell).toLinear x))
        ((R₂ ell).toLinear ((encoder base R₁ R₂ ell).toLinear ((R₁ ell).toLinear x))))))

theorem encoder_step_systematic (ell : Nat)
    (x : Word (messageWidth D (ell + 1))) (i : Fin (messageWidth D (ell + 1))) :
    (encoder base R₁ R₂ (ell + 1)).toLinear x ⟨i.val, by omega⟩ = x i := by
  let hdim : 2 * messageWidth D ell +
      (4 * messageWidth D ell + 2 * messageWidth D ell) =
      4 * messageWidth D (ell + 1) := by simp only [messageWidth]; omega
  have hidx : Fin.cast hdim.symm (⟨i.val, by omega⟩ : Fin (4 * messageWidth D (ell + 1))) =
      Fin.castAdd (4 * messageWidth D ell + 2 * messageWidth D ell) i := by
    apply Fin.ext
    rfl
  change castWord hdim ((XorProgram.oneCopy (R₁ ell)
      (encoder base R₁ R₂ ell) (R₂ ell)).toLinear x) ⟨i.val, by omega⟩ = x i
  change (XorProgram.oneCopy (R₁ ell) (encoder base R₁ R₂ ell) (R₂ ell)).toLinear x
    (Fin.cast hdim.symm ⟨i.val, by omega⟩) = x i
  rw [XorProgram.oneCopy_linear, hidx, Fin.append_left]

theorem encoder_systematic
    (hbase : ∀ x : Word (messageWidth D 0), ∀ i : Fin (messageWidth D 0),
      base.toLinear x ⟨i.val, by omega⟩ = x i)
    (ell : Nat) (x : Word (messageWidth D ell)) (i : Fin (messageWidth D ell)) :
    (encoder base R₁ R₂ ell).toLinear x ⟨i.val, by omega⟩ = x i := by
  cases ell with
  | zero => exact hbase x i
  | succ ell => exact encoder_step_systematic base R₁ R₂ ell x i

theorem encoder_injective
    (hbase : ∀ x : Word (messageWidth D 0), ∀ i : Fin (messageWidth D 0),
      base.toLinear x ⟨i.val, by omega⟩ = x i)
    (ell : Nat) : Function.Injective (encoder base R₁ R₂ ell).toLinear := by
  intro x y hxy
  funext i
  have h := congrFun hxy (⟨i.val, by omega⟩ : Fin (4 * messageWidth D ell))
  simpa only [encoder_systematic base R₁ R₂ hbase] using h

/-- Distance induction on the actual one-copy circuit. The first amplifier's
strict inequality establishes a NONZERO recursive input; it is not assumed.
Boundary equality belongs to the sparse case at both thresholds. -/
theorem encoder_distance
    (hD : 0 < D)
    (hbase : ∀ x : Word (messageWidth D 0), x ≠ 0 →
      alpha * ((4 * messageWidth D 0 : Nat) : ℝ) ≤ (weight (base.toLinear x) : ℝ))
    (hR₁ : ∀ ell, SparseSpec (R₁ ell))
    (hR₂ : ∀ ell, SparseSpec (R₂ ell))
    (ell : Nat) (x : Word (messageWidth D ell)) (hx : x ≠ 0) :
    alpha * ((4 * messageWidth D ell : Nat) : ℝ) ≤
      (weight ((encoder base R₁ R₂ ell).toLinear x) : ℝ) := by
  induction ell with
  | zero => exact hbase x hx
  | succ ell ih =>
    let w := messageWidth D ell
    let a := (R₁ ell).toLinear x
    let H := (encoder base R₁ R₂ ell).toLinear a
    let Z := (R₂ ell).toLinear H
    have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg _
    have hxpos := weight_pos_of_ne_zero hx
    have htarget : alpha * ((4 * messageWidth D (ell + 1) : Nat) : ℝ) =
        alpha * (8 * (w : ℝ)) := by
      change alpha * ((4 * (2 * w) : Nat) : ℝ) = _
      push_cast
      ring
    rw [htarget, encoder_weight_step]
    change alpha * (8 * (w : ℝ)) ≤ ((weight x + (weight H + weight Z) : Nat) : ℝ)
    push_cast
    by_cases hxsmall : (weight x : ℝ) ≤ theta * ((2 * w : Nat) : ℝ)
    · have haGrow : weight x < weight a := hR₁ ell x hxpos hxsmall
      have hapos : 0 < weight a := lt_trans hxpos haGrow
      have hane : a ≠ 0 := ne_zero_of_weight_pos hapos
      have hIH := ih a hane
      change alpha * ((4 * w : Nat) : ℝ) ≤ (weight H : ℝ) at hIH
      push_cast at hIH
      by_cases hHsmall : (weight H : ℝ) ≤ theta * ((4 * w : Nat) : ℝ)
      · have hHpos : 0 < weight H := by
          have hwpos : 0 < w := messageWidth_pos hD ell
          have hwreal : (0 : ℝ) < w := by exact_mod_cast hwpos
          have hhreal : (0 : ℝ) < weight H :=
            lt_of_lt_of_le (mul_pos alpha_pos (by positivity)) hIH
          exact_mod_cast hhreal
        have hZGrow : weight H < weight Z := hR₂ ell H hHpos hHsmall
        have hZG : (weight H : ℝ) < (weight Z : ℝ) := by exact_mod_cast hZGrow
        have hxnonneg : (0 : ℝ) ≤ weight x := Nat.cast_nonneg _
        nlinarith
      · have hlarge : theta * (4 * (w : ℝ)) < (weight H : ℝ) := by
          push_cast at hHsmall
          exact lt_of_not_ge hHsmall
        have htheta := mul_le_mul_of_nonneg_right two_alpha_le_theta
          (show (0 : ℝ) ≤ 4 * (w : ℝ) by positivity)
        have hxnonneg : (0 : ℝ) ≤ weight x := Nat.cast_nonneg _
        have hznonneg : (0 : ℝ) ≤ weight Z := Nat.cast_nonneg _
        nlinarith
    · have hlarge : theta * (2 * (w : ℝ)) < (weight x : ℝ) := by
        push_cast at hxsmall
        exact lt_of_not_ge hxsmall
      have htheta := mul_le_mul_of_nonneg_right four_alpha_le_theta
        (show (0 : ℝ) ≤ 2 * (w : ℝ) by positivity)
      have hHnonneg : (0 : ℝ) ≤ weight H := Nat.cast_nonneg _
      have hZnonneg : (0 : ℝ) ≤ weight Z := Nat.cast_nonneg _
      nlinarith

/-- Final source-level closure with no assumed amplifier or encoder distance:
the maps being compiled are the defined base and padded-amplifier maps. -/
theorem encoder_distance_from_local_and_padded
    (hD : 0 < D) (hD4 : 4 ∣ D)
    (A : Word (D + D) →ₗ[F] Word (D / 4))
    (hlocal : ∀ z : Word (D + D), z ≠ 0 →
      (D : ℝ) / 256 ≤ (weight z : ℝ) + (weight (A z) : ℝ))
    (hbase : base.toLinear = baseForEncoder hD4 A)
    (S₁ : (ell : Nat) → PaddedSource D (2 * messageWidth D ell) (messageWidth D ell))
    (S₂ : (ell : Nat) → PaddedSource D (4 * messageWidth D ell) (2 * messageWidth D ell))
    (hcompile₁ : ∀ ell, (R₁ ell).toLinear = (S₁ ell).linear A)
    (hcompile₂ : ∀ ell, (R₂ ell).toLinear = (S₂ ell).linear A)
    (hspectral₁ : ∀ ell, ∀ f : ExpanderWalk.RVec (S₁ ell).vertices,
      (∑ v, f v) = 0 → ExpanderWalk.dot f ((S₁ ell).graph.transition f) ≤
        (1 / 4096 : ℝ) * ExpanderWalk.energy f)
    (hspectral₂ : ∀ ell, ∀ f : ExpanderWalk.RVec (S₂ ell).vertices,
      (∑ v, f v) = 0 → ExpanderWalk.dot f ((S₂ ell).graph.transition f) ≤
        (1 / 4096 : ℝ) * ExpanderWalk.energy f)
    (ell : Nat) (x : Word (messageWidth D ell)) (hx : x ≠ 0) :
    alpha * (((64 * D) * 2 ^ ell : Nat) : ℝ) ≤
      (weight ((encoder base R₁ R₂ ell).toLinear x) : ℝ) := by
  rw [← codeLength_formula]
  apply encoder_distance base R₁ R₂ hD
  · intro x hx
    rw [hbase]
    exact baseForEncoder_distance hD4 A hlocal x hx
  · intro j
    exact sparseSpec_of_padded (R₁ j) (S₁ j) A (hcompile₁ j) hlocal (hspectral₁ j)
  · intro j
    exact sparseSpec_of_padded (R₂ j) (S₂ j) A (hcompile₂ j) hlocal (hspectral₂ j)
  · exact hx

/-- Input and output casts do not change the exact constructor's linear map,
except for the displayed dimension transports. -/
theorem exactEncoder_linear (ell : Nat)
    (x : Word (((64 * D) * 2 ^ ell) / 4)) :
    (exactEncoder base R₁ R₂ ell).toLinear x =
      castWord (codeLength_formula D ell)
        ((encoder base R₁ R₂ ell).toLinear
          (castWord (messageWidth_div_four D ell).symm x)) := by
  simp only [exactEncoder, XorProgram.outputCast_linear, XorProgram.inputCast_linear]

theorem exactEncoder_distance
    (hD : 0 < D)
    (hbase : ∀ x : Word (messageWidth D 0), x ≠ 0 →
      alpha * ((4 * messageWidth D 0 : Nat) : ℝ) ≤ (weight (base.toLinear x) : ℝ))
    (hR₁ : ∀ ell, SparseSpec (R₁ ell))
    (hR₂ : ∀ ell, SparseSpec (R₂ ell))
    (ell : Nat) (x : Word (((64 * D) * 2 ^ ell) / 4)) (hx : x ≠ 0) :
    alpha * (((64 * D) * 2 ^ ell : Nat) : ℝ) ≤
      (weight ((exactEncoder base R₁ R₂ ell).toLinear x) : ℝ) := by
  rw [exactEncoder_linear, weight_castWord]
  have hcast : castWord (messageWidth_div_four D ell).symm x ≠ 0 := by
    intro hz
    apply hx
    exact castWord_injective _ (hz.trans (map_zero _).symm)
  have h := encoder_distance base R₁ R₂ hD hbase hR₁ hR₂ ell
    (castWord (messageWidth_div_four D ell).symm x) hcast
  have hnum : alpha * (((64 * D) * 2 ^ ell : Nat) : ℝ) =
      alpha * ((4 * messageWidth D ell : Nat) : ℝ) := by
    rw [codeLength_formula]
  exact hnum.trans_le h

/-- Natural-integer target distances may be chosen below αN; no real floor is
silently substituted for the exact distance threshold. -/
theorem exactEncoder_distanceAtLeast
    (hD : 0 < D)
    (hbase : ∀ x : Word (messageWidth D 0), x ≠ 0 →
      alpha * ((4 * messageWidth D 0 : Nat) : ℝ) ≤ (weight (base.toLinear x) : ℝ))
    (hR₁ : ∀ ell, SparseSpec (R₁ ell))
    (hR₂ : ∀ ell, SparseSpec (R₂ ell))
    (ell r : Nat) (hr : (r : ℝ) ≤ alpha * (((64 * D) * 2 ^ ell : Nat) : ℝ)) :
    DistanceAtLeast (exactEncoder base R₁ R₂ ell).toLinear r := by
  intro x hx
  have h := hr.trans (exactEncoder_distance base R₁ R₂ hD hbase hR₁ hR₂ ell x hx)
  exact_mod_cast h

/-- The same bound for the Boolean evaluation of the actual exact-size DAG. -/
theorem exactEncoder_boolean_distance
    (hD : 0 < D)
    (hbase : ∀ x : Word (messageWidth D 0), x ≠ 0 →
      alpha * ((4 * messageWidth D 0 : Nat) : ℝ) ≤ (weight (base.toLinear x) : ℝ))
    (hR₁ : ∀ ell, SparseSpec (R₁ ell))
    (hR₂ : ∀ ell, SparseSpec (R₂ ell))
    (ell : Nat) (x : BitModels (((64 * D) * 2 ^ ell) / 4)) (hx : bitsVector x ≠ 0) :
    alpha * (((64 * D) * 2 ^ ell : Nat) : ℝ) ≤
      (weight (bitsVector ((exactEncoder base R₁ R₂ ell).toProgram.eval x)) : ℝ) := by
  rw [← XorProgram.toLinear_bool]
  exact exactEncoder_distance base R₁ R₂ hD hbase hR₁ hR₂ ell (bitsVector x) hx

/-- Systematicity and injectivity of the actual encoder from the concrete
eight-local-code base compiler equality, independently of spectral distance. -/
theorem encoder_injective_from_localBase (hD4 : 4 ∣ D)
    (A : Word (D + D) →ₗ[F] Word (D / 4))
    (hbase : base.toLinear = baseForEncoder hD4 A) (ell : Nat) :
    Function.Injective (encoder base R₁ R₂ ell).toLinear := by
  apply encoder_injective base R₁ R₂
  intro x i
  rw [hbase]
  exact baseForEncoder_systematic hD4 A x i

theorem exactEncoder_injective_from_localBase (hD4 : 4 ∣ D)
    (A : Word (D + D) →ₗ[F] Word (D / 4))
    (hbase : base.toLinear = baseForEncoder hD4 A) (ell : Nat) :
    Function.Injective (exactEncoder base R₁ R₂ ell).toLinear := by
  intro x y hxy
  simp only [exactEncoder_linear] at hxy
  have hout := castWord_injective (codeLength_formula D ell) hxy
  have hin := encoder_injective_from_localBase base R₁ R₂ hD4 A hbase ell hout
  exact castWord_injective (messageWidth_div_four D ell).symm hin

/-- The distance theorem does not introduce a second recursive H circuit.
This restates the wiring module's exact *same-constructor* gate recurrence. -/
theorem distance_encoder_one_copy_gates (ell : Nat) :
    (encoder base R₁ R₂ (ell + 1)).gates =
      (R₁ ell).gates + (encoder base R₁ R₂ ell).gates + (R₂ ell).gates :=
  encoder_step_gates base R₁ R₂ ell

def fixedDegree : Nat := 16 ^ 384

theorem fixedDegree_pos : 0 < fixedDegree := pow_pos (by decide) _

theorem fixedDegree_divisible : 256 ∣ fixedDegree := by
  refine ⟨16 ^ 382, ?_⟩
  change 16 ^ 384 = 256 * 16 ^ 382
  calc
    16 ^ 384 = 16 ^ (2 + 382) := rfl
    _ = 16 ^ 2 * 16 ^ 382 := pow_add _ _ _
    _ = 256 * 16 ^ 382 := by norm_num only [show (16 : Nat) ^ 2 = 256 by decide]

theorem fixedDegree_four : 4 ∣ fixedDegree :=
  dvd_trans (by decide : 4 ∣ 256) fixedDegree_divisible

end SerializedDyadicEncoder
end QecReliability.SharedCircuit
