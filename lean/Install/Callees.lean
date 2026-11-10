import Install.Remaining
import Trans.BoundsRest.Compile
import Trans.BoundsRest.Endpoint

/-!
# Install.Callees: the compile and endpoint parts of `RemainingBounds`

From `Trans/BoundsRest` (`compile_envelope`, `reach_arg_mag_le`, `endpoint_budget`) and
`Trans/BoundsEnc` (`hash_concrete_bound`, with the data-independent callees of the concrete
`HashCallees` record `hC` bounded by the `BoundsQH` lemmas):

* `theHash_bound`: the instance's hash program is `FnBAt (G K C)` at every
  `(base, den, q, r, bits)`;
* `compileBound_exists`: one envelope for the compile wrapper at every reachable state of
  every positive instance (uniform in the SAT machine);
* `endpointBound_exists`: one envelope for the endpoint wrapper;
* `calleeBounds_exist`: one common envelope for both (`CompileBound ∧ EndpointBound`).
-/

set_option autoImplicit false

noncomputable section
namespace QecReliability.Install
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.BoundsQH (G FnBAt PolyB)
open QecReliability.Trans.Hash (gNbr)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

/-! ## Envelopes -/

/-- An envelope dominating two envelopes. -/
def envMax (P Q : PolynomialEnvelope) : PolynomialEnvelope :=
  ⟨P.coefficient + Q.coefficient, P.degree + Q.degree⟩

theorem envMax_left (P Q : PolynomialEnvelope) (L : ℕ) : P.eval L ≤ (envMax P Q).eval L := by
  unfold envMax PolynomialEnvelope.eval
  exact Nat.mul_le_mul (Nat.le_add_right _ _)
    (Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_add_right _ _))

theorem envMax_right (P Q : PolynomialEnvelope) (L : ℕ) : Q.eval L ≤ (envMax P Q).eval L := by
  unfold envMax PolynomialEnvelope.eval
  exact Nat.mul_le_mul (Nat.le_add_left _ _)
    (Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_add_left _ _))

/-! ## The hash callees are polynomially bounded -/

theorem tg_P : PolyB (pcI.tgF hL) :=
  Trans.BoundsQH.tabGatesF_P (Trans.BoundsQH.twF_P _ _ _ _ _) (fun _ => rfl) _ _

theorem twl_P : PolyB (pcI.twlF hL) := Trans.BoundsQH.tabWiresF_P (Trans.BoundsQH.twF_P _ _ _ _ _) _

theorem twl_den' (x : (Ty.prod Trans.Hash.TTab (.list .nat)).den) :
    (pcI.twlF hL).den x = Trans.Hash.tabWires x.1 x.2 :=
  Trans.Hash.tabWiresF_den _ _ (fun _ => rfl) x.1 x.2

theorem aw_P : PolyB awF :=
  Trans.BoundsQH.addWireF_P (Trans.BoundsQH.getD0F_P _ _) (fun _ => rfl)
    (Trans.BoundsQH.hsetF_P _ _ _ _ _) (fun _ => rfl) _

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t) (A : CertifiedParity (512*t) (64*t) t)
  (density : ℕ)

/-- **The instance's hash program is polynomially bounded** at the instance constants. -/
theorem theHash_bound : ∃ K C', ∀ q r bits,
    FnBAt (G K C') (theHash hD hd A) ((data hD hd A).base, (data hD hd A).den, q, r, bits) := by
  have hb : 1 ≤ (data hD hd A).base :=
    le_trans (by omega) (base_ge_eight hD hd A)
  obtain ⟨kp, cp, hp⟩ := Trans.BoundsQH.paramsF_on hL.range hL.mul hL.le hL.succ hL.mul I.dyS
    I.dyF hL.le hL.succ hL.mul ampI.cs ampI.csf hL.mul I.pwS I.pwF I.params
    (data hD hd A).base (data hD hd A).den
  exact Trans.BoundsEnc.hash_concrete_bound hD hd A hL encI rotI I.nbr I.vis I.visF I.encIdx
    I.encMap (hC (Trans.HashCallees.encConsts D A) (gNbr actualMGG)) rfl rfl I.hash _ _ hb hp
    (fun _ => rfl)
    (Trans.BoundsQH.padF_P (Trans.BoundsQH.mapEnvH_P (Trans.BoundsQH.minF_P (i := iMin)) _) (fun _ => rfl)
      tg_P twl_P (fun _ => rfl) twl_den' _)
    (Trans.BoundsQH.pselectF_P _)
    (Trans.BoundsQH.affF_P (Trans.BoundsQH.abitF_P _ _ _ _ _ _ _) (fun _ => rfl) tg_P twl_P
      (fun _ => rfl) twl_den' _ _ _ _)
    (Trans.BoundsQH.seedRowsF_P (Trans.BoundsQH.rowF_P _ _ _ _ _ _ _) (fun _ => rfl) _)
    (Trans.BoundsQH.transF_P aw_P (fun _ => rfl) (Trans.BoundsQH.dropLastF_P _ _ _ _)
      (fun _ => rfl) (Trans.BoundsQH.getD0F_P _ _) (fun _ => rfl) _ _ _ _ _)
    (Trans.BoundsQH.pcomposeF_P tg_P twl_P (fun _ => rfl) twl_den' _)
    (Trans.BoundsQH.divModF_P hL.le hL.sub hL.dm)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)

/-- **Compile wrapper**: one envelope at every reachable state, uniformly in the SAT machine. -/
theorem compileBound_exists : ∃ P : PolynomialEnvelope, CompileBound hD hd A density P P P := by
  obtain ⟨K, C', hH⟩ := theHash_bound hD hd A
  obtain ⟨P, hP⟩ := Trans.BoundsRest.compile_envelope wL wC (theHash hD hd A) (data hD hd A).base
    (data hD hd A).den density (seedConstant hD hd A) hH
  refine ⟨P, ?_⟩
  intro kE ΓE ΛE _ _ _ E PtE PsE T spec _ a b c d k rows coins ha _ hc _ s hs
  exact hP _ _ (Trans.BoundsRest.reach_arg_mag_le hD hd A spec rows coins ha hc hs)

/-- **Endpoint wrapper**: one envelope for every instance and side. -/
theorem endpointBound_exists : ∃ P : PolynomialEnvelope, EndpointBound hD hd A P P P := by
  obtain ⟨P, hP⟩ := Trans.BoundsRest.endpoint_budget hD hd A wC yR
  exact ⟨P, fun a b c d k rows coins side ha _ hc _ =>
    hP (theCX hD hd A 0) rfl rows coins ha hc side⟩

theorem compileBound_mono {P Q : PolynomialEnvelope} (hPQ : ∀ L, P.eval L ≤ Q.eval L)
    (h : CompileBound hD hd A density P P P) : CompileBound hD hd A density Q Q Q := by
  intro kE ΓE ΛE _ _ _ E PtE PsE T spec hT a b c d k rows coins ha hab hc hd' s hs
  obtain ⟨h1, h2, h3⟩ := h E PtE PsE T spec hT a b c d k rows coins ha hab hc hd' s hs
  have := hPQ (paperL rows a b c d)
  exact ⟨h1.trans this, h2.trans this, h3.trans this⟩

theorem endpointBound_mono {P Q : PolynomialEnvelope} (hPQ : ∀ L, P.eval L ≤ Q.eval L)
    (h : EndpointBound hD hd A P P P) : EndpointBound hD hd A Q Q Q := by
  intro a b c d k rows coins side ha hab hc hd'
  obtain ⟨h1, h2, h3⟩ := h a b c d k rows coins side ha hab hc hd'
  have := hPQ (paperL rows a b c d)
  exact ⟨h1.trans this, h2.trans this, h3.trans this⟩

/-- **Both callees within one envelope.** -/
theorem calleeBounds_exist : ∃ P : PolynomialEnvelope,
    CompileBound hD hd A density P P P ∧ EndpointBound hD hd A P P P := by
  obtain ⟨P1, h1⟩ := compileBound_exists hD hd A density
  obtain ⟨P2, h2⟩ := endpointBound_exists hD hd A
  exact ⟨envMax P1 P2, compileBound_mono hD hd A density (envMax_left P1 P2) h1,
    endpointBound_mono hD hd A (envMax_right P1 P2) h2⟩

/-- The init part of the remaining bounds. -/
def InitBounds : Prop :=
  ∃ Ci Di Mi : PolynomialEnvelope, InitBound hD hd A Ci Di Mi ∧ InitZeroBound hD hd A Ci Di Mi

/-- **`RemainingBounds` from the init bounds alone.** -/
theorem remaining_of_init (h : InitBounds hD hd A) : RemainingBounds hD hd A density := by
  obtain ⟨Ci, Di, Mi, hi, hz⟩ := h
  obtain ⟨P, hc, he⟩ := calleeBounds_exist hD hd A density
  exact ⟨P, P, P, Ci, Di, Mi, hc, he, hi, hz⟩

end QecReliability.Install

end
