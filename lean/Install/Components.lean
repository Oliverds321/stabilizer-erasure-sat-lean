import Install.OK
import Install.Remaining
import Trans.BoundsStep.Envelope

/-!
# Install.Components: the component bundle from the remaining bounds

* `theHash_ok`: the instance's hash program is valid in `theProg` (oracle meanings from
  `Trans.HashCallees`: `encProg_dataProgram`, `nbrF_den`, `four_le_degree`);
* `positive_of`: `Assembly.PositiveFacts` for every positive instance with
  `enc = Trans.Wire.instEnc …`, from the contract lemmas (`Trans.Wire.init_computes`,
  `step_computes`, `Trans.Bounds.*_computes`) and the budget lemmas (`Trans.BoundsStep.*_budget`),
  given the compile/endpoint/init envelopes;
* `zero_of`: `Assembly.ZeroFacts` (`Trans.Bounds.zeroFacts_of`); the zero-length state's
  output bounds are constants (`zeroK`), absorbed into the init envelopes;
* **`components_of_remaining : RemainingBounds hD hd A density →
  Nonempty (Assembly.Components hD hd A density)`**.
-/

set_option autoImplicit false

noncomputable section
namespace QecReliability.Install
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Query.Plain (ProgP)
open QecReliability.Trans.Control (encKey encCfg TArg TCfg)
open QecReliability.Trans.Hash (gNbr)
open QecReliability.Trans.BoundsStep (valueB costB depthB)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

/-! ## Envelopes -/

/-- `P + K` as an envelope (`eval ≥ P.eval + K`). -/
def envAdd (P : PolynomialEnvelope) (K : ℕ) : PolynomialEnvelope := ⟨P.coefficient + K, P.degree⟩

theorem envAdd_eval (P : PolynomialEnvelope) (K L : ℕ) : P.eval L + K ≤ (envAdd P K).eval L := by
  unfold envAdd PolynomialEnvelope.eval
  have h : 1 ≤ (L + 1) ^ P.degree := Nat.one_le_pow _ _ (Nat.succ_pos L)
  rw [Nat.add_mul]
  have : K ≤ K * (L + 1) ^ P.degree := Nat.le_mul_of_pos_right K h
  simp only
  omega

/-- Size of the encoded zero-length configuration (a constant). -/
def zeroC : ℕ := (TCfg.enc (encCfg Trans.Wire.zeroCfg)).size

/-- A constant dominating the output bounds at the zero-length state. -/
def zeroK : ℕ := 1100 * (zeroC + 1) ^ 3 + 10 * (zeroC + 1) ^ 2 + 40 * zeroC + 100

theorem ci_le_costB (G density sc : ℕ) (Cc Ci : PolynomialEnvelope) (L : ℕ) :
    Ci.eval L ≤ costB G density sc Cc Ci L := by unfold costB; omega
theorem di_le_depthB (G density sc : ℕ) (Cd Di : PolynomialEnvelope) (L : ℕ) :
    Di.eval L ≤ depthB G density sc Cd Di L := by unfold depthB; omega
theorem mi_le_valueB (G density sc : ℕ) (Cm Mi : PolynomialEnvelope) (L : ℕ) :
    Mi.eval L ≤ valueB G density sc Cm Mi L := by unfold valueB; omega
theorem k_le_costB (G density sc : ℕ) (Cc Ci : PolynomialEnvelope) (L : ℕ) :
    40000 ≤ costB G density sc Cc Ci L := by unfold costB; omega
theorem k_le_depthB (G density sc : ℕ) (Cd Di : PolynomialEnvelope) (L : ℕ) :
    2000 ≤ depthB G density sc Cd Di L := by unfold depthB; nlinarith
theorem k_le_valueB (G density sc : ℕ) (Cm Mi : PolynomialEnvelope) (L : ℕ) :
    30000 ≤ valueB G density sc Cm Mi L := by unfold valueB; nlinarith

/-! ## Init's result fits its size budget -/

theorem initTop_res_le (L : Trans.Wire.Lib) (h : Trans.Wire.HIx) (p : Trans.Wire.PIx)
    (a : Trans.Wire.AIx) (y : Trans.Control.IxI)
    (Fp : FnSig (.prod .nat (.prod .nat .nat)) Trans.Hash.TParams) (base den : ℕ) (w : List Bool) :
    ((TArg Trans.Wire.TX).enc ((Trans.Wire.initTopF L h p a y Fp base den).den w)).size ≤
      (Trans.Wire.initTopF L h p a y Fp base den).msize w := by
  rw [Trans.Wire.initTopF, Trans.Control.bodySig_den, Trans.Control.bodySig_msize]
  exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t) (A : CertifiedParity (512*t) (64*t) t)
  (density : ℕ)

/-! ## Validity in the instance program -/

/-- **The instance's hash program is valid** (all arguments). -/
theorem theHash_ok : ∀ x, (theHash hD hd A).ValidAt (theProg hD hd A density) x :=
  hash_ok (Trans.HashCallees.four_le_degree hD)
    (fun ell => (Trans.HashCallees.encProg_dataProgram hD hd A ell).symm)
    (Trans.HashCallees.nbrF_den _ _ _ _)

/-! ## Positive instances -/

local notation "GG" => gateConstant hD hd A
local notation "SC" => seedConstant hD hd A

theorem positive_of (Cc Cd Cm Ci Di Mi : PolynomialEnvelope) (Bd : Assembly.Budget)
    (hBd : ∀ L, valueB GG density SC Cm Mi L ≤ Bd.value.eval L ∧
      costB GG density SC Cc Ci L ≤ Bd.cost.eval L ∧ depthB GG density SC Cd Di L ≤ Bd.depth.eval L)
    (hcomp : CompileBound hD hd A density Cc Cd Cm) (hend : EndpointBound hD hd A Cc Cd Cm)
    (hinit : InitBound hD hd A Ci Di Mi) :
    ∀ {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
      (E : MultiTape.Machine kE ΓE ΛE) (PtE PsE : PolynomialEnvelope) (T : ℕ → ℕ)
      (spec : EncodedSAT E density PtE PsE T), Monotone T →
      ∀ (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
        (coins : Fin (coinBits hD hd A c d (k+1)) → Bool),
        0 < a → a ≤ b → 0 < c → 0 < d →
        ∃ enc : Config → FL.Val,
          Assembly.PositiveFacts hD hd A (theProg hD hd A density) topIdx Bd spec a b c d k rows
            coins enc := by
  intro kE ΓE ΛE _ _ _ E PtE PsE T spec hT a b c d k rows coins ha hab hc hd'
  refine ⟨Trans.Wire.instEnc hD hd A a b c d k rows coins, ?_⟩
  have hH := theHash_ok hD hd A density
  obtain ⟨hBv, hBc, hBd⟩ := hBd (paperL rows a b c d)
  have harg : ∀ {s}, Assembly.InstReachable hD hd A spec a b c d k rows coins s →
      (Trans.Wire.instEnc hD hd A a b c d k rows coins s).size ≤ Bd.value.eval (paperL rows a b c d) :=
    fun hs => (Trans.BoundsStep.arg_budget hD hd A spec hT Cm Mi rows coins ha hab hc hd' hs).trans
      hBv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- init
    obtain ⟨i1, i2, i3, i4⟩ := hinit a b c d k rows coins ha hab hc hd'
    obtain ⟨j1, j2, j3, j4⟩ :=
      Trans.BoundsStep.init_budget hD hd A (density := density) Cc Cd Cm Ci Di Mi rows i1 i2 i3 i4
    exact Trans.Wire.init_computes hD hd A wL wH wP wA yI paramsFn Bd (fun _ => rfl) init_ok
      a b c d k rows coins (j3.trans hBv) (j4.trans hBv) (j1.trans hBc) (j2.trans hBd)
  · -- isDone
    intro s hs
    obtain ⟨c1, d1, m1⟩ := Trans.BoundsStep.isDone_budget hD hd A (density := density)
      Cc Cd Cm Ci Di Mi rows coins (theCX hD hd A density) s
    exact Trans.Bounds.isDone_computes hD hd A spec Bd rows coins hT ha hab hc hd'
      (theCX hD hd A density) s hs (isDone_ok _) (m1.trans hBv) (harg hs) (c1.trans hBc)
      (d1.trans hBd)
  · -- isInvoke
    intro s hs _
    obtain ⟨c1, d1, m1⟩ := Trans.BoundsStep.isInvoke_budget hD hd A (density := density)
      Cc Cd Cm Ci Di Mi rows coins (theCX hD hd A density) s
    exact Trans.Bounds.isInvoke_computes hD hd A Bd rows coins (theCX hD hd A density) s
      (isInvoke_ok _) (m1.trans hBv) (harg hs) (c1.trans hBc) (d1.trans hBd)
  · -- query
    intro s hs _
    obtain ⟨c1, d1, m1⟩ := Trans.BoundsStep.query_budget hD hd A (density := density)
      Cc Cd Cm Ci Di Mi rows coins (theCX hD hd A density) s
    exact Trans.Bounds.query_computes hD hd A Bd rows coins (theCX hD hd A density) s
      (queryOf_ok _) (m1.trans hBv) (harg hs) (c1.trans hBc) (d1.trans hBd)
  · -- resume
    intro s e hs hpc he
    have hden : (Trans.Bounds.resumeTopF oX (theCX hD hd A density)).den
        (((Assembly.instExt hD hd A spec c d k rows coins).sat s.query).value,
          (Trans.Bounds.ictx hD hd A a b c d k rows coins, encCfg s)) =
        (Trans.Bounds.ictx hD hd A a b c d k rows coins, encCfg e.next) := by
      rw [Trans.Bounds.resumeTopF_den, Trans.Bounds.invoke_edge_next _ _ _ _ _ s e hpc he]
    obtain ⟨c1, d1, m1, a1⟩ := Trans.BoundsStep.resume_budget hD hd A spec hT Cc Cd Cm Ci Di Mi
      rows coins ha hab hc hd' oX (theCX hD hd A density) _ hs he hden
    exact Trans.Bounds.resume_computes hD hd A spec Bd rows coins oX (theCX hD hd A density) s e
      hpc he (resumeTop_ok hH _) (m1.trans hBv) (a1.trans hBv) (c1.trans hBc) (d1.trans hBd)
  · -- step
    intro s e hs hpc he
    have hden := Trans.Wire.wire_step_correct hD hd A spec wL wC queryFn (theHash hD hd A) yR
      (fun _ => rfl) (fun _ => rfl) (theCX hD hd A density) rfl rfl rows coins e hs hpc he
    obtain ⟨c1, d1, m1⟩ := Trans.BoundsStep.step_budget hD hd A spec hT Cc Cd Cm Ci Di Mi
      rows coins ha hab hc hd' (theCX hD hd A density) hs hpc he hden
      (hcomp E PtE PsE T spec hT a b c d k rows coins ha hab hc hd' s hs)
      (fun bb => hend a b c d k rows coins bb ha hab hc hd')
    exact Trans.Wire.step_computes hD hd A spec wL wC queryFn (theHash hD hd A) yR Bd
      (fun _ => rfl) (fun _ => rfl) (theCX hD hd A density) rfl rfl rows coins s e hs hpc he
      (step_ok hH _) (m1.trans hBv) (harg hs) (c1.trans hBc) (d1.trans hBd)
  · -- output
    intro s hs _
    obtain ⟨c1, d1, m1⟩ := Trans.BoundsStep.output_budget hD hd A spec hT Cc Cd Cm Ci Di Mi
      rows coins ha hab hc hd' oX hs
    exact Trans.Bounds.output_computes hD hd A Bd rows coins oX s (output_ok _) (m1.trans hBv)
      (harg hs) (c1.trans hBc) (d1.trans hBd)


/-! ## `n = 0` -/

theorem zero_of (Cc Cd Cm Ci Di Mi : PolynomialEnvelope) (Bd : Assembly.Budget)
    (hBd : ∀ L, valueB GG density SC Cm Mi L ≤ Bd.value.eval L ∧
      costB GG density SC Cc Ci L ≤ Bd.cost.eval L ∧ depthB GG density SC Cd Di L ≤ Bd.depth.eval L)
    (hzero : InitZeroBound hD hd A Ci Di Mi)
    (hK : ∀ L, zeroK ≤ Ci.eval L ∧ zeroK ≤ Di.eval L ∧ zeroK ≤ Mi.eval L) :
    ∀ (rows : List (List (PauliCoord 0))) (a b c d : ℕ), 0 < a → a ≤ b → 0 < c → 0 < d →
      Assembly.ZeroFacts (theProg hD hd A density) topIdx Bd rows a b c d := by
  intro rows a b c d ha hab hc hd'
  obtain ⟨hBv, hBc, hBd⟩ := hBd (paperL rows a b c d)
  obtain ⟨i1, i2, i3, i4⟩ := hzero rows a b c d ha hab hc hd'
  obtain ⟨k1, k2, k3⟩ := hK (paperL rows a b c d)
  have vI := (mi_le_valueB GG density SC Cm Mi (paperL rows a b c d)).trans hBv
  have cI := (ci_le_costB GG density SC Cc Ci (paperL rows a b c d)).trans hBc
  have dI := (di_le_depthB GG density SC Cd Di (paperL rows a b c d)).trans hBd
  have vK := (k_le_valueB GG density SC Cm Mi (paperL rows a b c d)).trans hBv
  have cK := (k_le_costB GG density SC Cc Ci (paperL rows a b c d)).trans hBc
  have dK := (k_le_depthB GG density SC Cd Di (paperL rows a b c d)).trans hBd
  -- the zero-length state is `init`'s result, so its size is within `init`'s size budget
  have hres := initTop_res_le wL wH wP wA yI paramsFn (data hD hd A).base (data hD hd A).den
    (machineInput rows a b c d [])
  rw [Trans.Wire.init_zero hD hd A wL wH wP wA yI paramsFn (fun _ => rfl) rows a b c d] at hres
  have harg : ((TArg Trans.Wire.TX).enc (Trans.Bounds.zeroArg hD hd A rows a b c d)).size ≤
      Bd.value.eval (paperL rows a b c d) := hres.trans (i3.trans vI)
  obtain ⟨e1, e2, e3⟩ := Trans.Bounds.isDone_bounds (theCX hD hd A density)
    (Trans.Bounds.zeroArg hD hd A rows a b c d).1 Trans.Wire.zeroCfg
  obtain ⟨o1, o2, o3⟩ := Trans.Bounds.outputF_bounds oX
    (Trans.Bounds.zeroArg hD hd A rows a b c d).1 Trans.Wire.zeroCfg
  have z1 : 1100 * (zeroC + 1) ^ 3 ≤ zeroK := by unfold zeroK; omega
  have z2 : 10 * (zeroC + 1) ^ 2 + 1 ≤ zeroK := by unfold zeroK; omega
  have z3 : 40 * zeroC + 60 ≤ zeroK := by unfold zeroK; omega
  exact Trans.Bounds.zeroFacts_of hD hd A wL wH wP wA yI paramsFn (theCX hD hd A density) oX topIdx
    Bd rfl rfl rfl (fun _ => rfl) init_ok rows a b c d (i3.trans vI) (i4.trans vI) (i1.trans cI)
    (i2.trans dI) (isDone_ok _) (e3.trans (by omega)) harg (e1.trans (by omega))
    (e2.trans (by omega)) (output_ok _) (o3.trans (z3.trans (k3.trans vI)))
    (o1.trans (z1.trans (k1.trans cI))) (o2.trans (z2.trans (k2.trans dI)))

/-! ## The bundle -/

theorem initBound_add {Ci Di Mi : PolynomialEnvelope} (K : ℕ) (h : InitBound hD hd A Ci Di Mi) :
    InitBound hD hd A (envAdd Ci K) (envAdd Di K) (envAdd Mi K) := by
  intro a b c d k rows coins ha hab hc hd'
  obtain ⟨h1, h2, h3, h4⟩ := h a b c d k rows coins ha hab hc hd'
  have e1 := envAdd_eval Ci K (paperL rows a b c d)
  have e2 := envAdd_eval Di K (paperL rows a b c d)
  have e3 := envAdd_eval Mi K (paperL rows a b c d)
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem initZeroBound_add {Ci Di Mi : PolynomialEnvelope} (K : ℕ)
    (h : InitZeroBound hD hd A Ci Di Mi) :
    InitZeroBound hD hd A (envAdd Ci K) (envAdd Di K) (envAdd Mi K) := by
  intro rows a b c d ha hab hc hd'
  obtain ⟨h1, h2, h3, h4⟩ := h rows a b c d ha hab hc hd'
  have e1 := envAdd_eval Ci K (paperL rows a b c d)
  have e2 := envAdd_eval Di K (paperL rows a b c d)
  have e3 := envAdd_eval Mi K (paperL rows a b c d)
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The component bundle from the remaining bounds.** -/
theorem components_of_remaining (h : RemainingBounds hD hd A density) :
    Nonempty (Assembly.Components hD hd A density) := by
  obtain ⟨Cc, Cd, Cm, Ci, Di, Mi, hcomp, hend, hinit, hzero⟩ := h
  obtain ⟨Bd, hBd⟩ := Trans.BoundsStep.budget_exists (gateConstant hD hd A) density
    (seedConstant hD hd A) Cc Cd Cm (envAdd Ci zeroK) (envAdd Di zeroK) (envAdd Mi zeroK)
  have hK : ∀ L, zeroK ≤ (envAdd Ci zeroK).eval L ∧ zeroK ≤ (envAdd Di zeroK).eval L ∧
      zeroK ≤ (envAdd Mi zeroK).eval L := fun L => by
    have e1 := envAdd_eval Ci zeroK L
    have e2 := envAdd_eval Di zeroK L
    have e3 := envAdd_eval Mi zeroK L
    exact ⟨by omega, by omega, by omega⟩
  exact ⟨{ P := theProg hD hd A density
           idx := topIdx
           budget := Bd
           positive := positive_of hD hd A density Cc Cd Cm _ _ _ Bd hBd hcomp hend
             (initBound_add hD hd A zeroK hinit)
           zero := zero_of hD hd A density Cc Cd Cm _ _ _ Bd hBd
             (initZeroBound_add hD hd A zeroK hzero) hK }⟩

end QecReliability.Install

end
