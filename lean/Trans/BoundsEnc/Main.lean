import Trans.BoundsEnc.Level

/-!
# Trans.BoundsEnc.Main: the encoder oracle bound for the concrete constants

* `encP_mag_le`: for `E = encConsts D A = (D, 384, A.code.val)` (`D = 16^384`), the level-`j`
  programs have `mag (encP E j) ≤ G 2 cS (2^ell)` for `j ≤ ell + 1` (`EncoderSize.lean`:
  `≤ 2D·N` gates, `N = 128 D 2^(j-1)` outputs, wires `< N/4 + gates + 2`; `mag_prog_le`).
* **`prog_bound`**: `∃ kq cq, ∀ ell, cost/depth/msize/mag(result) of progF L I (encConsts D A)
  at ell ≤ G kq cq (2^ell)` — exactly hypothesis (b) (`hprog`) of `Trans.BoundsQH.hash_on`.
* **`hash_concrete_bound`**: `hash_on` with the concrete encoder oracle `progF` and the concrete
  encoder-output map `encOutsF` (built on `nbrF`): one polynomial bound `G K C'` for
  `hashF C (encProg ∘ (data hD hd A).program) (gNbr actualMGG) i` at all `(base, den, q, r, bits)`;
  the remaining hypotheses concern the data-independent combinators (as in
  `HashCallees.hash_valid_concrete`).

Nothing about `D = 16^384`, `t` or the certificate `A` is evaluated: the constants `kq cq`
are existential terms built from `D`, `384`, `A.code.val` symbolically.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsEnc
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.BoundsQH QecReliability.Trans.Hash QecReliability.Trans.HashCallees
open QecReliability.Trans.Query.Plain
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength

/-- Arithmetic of the size bound: `(g + N + 2)(2(N/4 + g + 2) + 10) ≤ A (X+1)²` for
`N ≤ 128 Z`, `g ≤ 256 Z`, `Z = D² X`. -/
theorem size_arith (D X Y g : ℕ) (hD : 1 ≤ D) (hY : Y ≤ X) (hg : g ≤ 2 * D * (128 * D * Y)) :
    (g + 128 * D * Y + 2) * (2 * (128 * D * Y / 4 + g + 2) + 10) ≤
      360000 * (D * D) * (D * D) * ((X + 1) * (X + 1)) := by
  have hDD : D ≤ D * D := Nat.le_mul_of_pos_left D (by omega)
  have hDD1 : 1 ≤ D * D := le_trans hD hDD
  have f1 : D * Y ≤ D * D * X := Nat.mul_le_mul hDD hY
  have f2 : D * D * Y ≤ D * D * X := Nat.mul_le_mul_left _ hY
  have e1 : 128 * D * Y = 128 * (D * Y) := by ring
  have e2 : 2 * D * (128 * D * Y) = 256 * (D * D * Y) := by ring
  generalize hZ : D * D * X = Z at f1 f2
  have hN4 : 128 * D * Y / 4 ≤ 128 * D * Y := Nat.div_le_self _ _
  have a1 : g + 128 * D * Y + 2 ≤ 384 * (Z + 1) := by omega
  have a2 : 2 * (128 * D * Y / 4 + g + 2) + 10 ≤ 768 * (Z + 1) := by omega
  have a3 : Z + 1 ≤ D * D * (X + 1) := by
    have : D * D * (X + 1) = D * D * X + D * D := by ring
    omega
  calc (g + 128 * D * Y + 2) * (2 * (128 * D * Y / 4 + g + 2) + 10)
      ≤ (384 * (Z + 1)) * (768 * (Z + 1)) := Nat.mul_le_mul a1 a2
    _ = 294912 * ((Z + 1) * (Z + 1)) := by ring
    _ ≤ 294912 * ((D * D * (X + 1)) * (D * D * (X + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul a3 a3)
    _ = 294912 * (D * D) * (D * D) * ((X + 1) * (X + 1)) := by ring
    _ ≤ 360000 * (D * D) * (D * D) * ((X + 1) * (X + 1)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))

/-- **Size of the level programs** for the concrete constants. -/
theorem encP_mag_le {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) :
    ∃ kS cS, ∀ ell j, j ≤ ell + 1 → mag TProg (encP (encConsts D A) j) ≤ G kS cS (2 ^ ell) := by
  refine ⟨2, mag TProg (baseP D A.code.val) + 360000 * (D * D) * (D * D), fun ell j hj => ?_⟩
  rcases j with _ | j
  · show mag TProg (baseP D A.code.val) ≤ _
    exact G_const (by omega)
  · show mag TProg (encP (D, 384, A.code.val) (j + 1)) ≤ _
    have hD4 : 4 ≤ D := four_le_degree hD
    have hY : 2 ^ j ≤ 2 ^ ell := Nat.pow_le_pow_right (by omega) (by omega)
    have hg := encP_gates_le hD hd A j
    have ho := encP_outputs_length hD hd A j
    obtain ⟨hw1, hw2⟩ := encP_wires_lt hD hd A j
    have hinv : PInv (128 * D * 2 ^ j / 4 + (encP (D, 384, A.code.val) (j + 1)).1.length + 2)
        (encP (D, 384, A.code.val) (j + 1)) :=
      ⟨fun g hg => ⟨(hw1 g hg).1.le, (hw1 g hg).2.le⟩, fun o ho => by have := hw2 o ho; omega⟩
    have hm : mag TProg (encP (D, 384, A.code.val) (j + 1)) ≤
        ((encP (D, 384, A.code.val) (j + 1)).1.length +
          (encP (D, 384, A.code.val) (j + 1)).2.length + 2) *
        (2 * (128 * D * 2 ^ j / 4 + (encP (D, 384, A.code.val) (j + 1)).1.length + 2) + 10) :=
      mag_prog_le _ hinv
    rw [ho] at hm
    have ha := size_arith D (2 ^ ell) (2 ^ j) _ (by omega) hY hg
    have hq := quad_le (360000 * (D * D) * (D * D)) (2 ^ ell)
    have hG : G 2 (360000 * (D * D) * (D * D)) (2 ^ ell) ≤
        G 2 (mag TProg (baseP D A.code.val) + 360000 * (D * D) * (D * D)) (2 ^ ell) :=
      G_mono le_rfl (by omega) le_rfl
    generalize 360000 * (D * D) * (D * D) = Aq at ha hq hG
    omega

/-- **The encoder oracle bound** — hypothesis (b) of `hash_on` for `C.prog = progF L I
(encConsts D A)`. -/
theorem prog_bound {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (L : HashCallees.Lib) (I : EncIx) :
    ∃ kq cq, ∀ ell, (progF L I (encConsts D A)).cost ell ≤ G kq cq (2 ^ ell) ∧
      (progF L I (encConsts D A)).depth ell ≤ G kq cq (2 ^ ell) ∧
      (progF L I (encConsts D A)).msize ell ≤ G kq cq (2 ^ ell) ∧
      mag TProg ((progF L I (encConsts D A)).den ell) ≤ G kq cq (2 ^ ell) := by
  obtain ⟨kS, cS, hsz⟩ := encP_mag_le hD hd A
  exact prog_bound_gen L I (encConsts D A) (K0 := 384) le_rfl hsz

/-- **`hash_on` with the concrete encoder oracle and encoder-output map.** -/
theorem hash_concrete_bound {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) (L : HashCallees.Lib) (I : EncIx) (R : RotIx)
    (inbr ivs ifo iidx imap : ℕ) (C : HashCallees) (hCp : C.prog = progF L I (encConsts D A))
    (hCe : C.encOuts = encOutsF L R inbr ivs ifo iidx imap) (i base den : ℕ) (hb : 1 ≤ base)
    {kp cp : ℕ} (hparams : ∀ q, FnBAt (G kp cp) C.params (base, den, q))
    (hparamsd : ∀ x, C.params.den x = (params x.1 x.2.1 x.2.2).tuple)
    (hpad : PolyB C.pad) (hsel : PolyB C.sel) (haff : PolyB C.aff)
    (hrows : PolyB C.rows) (htrans : PolyB C.trans) (hcomp : PolyB C.comp) (hdm : PolyB C.dm)
    (hpadd : ∀ x, C.pad.den x = padP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hseld : ∀ x, C.sel.den x = pselect x.1 x.2)
    (haffd : ∀ x, C.aff.den x = affP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hrowsd : ∀ x, C.rows.den x = seedRows x.1 x.2.1 x.2.2)
    (htransd : ∀ x, C.trans.den x = transP x.1 x.2)
    (hcompd : ∀ x, C.comp.den x = pcompose x.1 x.2.1 x.2.2)
    (hdmd : ∀ x, C.dm.den x = (x.1 / x.2, x.1 % x.2)) :
    ∃ K C', ∀ q r bits, FnBAt (G K C')
      (hashF C (fun ell => Query.encProg ((data hD hd A).program ell)) (gNbr actualMGG) i)
      (base, den, q, r, bits) := by
  obtain ⟨kq, cq, hq⟩ := prog_bound hD hd A L I
  have hprog : ∀ ell, C.prog.cost ell ≤ G kq cq (2 ^ ell) ∧
      C.prog.depth ell ≤ G kq cq (2 ^ ell) ∧ C.prog.msize ell ≤ G kq cq (2 ^ ell) ∧
      mag TProg (C.prog.den ell) ≤ G kq cq (2 ^ ell) := by
    rw [hCp]; exact hq
  have hprogd : ∀ x, C.prog.den x = Query.encProg ((data hD hd A).program x) := by
    rw [hCp]; exact fun ell => (encProg_dataProgram hD hd A ell).symm
  have henc : PolyB C.encOuts := by
    rw [hCe]; exact encOutsF_P L R inbr ivs ifo iidx imap
  have hencd : ∀ x, C.encOuts.den x =
      x.2.map (encIndex (gNbr actualMGG x.1.1) 16 x.1.2.1 x.1.2.2.1 x.1.2.2.2) := by
    rw [hCe]; exact fun x => rfl
  exact hash_on C _ (gNbr actualMGG) i base den hb hparams hparamsd hprog hpad hsel henc haff
    hrows htrans hcomp hdm hpadd hprogd hseld hencd haffd hrowsd htransd hcompd hdmd

end QecReliability.Trans.BoundsEnc
