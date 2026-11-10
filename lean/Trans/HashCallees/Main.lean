import Trans.HashCallees.EncoderFL
import Trans.HashCallees.EncoderSize
import Trans.HashCallees.MGGBounds

/-!
# Trans.HashCallees.Main: the two callee contracts of `Trans.Hash.HashCallees`

`Trans/Hash/Main.lean`'s `hash_valid` takes, besides the generic program combinators, two
oracles fixed by the algorithm's data `X = data hD hd A`, `G = actualMGG`:

1. **the encoder family** `C.prog : FnSig .nat TProg` with
   `∀ x, C.prog.ValidAt P x` and `∀ x, C.prog.den x = Query.encProg ((data hD hd A).program x)`:
   `progF L I (encConsts D A)` (`prog_contract`);
2. **the neighbour map** `inb : FnSig (ℕ × ℕ × ℕ) ℕ` used inside `C.encOuts` with
   `∀ x, inb.ValidAt P x` and `inb.den x = gNbr actualMGG x.1 x.2.1 x.2.2`:
   `nbrF L R.rot R.coord i` (`nbr_contract`); the resulting encoder-output map
   `encOutsF` satisfies `hash_valid`'s `henc`/`hencd` (`encOuts_contract`).

`hash_valid_concrete`: `hash_valid` for the concrete data, with these three callees plugged in
(the remaining hypotheses concern the data-independent combinators of `Trans/Hash`).
-/

set_option autoImplicit false

namespace QecReliability.Trans.HashCallees
open QecReliability.FL QecReliability.FL.Lib Tm NatSize
open QecReliability.Trans.Query.Plain QecReliability.Trans.Hash
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength

variable {P : Program}

/-- The encoder constants `(D, K, code) = (D, 384, A.code.val)` (symbolic). -/
def encConsts {t : ℕ} (D : ℕ) (A : CertifiedParity (512 * t) (64 * t) t) : ℕ × ℕ × ℕ :=
  (D, 384, A.code.val)

theorem four_le_degree {D : ℕ} (hD : D = 16 ^ 384) : 4 ≤ D :=
  Nat.le_of_dvd (SharedCircuit.FixedWitnessEncoder.degree_pos hD)
    (SharedCircuit.FixedWitnessEncoder.degree_four hD)

/-! ## Contract 1: the encoder family -/

/-- **Encoder oracle contract** (`HashCallees.prog`): valid at every `ell`, meaning
`Query.encProg ((data hD hd A).program ell)`. -/
theorem prog_contract {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) {L : Lib} (hL : L.OK P) {I : EncIx}
    (hI : I.OK P L (encConsts D A)) :
    (∀ ell, (progF L I (encConsts D A)).ValidAt P ell) ∧
    (∀ ell, (progF L I (encConsts D A)).den ell = Query.encProg ((data hD hd A).program ell)) :=
  ⟨prog_valid hL hI (four_le_degree hD), fun ell => (encProg_dataProgram hD hd A ell).symm⟩

/-! ## Contract 2: the neighbour map -/

/-- **Neighbour oracle contract** (`inb` of `encIdx_valid`): valid everywhere, meaning
`gNbr actualMGG`. -/
theorem nbr_contract {L : Lib} (hL : L.OK P) {R : RotIx} (hR : R.OK P L) {i : ℕ}
    (hP : P[i]? = some (nbrBody L R.rot R.coord).compile) :
    (∀ x, (nbrF L R.rot R.coord i).ValidAt P x) ∧
    (∀ x, (nbrF L R.rot R.coord i).den x = gNbr actualMGG x.1 x.2.1 x.2.2) :=
  ⟨nbr_valid hL hR.coord hR.rot hP, nbrF_den L R.rot R.coord i⟩

/-- The encoder-output map `HashCallees.encOuts` with the neighbour oracle `nbrF`. -/
noncomputable abbrev encOutsF (L : Lib) (R : RotIx) (inbr ivs ifo iidx imap : ℕ) :
    FnSig (.prod (.prod .nat (.prod .nat (.prod .nat .nat))) (.list .nat)) (.list .nat) :=
  mapEnvF (encIdxF L.dmF L.mul L.add L.range
    (foldlF (visStepF (nbrF L R.rot R.coord inbr) L.dmF ivs) ifo) (gNbr actualMGG) iidx) imap

/-- `hash_valid`'s `henc`/`hencd` for `encOutsF`. -/
theorem encOuts_contract {L : Lib} (hL : L.OK P) {R : RotIx} (hR : R.OK P L)
    {inbr ivs ifo iidx imap : ℕ}
    (hdm : P[L.dm]? = some (divModBody L.le L.sub L.dm).compile)
    (hnbr : P[inbr]? = some (nbrBody L R.rot R.coord).compile)
    (hvs : P[ivs]? = some (visStepBody (nbrF L R.rot R.coord inbr) L.dmF).compile)
    (hfo : P[ifo]? = some (foldlBody (visStepF (nbrF L R.rot R.coord inbr) L.dmF ivs) ifo).compile)
    (hidx : P[iidx]? = some (encIdxBody L.dmF L.mul L.add L.range
      (foldlF (visStepF (nbrF L R.rot R.coord inbr) L.dmF ivs) ifo)).compile)
    (hmap : P[imap]? = some (mapEnvBody (encIdxF L.dmF L.mul L.add L.range
      (foldlF (visStepF (nbrF L R.rot R.coord inbr) L.dmF ivs) ifo) (gNbr actualMGG) iidx)
      imap).compile) :
    (∀ x, 0 < x.1.2.1 ∧ 0 < x.1.2.2.1 ∧ 0 < x.1.2.2.2 →
      (encOutsF L R inbr ivs ifo iidx imap).ValidAt P x) ∧
    (∀ x, (encOutsF L R inbr ivs ifo iidx imap).den x =
      x.2.map (encIndex (gNbr actualMGG x.1.1) 16 x.1.2.1 x.1.2.2.1 x.1.2.2.2)) := by
  obtain ⟨hnb, hnbd⟩ := nbr_contract hL hR hnbr
  refine ⟨fun x hx => mapEnv_valid hmap x (fun y _ => ?_), fun x => rfl⟩
  exact encIdx_valid hL.le hL.sub hdm hL.mul hL.add hL.range hnb hnbd hvs hfo hidx (x.1, y) hx

/-! ## `hash_valid` for the concrete data -/

/-- **`hash_valid` with the concrete callees**: the encoder oracle `progF` and the
encoder-output map built on `nbrF`; the remaining hypotheses are those of `hash_valid` for the
data-independent combinators. -/
theorem hash_valid_concrete {D t : ℕ} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t) {L : Lib} (hL : L.OK P) {I : EncIx}
    (hI : I.OK P L (encConsts D A)) {R : RotIx} (hR : R.OK P L) {inbr ivs ifo iidx imap : ℕ}
    (hdm : P[L.dm]? = some (divModBody L.le L.sub L.dm).compile)
    (hnbr : P[inbr]? = some (nbrBody L R.rot R.coord).compile)
    (hvs : P[ivs]? = some (visStepBody (nbrF L R.rot R.coord inbr) L.dmF).compile)
    (hfo : P[ifo]? = some (foldlBody (visStepF (nbrF L R.rot R.coord inbr) L.dmF ivs) ifo).compile)
    (hidx : P[iidx]? = some (encIdxBody L.dmF L.mul L.add L.range
      (foldlF (visStepF (nbrF L R.rot R.coord inbr) L.dmF ivs) ifo)).compile)
    (hmap : P[imap]? = some (mapEnvBody (encIdxF L.dmF L.mul L.add L.range
      (foldlF (visStepF (nbrF L R.rot R.coord inbr) L.dmF ivs) ifo) (gNbr actualMGG) iidx)
      imap).compile)
    (C : HashCallees) (hCp : C.prog = progF L I (encConsts D A))
    (hCe : C.encOuts = encOutsF L R inbr ivs ifo iidx imap) {i : ℕ}
    (hparams : ∀ x, C.params.ValidAt P x)
    (hparamsd : ∀ x, C.params.den x = (params x.1 x.2.1 x.2.2).tuple)
    (hpad : ∀ x, C.pad.ValidAt P x) (hpadd : ∀ x, C.pad.den x = padP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hsel : ∀ x, C.sel.ValidAt P x) (hseld : ∀ x, C.sel.den x = pselect x.1 x.2)
    (hrange : ∀ x, (rangeF C.range).ValidAt P x) (hmul : ∀ x, (mulF C.mul).ValidAt P x)
    (hsucc : ∀ x, (succF C.succ).ValidAt P x)
    (haff : ∀ x, C.aff.ValidAt P x) (haffd : ∀ x, C.aff.den x = affP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hrows : ∀ x, C.rows.ValidAt P x) (hrowsd : ∀ x, C.rows.den x = seedRows x.1 x.2.1 x.2.2)
    (htrans : ∀ x, C.trans.ValidAt P x) (htransd : ∀ x, C.trans.den x = transP x.1 x.2)
    (hcomp : ∀ x, C.comp.ValidAt P x) (hcompd : ∀ x, C.comp.den x = pcompose x.1 x.2.1 x.2.2)
    (hdmC : ∀ a, C.dm.ValidAt P (a, 4)) (hdmd : ∀ x, C.dm.den x = (x.1 / x.2, x.1 % x.2))
    (hP : P[i]? = some (hashBody C).compile) :
    ∀ x, (hashF C (fun ell => Query.encProg ((data hD hd A).program ell)) (gNbr actualMGG) i).ValidAt P x := by
  obtain ⟨hpv, hpd⟩ := prog_contract hD hd A hL hI
  obtain ⟨hev, hed⟩ := encOuts_contract hL hR hdm hnbr hvs hfo hidx hmap
  exact hash_valid C _ _ hparams hparamsd hpad hpadd (by rw [hCp]; exact hpv)
    (by rw [hCp]; exact hpd) hsel hseld (by rw [hCe]; exact hev) (by rw [hCe]; exact hed) hrange
    hmul hsucc haff haffd hrows hrowsd htrans htransd hcomp hcompd hdmC hdmd hP

end QecReliability.Trans.HashCallees
