import Trans.Wire.Parse

/-! Total runtime parser for arbitrary latent circuits. Preserves the exact
unconsumed coin suffix. Uses the existing bounded-repetition reader `many`,
so the definition has the same recursive shape as the existing FL `manyF`.
This is parser semantics, not yet its FL transcription or resource proof.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine.Parser
open SharedCircuit Trans.Query Trans.Wire
open OracleCost OracleCost.WholeWrapperCandidate.InputEncoding

def gateR : List Bool → Plain.GateP × List Bool
  | false :: tag :: bs =>
      let x := hdr bs
      let y := hdr x.2
      ((false, tag, x.1, y.1), y.2)
  | true :: false :: bs =>
      let x := hdr bs
      ((true, false, x.1, 0), x.2)
  | true :: true :: b :: bs => (Plain.constGate b, bs)
  | _ => ((true, true, 0, 0), [])

theorem gateR_gateBits {v : ℕ} (g : Gate v) (rest : List Bool) :
    gateR (gateBits g ++ rest) = (encGate g, rest) := by
  cases g <;> simp [gateBits, gateR, encGate, hdr_natHeader, List.append_assoc]

theorem many_succ {α : Type} (f : List Bool → α × List Bool) (k : ℕ) (bs : List Bool) :
    many f (k+1) bs =
      ((many f k bs).1 ++ [(f (many f k bs).2).1], (f (many f k bs).2).2) := by
  simp [many, List.range_succ, List.foldl_append, manyStep]

theorem gatesR_circuitBits {r g : ℕ} (C : Circuit r g) (rest : List Bool) :
    many gateR g (circuitBits C ++ rest) = (encCirc C, rest) := by
  induction C generalizing rest with
  | nil => simp [circuitBits, many, encCirc]
  | snoc C gate ih =>
      rw [many_succ]
      simp only [circuitBits, List.append_assoc, ih, gateR_gateBits, encCirc_snoc]

def programR (n : ℕ) (bs : List Bool) : Plain.ProgP × List Bool :=
  let h := hdr bs
  let gs := many gateR h.1 h.2
  let os := many hdr n gs.2
  ((gs.1, os.1), os.2)

theorem outputsR_outputBits {n r : ℕ} (C : Program r n) (rest : List Bool) :
    many hdr n (outputBits C ++ rest) =
      (List.ofFn (fun i : Fin n => (C.output i).val), rest) := by
  have h := many_flatMap hdr QueryCodec.natHeader id hdr_natHeader
    (List.ofFn (fun i : Fin n => (C.output i).val)) rest
  simpa [outputBits, List.flatMap, List.map_ofFn, Function.comp_def] using h

theorem programR_programBits {n r : ℕ} (C : Program r n) (rest : List Bool) :
    programR n (programBits C ++ rest) = (encProg C, rest) := by
  simp only [programR, programBits, List.append_assoc, hdr_natHeader,
    gatesR_circuitBits, outputsR_outputBits, encProg]

abbrev Parsed := ℕ × ℕ × List (List Plain.Coord) × Plain.ProgP ×
  ℕ × ℕ × ℕ × ℕ × List Bool

def parse (bs : List Bool) : Parsed :=
  let hn := hdr bs
  let hr := hdr hn.2
  let rows := rowsR hr.2
  let prog := programR hn.1 rows.2
  (hn.1, hr.1, rows.1, prog.1, precR prog.2)

/-- Every dimension, gate, wire and precision value is recovered, with the
literal same coin suffix. In particular no iid program is reconstructed. -/
theorem parse_problemBits {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (a b c d : ℕ) (coins : List Bool) :
    parse (problemBits rows C a b c d ++ coins) =
      (n, r, encRows rows, encProg C, a, b, c, d, coins) := by
  simp only [parse, problemBits, List.append_assoc, hdr_natHeader, rowsR_rowsBits,
    programR_programBits, precR_precisionBits]

end QecReliability.LatentMachine.Parser
