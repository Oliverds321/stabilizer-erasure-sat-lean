import SatToDistance
open QecReliability.SatReduction QecReliability.SharedCircuit
def enc (φ : Std.Sat.CNF Nat) : String :=
  let I := reduce φ
  s!"{I.n} {I.thr}\n" ++ String.intercalate "\n" (I.rows.map (fun r => String.intercalate " " (r.map (fun c => match c with | Sum.inl i => s!"X{i.val}" | Sum.inr i => s!"Z{i.val}"))))
#eval IO.println (enc ⟨#[[(0, true)]]⟩)
#eval IO.println "---"
#eval IO.println (enc ⟨#[[(0, true)], [(0, false)]]⟩)
#eval IO.println "---"
#eval IO.println (enc ⟨#[[(0, false), (0, true)]]⟩)
