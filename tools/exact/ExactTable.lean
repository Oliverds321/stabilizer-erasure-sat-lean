import ExactTable

/-!
# Exact erasure coefficient tables, computed by the verified Lean function

usage (from the repository root; `LEAN_PATH` must contain the directory of the compiled
modules of this development, which include `ExactTable`):

    lean -M 9000 --run tools/exact/ExactTable.lean INSTANCE.txt

Instance format: the one of `tools/lrat/CertifyList.lean` (`n K` first, then `row X0 Z5 ...`
lines; `Xi` is `.inl i`, `Zi` is `.inr i`). Lines `L`, `min`, `unit` are accepted and ignored.

Output, one item per line:

    n 18
    f j NUM/DEN      f_j = fRat rows j  (average of 2^{-d_E} over |E| = j)
    u j NUM/DEN      u_j = uRat rows j  (fraction of uncorrectable E with |E| = j)

## Meaning

By `QecPhysical.Stabilizer.ExactTable.fRat_spec` and `uRat_spec` (module `ExactTable`;
axioms propext, Classical.choice, Quot.sound), for the parsed `rows`,

    (fRat rows j : ℝ) = layerAverage id (erasureScore (rowSpace rows)) j
    (uRat rows j : ℝ) = Uncorrectable.layerFraction (rowSpace rows) j

for every `j ≤ n`, with no isotropy hypothesis. The values are computed by the fast enumeration
`exactAcc` (bitmask loop and bitmask GF(2) elimination), which is proved equal to the
specification over `Finset.univ`; no `implemented_by` is involved.

What remains trusted: the parser below, the Lean compiler/interpreter that runs the compiled
code of the definitions, and the printing of rationals.
-/

open QecReliability.SharedCircuit QecPhysical.Stabilizer.ExactTable

def parseNat (tok : String) : Except String Nat :=
  match tok.toNat? with
  | some k => .ok k
  | none => .error s!"bad number: {tok}"

def parseCoord (tok : String) : Except String (Bool × Nat) := do
  if tok.startsWith "X" then return (true, ← parseNat (tok.drop 1).toString)
  else if tok.startsWith "Z" then return (false, ← parseNat (tok.drop 1).toString)
  else throw s!"bad coordinate: {tok}"

def parseInstance (text : String) : Except String (Nat × Array (List (Bool × Nat))) := do
  let mut nOpt : Option Nat := none
  let mut rows : Array (List (Bool × Nat)) := #[]
  for line0 in text.splitOn "\n" do
    let line := ((line0.splitOn "#").headD "").replace "\r" ""
    let tokens := (line.splitOn " ").filter (· ≠ "")
    match tokens with
    | [] => continue
    | ["n", k] => nOpt := some (← parseNat k)
    | "row" :: cs => rows := rows.push (← cs.mapM parseCoord)
    | "L" :: _ => continue
    | "min" :: _ => continue
    | "unit" :: _ => continue
    | _ => throw s!"bad line: {line}"
  let some n := nOpt | throw "missing n"
  for r in rows do
    for (_, i) in r do
      unless i < n do throw s!"qubit {i} out of range"
  return (n, rows)

def main (args : List String) : IO UInt32 := do
  match args with
  | [inst] =>
    let (n, raw) ← IO.ofExcept (parseInstance (← IO.FS.readFile inst))
    let fin : Nat → Except String (Fin n) := fun i =>
      if h : i < n then pure ⟨i, h⟩ else throw s!"qubit {i} out of range"
    let rows : List (List (PauliCoord n)) ← IO.ofExcept (raw.toList.mapM fun r =>
      r.mapM fun (isX, i) => do
        let q ← fin i
        pure (if isX then Sum.inl q else Sum.inr q))
    IO.println s!"n {n}"
    -- one enumeration; `fRat rows j = fOfAcc n (exactAcc rows) j` holds by `rfl`
    -- (`fRat_eq_ofAcc`, `uRat_eq_ofAcc`)
    let acc := exactAcc rows
    for j in List.range (n + 1) do
      IO.println s!"f {j} {fOfAcc n acc j}"
    for j in List.range (n + 1) do
      IO.println s!"u {j} {uOfAcc n acc j}"
    return 0
  | _ =>
    IO.eprintln "usage: lean --run tools/exact/ExactTable.lean INSTANCE.txt"
    return 2
