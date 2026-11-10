import CompletenessFormula
import Std.Tactic.BVDecide.LRAT.Parser
import Lean.Meta.Tactic.BVDecide.LRAT.Trim

/-!
# Certify a list of minimal uncorrectable sets with a formula built inside Lean

usage (from the repository root; `LEAN_PATH` must contain the directory of the compiled
modules of this development, which include `CompletenessFormula`):

    lean -M 9000 --run tools/lrat/CertifyList.lean emit  INSTANCE.txt OUT.cnf
    lean -M 9000 --run tools/lrat/CertifyList.lean check INSTANCE.txt PROOF.lrat

`lean.exe` finds the core library (`Std`, `Lean`) in its own `lib/lean`; only the project
objects have to be on `LEAN_PATH`.

## Instance format (plain text, one item per line, `#` starts a comment)

    n 18                  number of qubits (must come first)
    L 6                   size bound
    row X0 X3 Z5 ...      one check row; `Xi` is the coordinate `.inl i` (the X part, i.e. the
                          first component of `Pauli n`), `Zi` is `.inr i` (the Z part)
    min 0 4 9             one listed set (qubit indices, 0-based)
    unit 4 1              unit constraint: qubit 4 erased (`1`) or not erased (`0`)

## Modes

* `emit INSTANCE OUT.cnf` writes `Std.Sat.CNF.dimacs (certFormula rows L mins units)`.
* `check INSTANCE PROOF.lrat` rebuilds the same formula *inside Lean*, loads the LRAT proof
  (text or binary), trims it, and runs `Std.Tactic.BVDecide.LRAT.check` on the Lean-built
  formula (not on any DIMACS file).

## Meaning of `CERTIFIED`

`CERTIFIED` is printed only if `LRAT.check proof (certFormula rows L mins units) = true`. By

    QecPhysical.Stabilizer.Completeness.certFormula_checked
      (rows) (hS : rowSpace rows ≤ normalizer (symplectic n) (rowSpace rows)) (L) (mins) (units)
      (proof) (h : LRAT.check proof (certFormula rows L mins units) = true) :
      ∀ E : Finset (Fin n), E.card ≤ L → (∀ u ∈ units, (u.1 ∈ E ↔ u.2 = true)) →
        0 < ambiguity (symplectic n) (rowSpace rows) (supported E) → ∃ M ∈ mins, M.toFinset ⊆ E

(module `CompletenessFormula`; axioms propext, Classical.choice, Quot.sound) this means:
if the rows span an isotropic space, every uncorrectable erased set of size at most `L`
satisfying the unit constraints contains one of the listed sets. The isotropy hypothesis `hS`
is not checked by this program (the Python driver checks it by exact GF(2) arithmetic).

What remains trusted: the parser of the instance file below (that the `rows`, `L`, `mins`,
`units` it produces are the intended ones), the LRAT proof parser and trimmer (they only produce
the `proof` argument, so they cannot cause a false `CERTIFIED`), the Lean compiler/interpreter
that evaluates `certFormula` and `LRAT.check` (the theorem is about the kernel-level
definitions; the program runs their compiled code), and the Lean kernel.
-/

open Std.Sat Std.Tactic.BVDecide
open QecReliability.SharedCircuit QecPhysical.Stabilizer.Completeness

structure RawInstance where
  n : Nat
  L : Nat
  rows : Array (List (Bool × Nat))   -- (true = X / .inl, index)
  mins : Array (List Nat)
  units : Array (Nat × Bool)

def parseNat (tok : String) : Except String Nat :=
  match tok.toNat? with
  | some k => .ok k
  | none => .error s!"bad number: {tok}"

def parseCoord (tok : String) : Except String (Bool × Nat) := do
  if tok.startsWith "X" then return (true, ← parseNat (tok.drop 1).toString)
  else if tok.startsWith "Z" then return (false, ← parseNat (tok.drop 1).toString)
  else throw s!"bad coordinate: {tok}"

def parseInstance (text : String) : Except String RawInstance := do
  let mut nOpt : Option Nat := none
  let mut LOpt : Option Nat := none
  let mut rows : Array (List (Bool × Nat)) := #[]
  let mut mins : Array (List Nat) := #[]
  let mut units : Array (Nat × Bool) := #[]
  for line0 in text.splitOn "\n" do
    let line := ((line0.splitOn "#").headD "").replace "\r" ""
    let tokens := (line.splitOn " ").filter (· ≠ "")
    match tokens with
    | [] => continue
    | ["n", k] => nOpt := some (← parseNat k)
    | ["L", k] => LOpt := some (← parseNat k)
    | "row" :: cs => rows := rows.push (← cs.mapM parseCoord)
    | "min" :: is => mins := mins.push (← is.mapM parseNat)
    | ["unit", q, b] =>
      let b ← parseNat b
      unless b ≤ 1 do throw s!"bad unit value: {line}"
      units := units.push ((← parseNat q), decide (b = 1))
    | _ => throw s!"bad line: {line}"
  let some n := nOpt | throw "missing n"
  let some L := LOpt | throw "missing L"
  for r in rows do
    for (_, i) in r do
      unless i < n do throw s!"qubit {i} out of range"
  for m in mins do
    for i in m do
      unless i < n do throw s!"qubit {i} out of range"
  for (i, _) in units do
    unless i < n do throw s!"qubit {i} out of range"
  return { n, L, rows, mins, units }

/-- The typed instance and the Lean-built formula `certFormula rows L mins units`. -/
def buildFormula (raw : RawInstance) : Except String (CNF Nat) := do
  let n := raw.n
  let fin : Nat → Except String (Fin n) := fun i =>
    if h : i < n then pure ⟨i, h⟩ else throw s!"qubit {i} out of range"
  let rows : List (List (PauliCoord n)) ← raw.rows.toList.mapM fun r =>
    r.mapM fun (isX, i) => do
      let q ← fin i
      pure (if isX then Sum.inl q else Sum.inr q)
  let mins : List (List (Fin n)) ← raw.mins.toList.mapM fun m => m.mapM fin
  let units : List (Fin n × Bool) ← raw.units.toList.mapM fun (i, b) => do
    pure (← fin i, b)
  return certFormula rows raw.L mins units

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", inst, out] =>
    let raw ← IO.ofExcept (parseInstance (← IO.FS.readFile inst))
    let f ← IO.ofExcept (buildFormula raw)
    IO.FS.writeFile out (CNF.dimacs f)
    IO.println s!"EMITTED {out}: n={raw.n} L={raw.L} rows={raw.rows.size} listed={raw.mins.size} units={raw.units.size} clauses={f.clauses.size}"
    return 0
  | ["check", inst, lratPath] =>
    let raw ← IO.ofExcept (parseInstance (← IO.FS.readFile inst))
    let f ← IO.ofExcept (buildFormula raw)
    let proof ← LRAT.loadLRATProof lratPath
    let steps := proof.size
    let proof ← IO.ofExcept (Lean.Meta.Tactic.BVDecide.LRAT.trim proof)
    if LRAT.check proof f then
      IO.println s!"CERTIFIED n={raw.n} L={raw.L} listed={raw.mins.size} units={raw.units.size}: every uncorrectable erased set of size <= {raw.L} satisfying the unit constraints contains a listed set ({f.clauses.size} clauses, {steps} proof steps, {proof.size} after trimming)"
      return 0
    else
      IO.println s!"CHECK FAILED {inst}"
      return 1
  | _ =>
    IO.eprintln "usage: lean --run CertifyList.lean (emit INSTANCE OUT.cnf | check INSTANCE PROOF.lrat)"
    return 2
