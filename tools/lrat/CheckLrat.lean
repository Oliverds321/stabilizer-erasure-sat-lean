import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser
import Lean.Meta.Tactic.BVDecide.LRAT.Trim

/-!
# Check an LRAT refutation of a DIMACS CNF with Lean's verified checker

usage: lean --run tools/lrat/CheckLrat.lean FILE.cnf FILE.lrat

The program parses the DIMACS file into `Std.Sat.CNF Nat`, parses the LRAT proof (text or
binary) with the parser of Lean core, trims it, and runs `Std.Tactic.BVDecide.LRAT.check`.
By the core theorem

    Std.Tactic.BVDecide.LRAT.check_sound :
      check lratProof cnf → cnf.Unsat

the line `VERIFIED UNSAT` means that the parsed formula has no satisfying assignment.
What is trusted: the Lean kernel and core library, the compiled code of `check`, and the
DIMACS parser below (which is the inverse of `Std.Sat.CNF.dimacs`: the DIMACS variable `x`
is the variable `x - 1` of the formula, and clauses keep their order).
-/

open Std.Sat Std.Tactic.BVDecide

def parseDimacs (text : String) : Except String (CNF Nat) := do
  let mut clauses : Array (CNF.Clause Nat) := #[]
  let mut current : List (Literal Nat) := []
  let mut declared : Option Nat := none
  for line in text.splitOn "\n" do
    let tokens := (line.splitOn " ").filter (fun t => t ≠ "" && t ≠ "\r")
    match tokens with
    | [] => continue
    | "c" :: _ => continue
    | ["p", "cnf", _, c] =>
      match (c.replace "\r" "").toNat? with
      | some k => declared := some k
      | none => throw s!"bad header: {line}"
    | _ =>
      for tok in tokens do
        match (tok.replace "\r" "").toInt? with
        | none => throw s!"bad token: {tok}"
        | some x =>
          if x = 0 then
            clauses := clauses.push current.reverse
            current := []
          else
            current := (x.natAbs - 1, decide (0 < x)) :: current
  unless current.isEmpty do throw "unterminated clause"
  match declared with
  | none => throw "no DIMACS header"
  | some k =>
    unless k = clauses.size do
      throw s!"header declares {k} clauses, found {clauses.size}"
  return { clauses }

def main (args : List String) : IO UInt32 := do
  match args with
  | [cnfPath, lratPath] =>
    let cnf ← IO.ofExcept (parseDimacs (← IO.FS.readFile cnfPath))
    let proof ← LRAT.loadLRATProof lratPath
    let steps := proof.size
    let proof ← IO.ofExcept (Lean.Meta.Tactic.BVDecide.LRAT.trim proof)
    if LRAT.check proof cnf then
      IO.println s!"VERIFIED UNSAT {cnfPath}: {cnf.clauses.size} clauses, {steps} proof steps, {proof.size} after trimming"
      return 0
    else
      IO.println s!"CHECK FAILED {cnfPath}"
      return 1
  | _ =>
    IO.eprintln "usage: lean --run CheckLrat.lean FILE.cnf FILE.lrat"
    return 2
