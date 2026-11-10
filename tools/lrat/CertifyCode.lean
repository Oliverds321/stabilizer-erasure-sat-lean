import ListCertificate
import Std.Tactic.BVDecide.LRAT.Parser
import Lean.Meta.Tactic.BVDecide.LRAT.Trim

/-!
# Certify the list of minimal uncorrectable sets of one code at one level

usage (from the repository root; `LEAN_PATH` must contain the directory of the compiled
modules of this development, which include `ListCertificate`):

    lean.exe -M 9000 --run tools/lrat/CertifyCode.lean combine BUNDLE.txt
    lean.exe -M 9000 --run tools/lrat/CertifyCode.lean full    BUNDLE.txt PROOFDIR

## Bundle format (one item per line, `#` comments only at the start of a line)

    name toric [[18,2,3]]     code name (used verbatim in the instance header, see below)
    n 18
    L 6                       level
    d 3                       claimed distance
    row X0 X3 Z5 ...          check rows in order (`Xi` = `.inl i`, `Zi` = `.inr i`)
    min 0 1 2                 listed sets of size <= L, in order (index 0, 1, ...)
    logical Z0 Z3 ...         vectors z (index 0, 1, ...) used by the certificates
    cert K J X0 Z3 ...        certificate of listed set K: x = the coordinates, z = logical J
    gen 1 2 0 ...             a generator: images of qubits 0..n-1
    img 4 0 7 ...             image table of the last generator: listed set k maps to set img[k]
    word Q K1 K2 ...          word for qubit Q (rightmost generator acts first)
    leaf R SHA V:B V:B ...    a leaf: representative R (or `-` without symmetry), recorded
                              instance SHA-256 (or `-`), unit literals (qubit V erased iff B = 1)

## What `CERTIFIED` means

The program evaluates `symCheckB rows L d mins xs zi logs gens imgs words leaves` (or
`plainCheckB` without symmetry) from the module `ListCertificate`, and for every leaf it
establishes that `certFormula rows L mins ((R, true) :: units)` (resp. `certFormula rows L mins
units`) is unsatisfiable. By

    QecPhysical.Stabilizer.ListCertificate.symmetric_certificate /
    QecPhysical.Stabilizer.ListCertificate.plain_certificate :
      (checks = true) → (all leaf formulas Unsat) → Certified rows L d mins

where `Certified` says: every uncorrectable erased set of size ≤ L contains a listed set,
`IsDistance (rowSpace rows) d`, the uncorrectable sets of size d are exactly the listed sets of
size d (`leadList`), and `∑_{|E| = d} infidelityScore S E = ∑_k leadCount k * (1 - 2^{-k})`;
the printed exponent counts are `leadCounts rows mins d`.

How the leaf formulas are established:
* `full`: `Std.Tactic.BVDecide.LRAT.check proof (certFormula …) = true` for the proof file
  `PROOFDIR/leafK.lrat` of leaf K; `check_sound` gives `Unsat`.
* `combine`: the program renders the exact instance file that `CertifyList.lean` reads for that
  leaf (header `# NAME, level L`, `n`, `L`, rows, listed sets, unit lines with `unit R 1`
  first) and compares its SHA-256 with the recorded one. The meaning then rests on the earlier
  `CertifyList check` run that printed CERTIFIED for the file with that hash (recorded by
  experiments/erasure/certify.py), and on SHA-256 collision resistance.

Trusted: this bundle parser (that it produces the intended data; wrong data can only make a
wrong *code* be certified, never a false statement about the parsed data), the Lean
compiler/interpreter running the checks, the kernel; in `combine` mode also the earlier
CertifyList runs and their hash records, and the SHA-256 code below (an error there can only
cause a mismatch unless it produces a collision).
-/

open Std.Sat Std.Tactic.BVDecide
open QecReliability.SharedCircuit QecPhysical.Stabilizer.Completeness
open QecPhysical.Stabilizer.ListCertificate

/-! ## SHA-256 -/

def shaK : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] def rotr (x : UInt32) (k : UInt32) : UInt32 := (x >>> k) ||| (x <<< (32 - k))

def sha256 (msg : ByteArray) : String := Id.run do
  let len := msg.size
  let mut data := msg.push 0x80
  while data.size % 64 != 56 do
    data := data.push 0
  let bits : UInt64 := (len.toUInt64) * 8
  for i in [0:8] do
    data := data.push ((bits >>> (8 * (7 - i)).toUInt64).toUInt8)
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for blk in [0:data.size / 64] do
    let mut w : Array UInt32 := Array.replicate 64 0
    for t in [0:16] do
      let b := fun k => (data.get! (64 * blk + 4 * t + k)).toUInt32
      w := w.set! t ((b 0 <<< 24) ||| (b 1 <<< 16) ||| (b 2 <<< 8) ||| b 3)
    for t in [16:64] do
      let s0 := rotr w[t-15]! 7 ^^^ rotr w[t-15]! 18 ^^^ (w[t-15]! >>> 3)
      let s1 := rotr w[t-2]! 17 ^^^ rotr w[t-2]! 19 ^^^ (w[t-2]! >>> 10)
      w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
    let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
    let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
    for t in [0:64] do
      let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
      let t1 := hh + S1 + ch + shaK[t]! + w[t]!
      let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := S0 + maj
      hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]
  let hex := fun (x : UInt32) =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    String.ofList (List.replicate (8 - s.length) '0') ++ s
  return String.join (h.toList.map hex)

/-! ## Bundle -/

structure Bundle where
  name : String := ""
  n : Nat := 0
  L : Nat := 0
  d : Nat := 0
  rows : Array (List (Bool × Nat)) := #[]
  mins : Array (List Nat) := #[]
  logicals : Array (List (Bool × Nat)) := #[]
  certs : Array (Nat × Nat × List (Bool × Nat)) := #[]
  gens : Array (Array Nat) := #[]
  imgs : Array (Array Nat) := #[]
  words : Array (Nat × List Nat) := #[]
  leaves : Array (Option Nat × String × List (Nat × Bool)) := #[]

def parseNat (tok : String) : Except String Nat :=
  match tok.toNat? with
  | some k => .ok k
  | none => .error s!"bad number: {tok}"

def parseCoord (tok : String) : Except String (Bool × Nat) := do
  if tok.startsWith "X" then return (true, ← parseNat (tok.drop 1).toString)
  else if tok.startsWith "Z" then return (false, ← parseNat (tok.drop 1).toString)
  else throw s!"bad coordinate: {tok}"

def parseLit (tok : String) : Except String (Nat × Bool) := do
  match tok.splitOn ":" with
  | [v, b] =>
    let b ← parseNat b
    unless b ≤ 1 do throw s!"bad literal {tok}"
    return (← parseNat v, decide (b = 1))
  | _ => throw s!"bad literal {tok}"

def parseBundle (text : String) : Except String Bundle := do
  let mut B : Bundle := {}
  for line0 in text.splitOn "\n" do
    let line := line0.replace "\r" ""
    if line.startsWith "#" then continue
    if line.startsWith "name " then
      B := { B with name := (line.drop 5).toString }
      continue
    let tokens := (line.splitOn " ").filter (· ≠ "")
    match tokens with
    | [] => continue
    | ["n", k] => B := { B with n := ← parseNat k }
    | ["L", k] => B := { B with L := ← parseNat k }
    | ["d", k] => B := { B with d := ← parseNat k }
    | "row" :: cs => B := { B with rows := B.rows.push (← cs.mapM parseCoord) }
    | "min" :: is => B := { B with mins := B.mins.push (← is.mapM parseNat) }
    | "logical" :: cs => B := { B with logicals := B.logicals.push (← cs.mapM parseCoord) }
    | "cert" :: k :: j :: cs =>
      B := { B with certs := B.certs.push (← parseNat k, ← parseNat j, ← cs.mapM parseCoord) }
    | "gen" :: is => B := { B with gens := B.gens.push (← is.mapM parseNat).toArray }
    | "img" :: is => B := { B with imgs := B.imgs.push (← is.mapM parseNat).toArray }
    | "word" :: q :: ks => B := { B with words := B.words.push (← parseNat q, ← ks.mapM parseNat) }
    | "leaf" :: r :: sha :: lits =>
      let r ← if r = "-" then pure none else some <$> parseNat r
      B := { B with leaves := B.leaves.push (r, sha, ← lits.mapM parseLit) }
    | _ => throw s!"bad line: {line}"
  return B

/-- The text of the instance file that CertifyList reads for a leaf (as certify_lean.py writes
it). -/
def renderInstance (B : Bundle) (units : List (Nat × Bool)) : String :=
  let coord := fun (c : Bool × Nat) => (if c.1 then "X" else "Z") ++ toString c.2
  let lines := [s!"# {B.name}, level {B.L}", s!"n {B.n}", s!"L {B.L}"] ++
    B.rows.toList.map (fun r => "row " ++ " ".intercalate (r.map coord)) ++
    B.mins.toList.map (fun m => "min " ++ " ".intercalate (m.map toString)) ++
    units.map (fun (q, b) => s!"unit {q} {if b then 1 else 0}")
  "\n".intercalate lines ++ "\n"

/-- Typed data. -/
structure Typed (n : Nat) where
  rows : List (List (PauliCoord n))
  mins : Array (List (Fin n))
  xs : Array (List (PauliCoord n))
  zi : Array Nat
  logs : Array (List (PauliCoord n))
  gens : Array (Fin n → Fin n)
  words : Array (List Nat)
  symLeaves : List (Fin n × List (List (Fin n × Bool)))
  plainLeaves : List (List (Fin n × Bool))

def typeBundle (B : Bundle) : Except String (Typed B.n) := do
  let n := B.n
  let fin : Nat → Except String (Fin n) := fun i =>
    if h : i < n then pure ⟨i, h⟩ else throw s!"qubit {i} out of range"
  let coord : Bool × Nat → Except String (PauliCoord n) := fun (isX, i) => do
    let q ← fin i
    pure (if isX then Sum.inl q else Sum.inr q)
  let rows ← B.rows.toList.mapM fun r => r.mapM coord
  let mins ← B.mins.mapM fun m => m.mapM fin
  let logs ← B.logicals.mapM fun r => r.mapM coord
  let mut xs : Array (List (PauliCoord n)) := Array.replicate B.mins.size []
  let mut zi : Array Nat := Array.replicate B.mins.size 0
  for (k, j, x) in B.certs do
    unless k < B.mins.size do throw s!"cert index {k} out of range"
    xs := xs.set! k (← x.mapM coord)
    zi := zi.set! k j
  let mut gens : Array (Fin n → Fin n) := #[]
  for g in B.gens do
    unless g.size = n do throw "generator of wrong length"
    let arr ← g.mapM fin
    gens := gens.push (fun i => (arr[i.val]?).getD i)
  let mut words : Array (List Nat) := Array.replicate n []
  for (q, w) in B.words do
    unless q < n do throw s!"word for qubit {q} out of range"
    words := words.set! q w
  -- leaves, grouped by representative in order of first appearance
  let mut reps : Array Nat := #[]
  for (r, _, _) in B.leaves do
    if let some q := r then
      unless reps.contains q do reps := reps.push q
  let lits := fun (u : List (Nat × Bool)) => u.mapM fun (v, b) => do pure ((← fin v), b)
  let mut symLeaves : List (Fin n × List (List (Fin n × Bool))) := []
  for q in reps do
    let us ← (B.leaves.toList.filter (fun l => l.1 = some q)).mapM fun l => lits l.2.2
    symLeaves := symLeaves ++ [(← fin q, us)]
  let plainLeaves ← (B.leaves.toList.filter (fun l => l.1 = none)).mapM fun l => lits l.2.2
  unless reps.isEmpty || plainLeaves.isEmpty do throw "mixed symmetric and plain leaves"
  return { rows, mins, xs, zi, logs, gens, words, symLeaves, plainLeaves }

def main (args : List String) : IO UInt32 := do
  let (mode, bundlePath, proofDir) ← match args with
    | ["combine", b] => pure ("combine", b, "")
    | ["full", b, p] => pure ("full", b, p)
    | _ => do
      IO.eprintln "usage: lean --run CertifyCode.lean (combine BUNDLE | full BUNDLE PROOFDIR)"
      return 2
  let B ← IO.ofExcept (parseBundle (← IO.FS.readFile bundlePath))
  let T ← IO.ofExcept (typeBundle B)
  let symmetric := !T.symLeaves.isEmpty
  let t0 ← IO.monoMsNow
  -- checks 1-4 and the size checks, exactly as in the theorem
  let ok := if symmetric then
      symCheckB T.rows B.L B.d T.mins T.xs T.zi T.logs T.gens B.imgs T.words T.symLeaves
    else plainCheckB T.rows B.L B.d T.mins T.xs T.zi T.logs T.plainLeaves
  let t1 ← IO.monoMsNow
  if !ok then
    -- diagnosis only
    IO.println s!"isotropy: {isotropyB T.rows}"
    IO.println s!"listed sets uncorrectable (certificates): {allCertOK2 T.rows T.mins T.xs T.zi T.logs}"
    IO.println s!"sizes (all >= d, one = d, d <= L): {sizeB B.L T.mins.toList B.d}"
    if symmetric then
      IO.println s!"symmetry (generators preserve code and list): {symmetryB T.rows T.mins T.gens B.imgs}"
      IO.println s!"representatives meet every orbit: {repsB T.gens (T.symLeaves.map Prod.fst) T.words}"
      IO.println s!"leaves cover: {T.symLeaves.all (fun p => coversB (coverFuel p.2) p.2)}"
    else
      IO.println s!"leaves cover: {coversB (coverFuel T.plainLeaves) T.plainLeaves}"
    IO.println s!"NOT CERTIFIED {B.name}: a check failed"
    return 1
  IO.println s!"checks passed ({t1 - t0} ms): isotropy, {T.mins.size} listed sets uncorrectable, sizes, {if symmetric then s!"{T.gens.size} generators, {T.symLeaves.length} representatives, " else ""}cover"
  -- leaves
  let mut k := 0
  let mut allOk := true
  for (r, sha, u) in B.leaves do
    let units := match r with
      | some q => (q, true) :: u
      | none => u
    let leafOk ← if mode == "combine" then do
        let h := sha256 (renderInstance B units).toUTF8
        if h == sha then pure true else do
          IO.println s!"leaf {k}: hash mismatch (rendered {h}, recorded {sha})"
          pure false
      else do
        let typedUnits ← IO.ofExcept (units.mapM fun (v, b) =>
          if h : v < B.n then (pure (⟨v, h⟩, b) : Except String _) else throw "bad unit")
        let f := certFormula T.rows B.L T.mins.toList typedUnits
        let path := s!"{proofDir}/leaf{k}.lrat"
        let proof ← LRAT.loadLRATProof path
        let proof ← IO.ofExcept (Lean.Meta.Tactic.BVDecide.LRAT.trim proof)
        if LRAT.check proof f then pure true else do
          IO.println s!"leaf {k}: LRAT check failed"
          pure false
    if leafOk then
      IO.println s!"leaf {k} rep={r.map toString |>.getD "-"} units={u.length}: {if mode == "combine" then "hash matches a CertifyList-certified instance" else "LRAT proof checked"}"
    allOk := allOk && leafOk
    k := k + 1
  if !allOk then
    IO.println s!"NOT CERTIFIED {B.name}: a leaf is not established"
    return 1
  let counts := leadCounts T.rows T.mins.toList B.d
  let t2 ← IO.monoMsNow
  IO.println s!"CERTIFIED CODE {B.name}: complete through {B.L}, distance {B.d}, minimum-size sets by exponent {counts} ({mode} mode, {t2 - t0} ms)"
  return 0
