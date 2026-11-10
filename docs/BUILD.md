# How the Lean development is compiled

The compiled graph behind the theorems of the manuscript has 6,157 modules. It
is compiled module by module, one `lean` process per module, and is not a `lake`
project. It has been built on Windows 11 only.

## What is in the graph

| Part | Modules | Source |
|---|---:|---|
| Mathlib, its dependencies and OpenAI's verified SAT solver | 5,242 | fetched (see below) |
| Mathlib modules outside the solver's import closure | 190 | Mathlib `d13f23b7` (fetched) |
| This development | 725 | `lean/` |

## Toolchain and dependencies

- Lean 4.34.1 (official release, commit `5045d0056413266e57c625dcd7c365b10e377c52`).
- Mathlib `d13f23b7` with Batteries, Aesop, Qq, ProofWidgets, Plausible,
  LeanSearchClient, ImportGraph and Cli, at the revisions listed in
  `third_party/openai-math-4eaee875/records/pinned-dependencies.json`.
- OpenAI's verified SAT development (`github.com/openai/math`, commit
  `4eaee87548250b2682affda7d05d947c05554bae`): 2569 Lean files, of which 108
  are compiled in a modified form (21 proof-internal refactors that leave every
  exported statement unchanged, 87 import-only edits). The command

      python -I scripts/fetch_openai_math.py --out DIR

  downloads the upstream commit, checks every file against
  `third_party/openai-math-4eaee875/upstream-manifest.json`, applies the modified
  files of `third_party/openai-math-4eaee875/modified/` and checks the result,
  `DIR/overlay/`, against `overlay-manifest.json`.

## Module resolution

A module `A.B` is `lean/A/B.lean` if that file exists; otherwise it is a module of
the solver (`DIR/overlay/A/B.lean`) or of one of the dependency packages. No
module name occurs in more than one of these places.

## Compiler options

Every module of this development, of Mathlib and of the solver is compiled with

    -DautoImplicit=false -DmaxSynthPendingDepth=3

The modules of this development marked `"compatibility_options": true` in
[`build-plan.json`](build-plan.json) additionally get the two options that Lean
4.34 documents for proof scripts written for earlier versions:

    -Dbackward.isDefEq.respectTransparency=false -Dbackward.defeqAttrib.useBackward=true

Solver and Mathlib modules never get them.

A module is compiled, after all its imports, with

    lean -j1 -M4096 <options> -o OUT/A/B.olean -i OUT/A/B.ilean lean/A/B.lean

where `LEAN_PATH` points to the compiled imports. The memory limit is 5120 MiB for
modules that import the solver's final theorem. One process that loads the solver
graph peaks near 7 GiB of physical memory.

## Audits

- `tools/audit/FinalTheoremsAudit.lean` runs `#print axioms` on each of the
  147 theorems cited in the manuscript.
- `tools/audit/ModuleAudit.lean` collects the axioms of every constant declared in
  the 34 final modules (2,386 declarations) and fails on any axiom other than
  `propext`, `Classical.choice` and `Quot.sound`.

Both are compiled like a module of the development, against the compiled graph.

## Kernel replay

`leanchecker MODULE`, shipped with the toolchain, loads the compiled imports of a
module and re-checks every declaration of that module in the kernel,
independently of the elaborator that produced the object file. All 6,157 modules
of the graph pass.

`leanchecker` treats its argument as a prefix: `A.B` also replays `A.B.C`, in
parallel tasks. Set `LEAN_NUM_THREADS=1` to keep the memory use of one call low,
and do not call it without a module argument, which replays everything on the
search path at once.

## Scope

- Built and checked on Windows 11 only.
- The scheduler that ran the 6,157 compilations on the author's machine, with a
  memory budget per module, is not part of this repository. Everything a
  compilation depends on is stated above: the toolchain, the pinned sources, the
  options of each module and its imports.
