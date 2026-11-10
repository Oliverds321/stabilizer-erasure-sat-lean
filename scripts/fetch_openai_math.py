#!/usr/bin/env python3
"""Fetch OpenAI's verified SAT development and assemble the compiled solver sources.

usage: python -I scripts/fetch_openai_math.py [--out DIR] [--source CHECKOUT]

Downloads https://codeload.github.com/openai/math/tar.gz/<commit> (the commit of
third_party/openai-math-4eaee875/upstream-manifest.json), or reads an existing
checkout given by --source, and

1. extracts the Lean files of the solver's import closure into DIR/upstream/
   and checks each against the SHA-256 of upstream-manifest.json;
2. copies them to DIR/overlay/, replaces the files of
   third_party/openai-math-4eaee875/modified/, and checks every file of
   DIR/overlay/ against overlay-manifest.json.

DIR/overlay/ is then the solver source tree of the build (resolution step 2 in
docs/BUILD_434.md). DIR defaults to ./openai-math. Nothing is executed from the
download. Exit code 0 when every hash matches.
"""
import hashlib
import io
import json
import shutil
import sys
import tarfile
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TP = ROOT / "third_party" / "openai-math-4eaee875"


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def main():
    args = sys.argv[1:]
    out = Path(args[args.index("--out") + 1]) if "--out" in args else Path("openai-math")
    source = Path(args[args.index("--source") + 1]) if "--source" in args else None
    upstream = json.loads((TP / "upstream-manifest.json").read_text(encoding="utf-8"))
    overlay = json.loads((TP / "overlay-manifest.json").read_text(encoding="utf-8"))
    commit = upstream["commit"]
    wanted = {row["path"]: row["sha256"] for row in upstream["files"]}  # paths like lean/OAI/...
    got = {}
    if source is not None:
        for rel in wanted:
            p = source / rel
            if p.is_file():
                got[rel] = p.read_bytes()
    else:
        url = f"https://codeload.github.com/openai/math/tar.gz/{commit}"
        print(f"downloading {url}", flush=True)
        with urllib.request.urlopen(url) as response:
            with tarfile.open(fileobj=response, mode="r|gz") as tar:
                for member in tar:
                    if not member.isfile():
                        continue
                    rel = member.name.split("/", 1)[1] if "/" in member.name else member.name
                    if rel in wanted:
                        got[rel] = tar.extractfile(member).read()
    errors = []
    for rel, digest in sorted(wanted.items()):
        if rel not in got:
            errors.append(f"missing upstream file: {rel}")
        elif sha256(got[rel]) != digest:
            errors.append(f"upstream hash mismatch: {rel}")
    print(f"upstream: {len(got)}/{len(wanted)} files, {len(wanted) - len(errors)} verified")
    if errors:
        for e in errors[:50]:
            print("ERROR", e)
        return 1
    for name in ("upstream", "overlay"):
        if (out / name).exists():
            shutil.rmtree(out / name)
    for rel, data in got.items():
        for name in ("upstream", "overlay"):
            dest = out / name / rel[len("lean/"):]
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
    modified = 0
    for p in sorted((TP / "modified").rglob("*.lean")):
        rel = p.relative_to(TP / "modified")
        shutil.copyfile(p, out / "overlay" / rel)
        modified += 1
    for row in overlay["files"]:
        p = out / "overlay" / row["path"][len("lean/"):]
        if not p.is_file() or sha256(p.read_bytes()) != row["overlay_sha256"]:
            errors.append(f"overlay mismatch: {row['path']}")
    print(f"overlay: {len(overlay['files'])} files, {modified} replaced by modified copies, "
          f"{len(overlay['files']) - len(errors)} verified; written to {out / 'overlay'}")
    for e in errors[:50]:
        print("ERROR", e)
    print("OK" if not errors else f"FAILED ({len(errors)} errors)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
