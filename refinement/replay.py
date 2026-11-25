"""Replay the smaller-side census against a built, pinned P118 and Section 4 project."""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

MODULES = ["CutSizeIncidence", "SizeCatalogue", "SizeFamilyCertificate", "SizeFamilySeries"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SOURCE = Path(__file__).resolve().parent


def run(argv, cwd, path, env=None):
    start = time.monotonic()
    with path.open("x", encoding="utf8") as log:
        print(json.dumps({"time": datetime.now(timezone.utc).isoformat(), "cwd": str(cwd), "argv": argv}), file=log, flush=True)
        process = subprocess.run(argv, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT)
        print(json.dumps({"exit": process.returncode, "seconds": round(time.monotonic()-start,3)}), file=log)
    if process.returncode:
        raise RuntimeError(f"{process.returncode} from {argv[0]}; see {path}")
    return path.read_text(encoding="utf8")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--project", required=True, type=Path, help="prepared P118 + Section 4 checkout")
    p.add_argument("--out", required=True, type=Path, help="a new directory for a clean replay")
    args = p.parse_args()
    project, out = args.project.resolve(), args.out.resolve()
    if out.exists():
        p.error("--out must name a new directory so that prior evidence is preserved")
    out.mkdir(parents=True)
    build = out / "build"
    build.mkdir()
    source = out / "src"
    source.mkdir()
    for name in [*MODULES, "SizeAxioms"]:
        shutil.copy2(SOURCE / (name + ".lean"), source)
    table = project / "ProofBench" / "PROBLEMS" / "P118" / "ArbitraryCutTable.lean"
    run([sys.executable, str(SOURCE / "make_catalogue.py"), str(table), "--check"], project, out/"00-regenerate.log")
    # Lake supplies paths from its manifest. Absolute paths preserve their meaning when changing cwd.
    code = "import json,os;print(json.dumps({k:os.environ.get(k,'') for k in ('LEAN_PATH','PATH')}))"
    lake_env = json.loads(subprocess.check_output(["lake","env",sys.executable,"-c",code], cwd=project, text=True).strip())
    env = os.environ.copy()
    env.update(lake_env)
    dependency_paths = [str((project / s).resolve()) for s in lake_env["LEAN_PATH"].split(os.pathsep) if s]
    env["LEAN_PATH"] = os.pathsep.join([str(build), *dependency_paths])
    env["LEAN_NUM_THREADS"] = "1"
    version = run(["lean","--version"], source, out/"01-version.log",env)
    if "4.34.1" not in version:
        raise RuntimeError("Replay expects Lean 4.34.1")
    for i, name in enumerate(MODULES, 2):
        run(["lean","-j","1","-M","6500","-o",str(build/(name+".olean")),name+".lean"], source,out/f"{i:02d}-{name}.log", env)
    audit = run(["lean","-j","1","SizeAxioms.lean"], source,out/"06-axioms.log",env)
    expected = [s.split()[-1] for s in (source/"SizeAxioms.lean").read_text(encoding="utf8").splitlines() if s.startswith("#print axioms ")]
    records = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit))
    records.update({s:"" for s in re.findall(r"'([^']+)' does not depend on any axioms",audit)})
    if len(records) != len(expected):
        raise RuntimeError(f"expected {len(expected)} axiom reports and obtained {len(records)}")
    for name in expected:
        matches = [s for full,s in records.items() if full.endswith("." + name)]
        if len(matches)!=1 or {s.strip() for s in matches[0].split(",") if s.strip()}-ALLOWED:
            raise RuntimeError(f"unexpected axioms for {name}: {matches}")
    run(["leanchecker","-v",*MODULES], source,out/"07-leanchecker.log",env)
    manifest = {f.name:sha(f) for f in sorted(source.glob("*.lean"))}
    manifest["generator.py"]=sha(SOURCE / "make_catalogue.py")
    manifest["replay.py"]=sha(SOURCE / "replay.py")
    manifest["ArbitraryCutTable.lean"]=sha(table)
    (out/"summary.json").write_text(json.dumps({"modules":MODULES,"axioms":records,"sources":manifest},indent=2),encoding="utf8")
    print(f"Verified {len(MODULES)} modules and {len(records)} axiom reports. Evidence: {out}")


if __name__=="__main__":
    main()
