"""Verify the source bundle and reproduce the manuscript checks (Python 3.10+)."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
BASE = ROOT / "base"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
GROUPS = {
    "witness": ["Section3Probe", "ParallelDirections"],
    "count": ["CountingProbe"],
    "graph": ["GraphDeclarations", "LowDimensions", "StarOrder"],
    "cycle": ["NontrivialNestedCycle", "CycleAssertions"],
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def integrity():
    expected = {}
    for line in (ROOT / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        digest, name = line.split("  ", 1)
        target = ROOT / name
        require(re.fullmatch(r"[a-f0-9]{64}", digest) and name not in expected, "Invalid manifest entry")
        require(target.resolve().is_relative_to(ROOT) and target.is_file(), "Missing package member: " + name)
        require(sha(target) == digest, "Changed package member: " + name)
        expected[name] = digest
    print(f"Verified {len(expected)} input file digests.", flush=True)


def new_output(path):
    path = path.resolve()
    require(not path.is_relative_to(ROOT), "Choose a new output directory outside the extracted bundle")
    path.mkdir(parents=True, exist_ok=False)
    return path


def run(command, cwd, log, env=None):
    print(log.stem, flush=True)
    start = time.monotonic()
    with log.open("xb") as destination:
        result = subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                                stdout=destination, stderr=subprocess.STDOUT)
    elapsed = round(time.monotonic() - start, 3)
    print(f"  exit {result.returncode} in {elapsed}s", flush=True)
    require(result.returncode == 0, f"{log.stem} failed. Consult {log}")
    return log.read_text(encoding="utf-8")


def models(out):
    # Some original programs write data beside their source. Stage them away from the bundle.
    scripts = out / "programs"
    shutil.copytree(ROOT / "models", scripts)
    for path in (ROOT / "checks").glob("*.py"):
        shutil.copy2(path, scripts / path.name)
    shutil.copy2(BASE / "checks" / "enumerate_cuts.py", scripts)
    for name in ["check_math", "enumerate_cuts", "size_counts", "direct_enumeration", "audit_star",
                 "verify_diagrams", "audit_cycles", "check_local_steps"]:
        command = [sys.executable, "-E", "-B", scripts / (name + ".py")]
        if name == "audit_star":
            command.extend(["--out", scripts])
        run(command, scripts, out / (name + ".log"))
    def read(path):
        return json.loads(path.read_text(encoding="utf-8"))
    sizes = read(out / "size_counts.log")
    enumeration = read(scripts / "direct-enumeration.json")
    table = {(x["two"], x["three"], x["four"]): x["families"] for x in sizes["coefficients"]}
    second = {(x["size_2"], x["size_3"], x["size_4"]): x["coefficient"] for x in enumeration["monomials"]}
    require(table == second and len(table) == 9 and sum(table.values()) == 1116, "Coefficient tables disagree")
    require(sizes["candidate_four_cut_families"] == enumeration["tested_four_cut_families"] == 10334625,
            "Unexpected four-family denominator")
    witness, basic = read(out / "check_math.log"), read(out / "enumerate_cuts.log")
    require(witness["threshold_one_witness_cut_checks"] == 1016 and
            [r["two_cut_families"] for r in basic["rings"]] == [144]*4, "Unexpected witness results")
    star, graph = read(scripts / "star-audit.json"), read(scripts / "model-results.json")
    require(star["oriented_rows_including_boundaries"] == 2048 and graph["input_diagrams"] == 4572 and
            graph["checks"]["graph_lifted_cut_checks"] == 334872, "Unexpected graph denominator")
    cycles = read(scripts / "cycles-data.json")["diagrams"]
    require(cycles["all_crossing"]["all_flower_solutions_up_to_pole_order"] == [{"poles": ["000", "111"], "ell": 1}]
            and cycles["nested_pair"]["all_flower_solutions_up_to_pole_order"] == [], "Unexpected cycle profiles")
    save(out / "models.json", {"status": "passed", "witness_checks": 1016, "known_ring_minimum_family_counts": [144]*4,
         "candidate_families_per_enumeration": 10334625, "families": sum(table.values()), "coefficients": sizes["coefficients"],
         "star_oriented_cuts": 2048, "finite_graph_diagrams": 4572, "lifted_cuts": 334872,
         "cycle_oriented_cuts": 512, "first_cycle_poles": ["000", "111"], "mixed_cycle_flowers_at_two": 0})
    print("All finite checks passed.", flush=True)


def capture(command, cwd):
    return subprocess.check_output(list(map(str, command)), cwd=cwd, encoding="utf-8").strip()


def project_environment(project):
    manifest = json.loads((BASE / "manifest.json").read_text(encoding="utf-8"))
    require(capture(["git", "rev-parse", "HEAD"], project) == manifest["upstream"]["commit"], "Unexpected baseline")
    for path, expected in {**manifest["pinned_inputs"], **manifest["materialized_sha256"]}.items():
        require(sha(project / path) == expected, "Pinned source changed: " + path)
    locked = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))["packages"]
    for dep in locked:
        repo = project / ".lake/packages" / dep["name"]
        require(capture(["git", "rev-parse", "HEAD"], repo) == dep["rev"], "Package revision changed: " + dep["name"])
        require(not capture(["git", "--no-optional-locks", "status", "--porcelain", "--untracked-files=no"], repo),
                "Tracked package source changed: " + dep["name"])
    script = "import os,json; print(json.dumps({k:os.environ[k] for k in ('PATH','LEAN_PATH')}))"
    lake = json.loads(capture(["lake", "env", sys.executable, "-c", script], project))
    env = dict(os.environ, **lake)
    env["LEAN_NUM_THREADS"] = "1"
    for key in ("PATH", "LEAN_PATH"):
        env[key] = os.pathsep.join(str((project / p).resolve()) for p in env[key].split(os.pathsep) if p)
    return env, [dep["name"] for dep in locked]


def printed_axioms(source, output):
    names = re.findall(r"^#print axioms (\S+)", source.read_text(encoding="utf-8"), re.M)
    results = {}
    entries = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.M)
    entries.extend((n, "") for n in re.findall(r"^'([^']+)' does not depend on any axioms", output, re.M))
    for name in names:
        matches = [(k, v) for k, v in entries if k == name or k.endswith("." + name)]
        require(len(matches) == 1, "Missing or ambiguous axiom output for " + name)
        full, axioms = matches[0]
        values = sorted(x.strip() for x in axioms.split(",") if x.strip())
        require(set(values) <= ALLOWED, "Unexpected axioms for " + full)
        results[full] = values
    require(len(names) == len(entries), "Unexpected number of inspected declarations")
    return results


def probes(project, series, groups, out):
    project = project.resolve(strict=True)
    env, dependencies = project_environment(project)
    src, obj = out / "src", out / "build"
    src.mkdir()
    obj.mkdir()
    search = [str(obj)]
    if "count" in groups:
        require(series is not None, "The count probe needs --refinement with the output of refinement/replay.py")
        series = series.resolve(strict=True)
        for name in ["CutSizeIncidence", "SizeCatalogue", "SizeFamilyCertificate", "SizeFamilySeries"]:
            file = name + ".lean"
            require(sha(series / "src" / file) == sha(ROOT / "refinement" / file), "Changed refinement source " + file)
            require((series / "build" / (name + ".olean")).is_file(), "Missing refinement object " + name)
        search.append(str(series / "build"))
    env["LEAN_PATH"] = os.pathsep.join([*search, env["LEAN_PATH"]])
    version = run(["lean", "--version"], src, out / "version.log", env).strip()
    require("4.34.1" in version and "5045d005" in version, "Unexpected Lean version")
    modules = [name for group in groups for name in GROUPS[group]]
    records = {}
    for name in modules:
        origin = (BASE / "checks" if name == "NontrivialNestedCycle" else ROOT / "probes") / (name + ".lean")
        copy = src / origin.name
        shutil.copy2(origin, copy)
        result = run(["lean", "-j", "1", "-M", "6500", "-o", obj / (name + ".olean"), copy.name], src,
                     out / (name + ".log"), env)
        records[name] = printed_axioms(copy, result)
    output = run(["leanchecker", "-v", *modules], src, out / "leanchecker.log", env)
    for name in modules:
        require(re.search(r"^replaying " + re.escape(name) + r"$", output, re.M), "No kernel replay for " + name)
    save(out / "probes.json", {"status": "passed", "lean": version, "groups": groups, "fresh_modules": modules,
         "pinned_dependencies": dependencies, "materialized_base_files": 35, "axioms_per_module": records,
         "unique_axiom_queries": len(set().union(*(set(r) for r in records.values()))),
         "objects": {name: sha(obj / (name + ".olean")) for name in modules}})
    print("Selected probe builds, transitive axioms and kernel replay passed.", flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    commands = p.add_subparsers(dest="action", required=True)
    commands.add_parser("integrity", help="verify all named source, metadata and figure hashes")
    models_p = commands.add_parser("models", help="recompute the eight independent finite checks")
    models_p.add_argument("--out", type=Path, required=True, help="new output directory")
    lean_p = commands.add_parser("probes", help="compile and kernel-replay the chapter probes in a built, pinned project")
    lean_p.add_argument("--project", type=Path, required=True)
    lean_p.add_argument("--refinement", type=Path, help="output directory from refinement/replay.py")
    lean_p.add_argument("--group", nargs="+", choices=GROUPS, default=list(GROUPS))
    lean_p.add_argument("--out", type=Path, required=True, help="new output directory")
    args = p.parse_args()
    integrity()
    if args.action == "models":
        models(new_output(args.out))
    elif args.action == "probes":
        probes(args.project, args.refinement, list(dict.fromkeys(args.group)), new_output(args.out))


if __name__ == "__main__":
    main()
