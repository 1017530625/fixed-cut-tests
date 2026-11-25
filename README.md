# Sharp Fixed Cut Tests for the 3D Corner Lemma

Version 1.0.0 · 25 November 2026 · Lean 4.34.1

The [claim index](CLAIMS.md) links the manuscript results to the corresponding Lean declarations. For offline reading, open fixed-cut-tests-source.html in a browser after extracting the software. The project’s software contributions are available under the [Apache License 2.0](LICENSE). [Sources and attribution](RIGHTS.md) identify the original mathematical results and the external software that the build imports.

## Start with the finite checks

Use Python 3.10 or newer and run the commands inside the extracted version directory. On Windows, `py -3.12` can replace `python`. Choose unused sibling directories for output. The Python checks require only the standard library.

```sh
python verify.py integrity
python verify.py models --out ../cut-models
```

The second command independently constructs the eight witnesses and checks 1,016 pairs of a witness and an unoriented proper cut. It enumerates 10,334,625 candidate four-cut families twice and compares all nine coefficients. It checks 2,048 oriented cut instances on the fixed four-vertex star, 334,872 lifted cuts across 4,572 small graph diagrams, and all 512 oriented cuts of the two triples on the 24-cycle. The local proof-step enumeration for the finite graph corner lemma and the individual command outputs accompany `models.json`. Each numerical check has a finite range. The Lean declarations give the general statements.

## Build the Lean proofs

Install Git and the matching Lean toolchain. The baseline fixes the dependency revisions in its Lake manifest. Keep the extracted bundle, input repository, and build directories separate. Git and Lake need network access for a first installation. The Lean and Mathlib cache requires several GB of disk space. [Lean installation](https://lean-lang.org/install/) · [pinned LPBench source](https://github.com/lp-bench/lp-bench/tree/4eb96eb41fa762e44f7015c328e27d5a9df99239)

```sh
git clone https://github.com/lp-bench/lp-bench.git ../lpbench-input
git -C ../lpbench-input checkout --detach 4eb96eb41fa762e44f7015c328e27d5a9df99239
elan toolchain install leanprover/lean4:v4.34.1
python base/reproduce.py --upstream ../lpbench-input --work ../cut-base --kernel-replay
python refinement/replay.py --project ../cut-base/project --out ../cut-refinement
python verify.py probes --project ../cut-base/project --refinement ../cut-refinement --out ../cut-probes
```

The first runner reconstructs the frozen P118 from the reader's checkout and the two added proof fragments. It verifies 35 materialized sources, builds the base modules, inspects transitive axioms, runs numerical checks and replays eight designated base modules with `leanchecker`. Its timestamped run directory contains the individual logs and `verified.json`. The build can reuse a prebuilt package directory by appending `--packages ../lpbench-input/.lake/packages` to the base command. The runner checks the expected revisions and tracked source state of all 11 dependencies. A readable cache must contain matching compiled packages. A reader starting offline also needs a local clone that contains the pinned commit.

The second runner regenerates and checks the size catalogue and compiles its four Lean modules. It checks 19 axiom queries and replays the modules. The third builds the seven manuscript probes and their packaged mixed-example dependency into fresh output objects. It checks all transitive axiom reports printed by those sources, then replays the freshly compiled modules. The accepted axiom set is `propext`, `Classical.choice`, and `Quot.sound`. For a shorter replay, select one or more groups. Only the `count` group requires the refinement output.

```sh
python verify.py probes --project ../cut-base/project --group cycle --out ../cut-cycle
python verify.py probes --project ../cut-base/project --group witness graph --out ../cut-witness-graph
python verify.py probes --project ../cut-base/project --group count --refinement ../cut-refinement --out ../cut-count
```

The `cycle` command compiles both `base/checks/NontrivialNestedCycle.lean` and `probes/CycleAssertions.lean`, including the proof that the mixed diagram is uniform and has no flower for any natural threshold. Counts for complementary sides use one representative per cut and retain the cube labels. The optional `checks/RestrictedFamilyAudit.lean` gives a second inclusion–exclusion derivation for the two restricted counts. Run `lake env lean` on that file's absolute path from the built base project. Optional finite symmetry checks run with `python checks/explicit_orbits.py ../orbits.json` and `python checks/burnside_cycles.py ../fixed.json`.

## Independent comparisons and scope

The historical [verification receipts](comparison-receipts.json) distinguish the frozen benchmark theorem `P118` from the finite graph theorem `PaperCorner.key_lemma_4_14`. These records identify earlier proof sources by SHA-256. The source expressions in this release use the pinned public interfaces. The recorded local QEDRank first-layer run and Linux Comparator run for P118 used the official tools on this benchmark statement. The second Linux Comparator run used a separately specified project challenge for Lemma 4.14. The receipts identify their input hashes, source revisions, exit status and full-log digests. The reproduction commands above execute the Lean kernel and finite checks. Independent Comparator and QEDRank evidence has its own scope and date. Source-to-paper semantic sign-off rests with the human author. [QEDRank](https://github.com/lp-bench/QEDRank/tree/82417e2269f464c2ce64656ae8dc90c7839595ec) · [Lean Comparator](https://github.com/leanprover/comparator/tree/19e111e2141cf333c7daff0f64c5f24acc91dd2e)

The mathematical source for the 3D Corner Lemma is Bourneuf, Carmesin, Kurkofka and Planken, §4. The eight-witness criterion, optimal labelled test families, counting refinement, graph lifting and example probes are indexed individually. The published cube matching coefficients 42 and 9 have an earlier source. [Original mathematical paper](https://arxiv.org/abs/2611.01772v1) · [Balasubramanian, §3(c)](https://doi.org/10.3390/sym15020557)
