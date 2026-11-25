# License and attribution

Apache License 2.0 applies to this project’s own software contributions, including the Lean proof modules and proof fragments, Python verification programs, and project source code displayed in the generated reader. The accompanying instructions, claim index and manifests identify the source files and the inputs needed to reproduce the results. [License text](LICENSE)

## Mathematics

Romain Bourneuf, Johannes Carmesin, Jan Kurkofka and Tim Planken give the cube and graph corner lemmas in §4 of *An approximate cactus-decomposition for vertex-connectivity*. The fixed-cut tests extend the cube setting of their Lemma 4.1. The finite graph formalization includes their Lemma 4.14. Krishnan Balasubramanian records the ordinary three-cube matching polynomial, including the matching counts 42 and 9 used in the enumeration. [Original corner lemmas](https://arxiv.org/abs/2611.01772v1) · [Matching polynomial, §3(c)](https://www.mdpi.com/2073-8994/15/2/557)

## Benchmark and dependencies

LPBench supplies the P118 statement, the original cube definitions and the finite graph separation interface. The reproduction procedure reads those files from the user’s own checkout of commit `4eb96eb41fa762e44f7015c328e27d5a9df99239`. It inserts the project’s helper and proof-body fragments into that checkout. The Lean modules import the named interfaces there. The rights and terms for the external source remain with its respective rightsholders. [Pinned LPBench source](https://github.com/lp-bench/lp-bench/tree/4eb96eb41fa762e44f7015c328e27d5a9df99239) · [LPBench benchmark paper](https://doi.org/10.5281/zenodo.24195212)

The project uses Lean 4.34.1 and the Mathlib revision recorded in the pinned Lake manifest. Historical verification receipts identify QEDRank and Lean Comparator by revision and checked statement. Obtain these tools from their own distributions. [Lean](https://github.com/leanprover/lean4/tree/5045d0056413266e57c625dcd7c365b10e377c52) · [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612) · [QEDRank](https://github.com/lp-bench/QEDRank/tree/82417e2269f464c2ce64656ae8dc90c7839595ec) · [Comparator](https://github.com/leanprover/comparator/tree/19e111e2141cf333c7daff0f64c5f24acc91dd2e)

