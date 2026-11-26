# Reproduce Figures 1 and 2

These are the original ReportLab drawing programs for Mengfei Feng's *Sharp Fixed Cut Tests for the 3D Corner Lemma*. Figure 1 shows the alternating matching with edges (1, 3), (2, 6), and (4, 5), alongside its three-leaf star. Figure 2 shows two triples of separator pairs on a 24-cycle. [Preprint](https://doi.org/10.5281/zenodo.24550238)

## Generate the vector PDFs

From the root of the software bundle, run the following commands with Python 3.12. The reference build used CPython 3.12.14, ReportLab 5.0.1, and pypdf 6.21.4. Choose a new output directory for each run.

```sh
python -m pip install -r figures/requirements.txt
python figures/reproduce.py --out ../cut-figures
```

The command writes `connected-witness.pdf` and `cycle24-triples.pdf`. It checks each complete file, its page dimensions, and the SHA-256 of the decoded PDF drawing stream. The stream includes the vector geometry, text, colours, and line styles. The journal-preparation files `Fig1.pdf` and `Fig2.pdf` have the same drawing streams and use embedded font subsets.

| Figure | Width × height (PDF points) | Vector PDF bytes | Drawing-stream SHA-256 |
| --- | --- | ---: | --- |
| 1 | 410 × 117 | 2,531 | `1b12635a45154356ab1ef5e1e91faff7d4fb5b7d994d62d6585762061c93a72a` |
| 2 | 405 × 154 | 5,733 | `72da443dc4f269cacee101f51c59dd5eaf1b27ca0e1403852ec4ac77e69ffbb1` |

## Reproduce the font-embedded journal files

For an exact copy of the journal PDFs, supply local licensed copies of the regular and bold Arial TrueType files used in their preparation. The command checks the full font fingerprints and embeds subsets while preserving the original character advances. The default vector build above needs only the Python packages.

```sh
python figures/reproduce.py --out ../cut-figures-journal --regular-font /path/to/arial.ttf --bold-font /path/to/arialbd.ttf
```

| Local font | Expected SHA-256 |
| --- | --- |
| Arial Regular (`ArialMT`) | `edfbd22a3d088fc2f5d7c79b8c9c732df6dc878a60f0a80be0f92a3c7a634404` |
| Arial Bold (`Arial-BoldMT`) | `4d59199834e7439c67ea4949407639961060b21b173833f566eb60ac6fd8f5af` |

| Additional output | Bytes | Complete PDF SHA-256 |
| --- | ---: | --- |
| `Fig1.pdf` | 73,368 | `27d7812dd96e92cd3a72648bc5a90329f0bca9a444dbe3c195b485a7fcac1d5c` |
| `Fig2.pdf` | 76,573 | `4c2497c4b69646ca54012e203d5b861940c4ae11f2a5bf4265fc755a31544ccb` |

## Edit a drawing

Edit a working copy of `scripts/plot_connected_witness.py` or `scripts/plot_cycle_triples.py`. Both scripts are preserved byte for byte. Figure 1 reads its six vertices and first matching from `evidence/referee/cover-aware-count.json`, an extract of the project's enumeration output. Figure 2 defines the endpoint pairs in `TRIPLES` at the top of its script. To render an edited copy, use the original programs directly from the `figures` directory.

```sh
cd figures
python -c "from pathlib import Path; Path('manuscripts/figures').mkdir(parents=True, exist_ok=True)"
python scripts/plot_connected_witness.py
python scripts/plot_cycle_triples.py
```

The edited PDFs appear under `manuscripts/figures/` within that working copy.

## Attribution and licenses

OpenAI Codex wrote the original drawing programs using ReportLab. The repository's Apache-2.0 license covers the project-owned drawing code and reproducibility materials. [Software license](../LICENSE)

Attribute the original artwork to Mengfei Feng, *Sharp Fixed Cut Tests for the 3D Corner Lemma*, Figures 1 and 2 (2026). The author licensed the artwork under CC BY 4.0. [Preprint](https://doi.org/10.5281/zenodo.24550238) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
