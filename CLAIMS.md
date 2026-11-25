# Manuscript claims and Lean declarations

All source paths begin at the extracted version directory. The links open the corresponding declaration in the Lean source file at the selected revision. The package contains the exact Lean input for every listing. For fresh builds, use the commands in the [reproduction guide](README.md).

| Manuscript | Claim | Lean declaration | Source and line | Probe group |
| --- | --- | --- | --- | --- |
| Theorem 3.1 | [Eight-witness criterion](base/overlay/ProofBench/PROBLEMS/P118/ArbitraryCuts.lean#L224) | `CornerArbitraryCuts.sufficient_iff_complete` | `base/overlay/ProofBench/PROBLEMS/P118/ArbitraryCuts.lean:224` | `witness` |
| Theorem 3.1 | [The two witnesses for a fixed six-cycle](base/overlay/ProofBench/PROBLEMS/P118/ArbitraryCuts.lean#L202) | `CornerArbitraryCuts.ring_sufficient_iff_complete` | `base/overlay/ProofBench/PROBLEMS/P118/ArbitraryCuts.lean:202` | `witness` |
| Corollary 3.2 | [Parity-class cover](base/overlay/ProofBench/PROBLEMS/P118/CoverAware.lean#L856) | `CoverAware.parity_sufficient` | `base/overlay/ProofBench/PROBLEMS/P118/CoverAware.lean:856` | `witness` |
| Corollary 3.2 | [Two cuts suffice on a prescribed six-cycle](base/overlay/ProofBench/PROBLEMS/P118/CoverAware.lean#L917) | `CoverAware.ring_minimum_two` | `base/overlay/ProofBench/PROBLEMS/P118/CoverAware.lean:917` | `witness` |
| Corollary 3.2 | [Two cuts are necessary among unrestricted cuts](base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean#L43) | `CornerArbitraryCuts.ring_sufficient_card_ge_two` | `base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean:43` | `witness` |
| Corollary 3.3 | [Four universal tests are necessary](base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean#L32) | `CornerArbitraryCuts.sufficient_card_ge_four` | `base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean:32` | `witness` |
| Corollary 3.3 | [Four parallel edges attain the bound](probes/ParallelDirections.lean#L24) | `ManuscriptParallelDirections.optimal` | `probes/ParallelDirections.lean:24` | `witness` |
| Proposition 4.1 | [Pair multiplicities by smaller-side size](refinement/CutSizeIncidence.lean#L51) | `CornerArbitraryCuts.SizeRefinement.pair_multiplicity_by_smaller_side` | `refinement/CutSizeIncidence.lean:51` | `count` |
| Theorem 4.2 | [Optimal families cover by disjoint witness pairs](base/overlay/ProofBench/Research/WitnessPairing.lean#L63) | `CornerArbitraryCuts.complete_four_iff_pairing` | `base/overlay/ProofBench/Research/WitnessPairing.lean:63` | `count` |
| Theorem 4.2 | [Generating polynomial over a commutative semiring](refinement/SizeFamilySeries.lean#L156) | `CornerArbitraryCuts.SizeRefinement.size_series_formula` | `refinement/SizeFamilySeries.lean:156` | `count` |
| Theorem 4.2 | [1,116 labelled families](base/overlay/ProofBench/PROBLEMS/P118/ArbitraryCutCensus.lean#L84) | `CornerArbitraryCuts.minimumFamilies_card` | `base/overlay/ProofBench/PROBLEMS/P118/ArbitraryCutCensus.lean:84` | `count` |
| Table 2 | [Nine coefficients](probes/CountingProbe.lean#L32) | `ManuscriptCountingCheck.expanded` | `probes/CountingProbe.lean:32` | `count` |
| Theorem 5.1 | [Fixed four-vertex star](base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean#L15) | `CornerArbitraryCuts.on_star_iff_complete` | `base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean:15` | `graph` |
| Theorem 5.1 | [Uniform sufficiency on all connected finite simple graphs](base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean#L19) | `CornerArbitraryCuts.connected_iff_complete` | `base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean:19` | `graph` |
| Theorem 5.1 | [Uniform sufficiency on all finite simple graphs](base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean#L10) | `CornerArbitraryCuts.graph_iff_complete` | `base/overlay/ProofBench/PROBLEMS/P118/GeneralGraphCuts.lean:10` | `graph` |
| Theorem 5.1 | [Star order for every nontrivial oriented cut](probes/StarOrder.lean#L10) | `ManuscriptGraphCheck.star_order_nontrivial` | `probes/StarOrder.lean:10` | `graph` |
| Theorem 5.2 | [Order of the lifted separation](base/overlay/ProofBench/Research/CubicalDiagrams.lean#L228) | `CubicalDiagrams.order_lift` | `base/overlay/ProofBench/Research/CubicalDiagrams.lean:228` | `graph` |
| Theorem 5.2 | [Recover the oriented coordinate separation](base/overlay/ProofBench/Research/CubicalDiagrams.lean#L285) | `CubicalDiagrams.lift_coordinate` | `base/overlay/ProofBench/Research/CubicalDiagrams.lean:285` | `graph` |
| Theorem 5.2 | [Realize arbitrary natural face weights on a finite edgeless host](base/overlay/ProofBench/Research/CubicalDiagrams.lean#L337) | `CubicalDiagrams.exists_edgeless_realization` | `base/overlay/ProofBench/Research/CubicalDiagrams.lean:337` | `graph` |
| Section 5 | [Opposite two-coordinate corner order sum](base/overlay/ProofBench/Research/CubicalExamples.lean#L62) | `CubicalDiagrams.Square.opposite_order_sum` | `base/overlay/ProofBench/Research/CubicalExamples.lean:62` | `graph` |
| Corollary 5.3 | [Cut bound activated by two large inclusive corners](base/overlay/ProofBench/Research/LargeCornerCuts.lean#L46) | `CubicalDiagrams.large_corner_cut` | `base/overlay/ProofBench/Research/LargeCornerCuts.lean:46` | `graph` |
| Theorem 6.1 | [Finite-graph 3D Corner Lemma (source Lemma 4.14)](base/overlay/ProofBench/Research/PaperKeyBridge.lean#L55) | `PaperCorner.key_lemma_4_14` | `base/overlay/ProofBench/Research/PaperKeyBridge.lean:55` | `cycle` |
| Theorem 6.1 | [Internal finite-separation version](base/overlay/ProofBench/Research/KeyCornerLemma.lean#L79) | `CornerSection.key_lemma_4_14` | `base/overlay/ProofBench/Research/KeyCornerLemma.lean:79` | `cycle` |
| Example 6.2 | [All-crossing C24 diagram is a 2-flower](base/overlay/ProofBench/Research/FlowerCycle24.lean#L149) | `CornerSection.Cycle24.flower` | `base/overlay/ProofBench/Research/FlowerCycle24.lean:149` | `cycle` |
| Example 6.3 | [Uniform partitions of the mixed diagram](base/checks/NontrivialNestedCycle.lean#L44) | `CornerSection.NestedCycle24.partitions` | `base/checks/NontrivialNestedCycle.lean:44` | `cycle` |
| Example 6.3 | [Mixed C24 diagram has no flower at any threshold](probes/CycleAssertions.lean#L117) | `ManuscriptCycleCheck.mixed_not_flower` | `probes/CycleAssertions.lean:117` | `cycle` |
| Example 6.3 | [Uniform mixed diagram without a 2-flower](probes/CycleAssertions.lean#L123) | `ManuscriptCycleCheck.mixed_uniform_without_two_flower` | `probes/CycleAssertions.lean:123` | `cycle` |

The count identifies complementary sides, retains all cube vertex labels, and treats a family as an unordered set of four distinct cuts. The star is fixed. Its three separations and the external cover may vary. The finite-graph 4.14 statement and both cycle diagrams use the graph-separation definitions given in the pinned project. For the mixed diagram the manuscript uses the special case at threshold two.
