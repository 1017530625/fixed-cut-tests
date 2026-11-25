import ProofBench.PROBLEMS.P118.GeneralGraphCuts

namespace ManuscriptParallelDirections

open CornerLemma CornerArbitraryCuts CornerCutLowerBound

private def flipAt (i : Fin 3) (u : Vertex) : Vertex :=
  fun j => if j = i then !(u j) else u j

/-- Each unordered edge is included once, using its two endpoints as the chosen side. -/
def parallelEdges (i : Fin 3) : Finset (Finset Vertex) :=
  Finset.univ.image fun u : Vertex => ({u, flipAt i u} : Finset Vertex)

set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

theorem cardinality : ∀ i : Fin 3, (parallelEdges i).card = 4 := by decide

/-- Each witness has exactly one edge in this direction, and that edge detects the witness. -/
theorem detects_unique_edge : ∀ (i : Fin 3) (j : Fin 8),
    ((AlternatingMatching j) ∩ parallelEdges i).card = 1 ∧
      ∃ e ∈ parallelEdges i, e ∈ AlternatingMatching j ∧ j ∈ detected e := by decide

theorem optimal (i : Fin 3) : (parallelEdges i).card = 4 ∧
    CubeTransversals.Sufficient (parallelEdges i) ∧
    ∀ S : Finset (Finset Vertex), CubeTransversals.Sufficient S → (parallelEdges i).card ≤ S.card := by
  refine ⟨cardinality i, (sufficient_iff_complete _).mpr ?_, ?_⟩
  · intro j
    obtain ⟨e, he, _, hj⟩ := (detects_unique_edge i j).2
    exact ⟨e, he, hj⟩
  · intro S sufficient
    simpa only [cardinality] using sufficient_card_ge_four S sufficient

#check detects_unique_edge
#check optimal
#print axioms ManuscriptParallelDirections.detects_unique_edge
#print axioms ManuscriptParallelDirections.optimal

end ManuscriptParallelDirections
