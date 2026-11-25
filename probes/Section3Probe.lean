import ProofBench.PROBLEMS.P118.GeneralGraphCuts

namespace ManuscriptSectionThreeProbe

open CornerLemma CornerArbitraryCuts

#check CornerArbitraryCuts.sufficient_iff_complete
#check CornerArbitraryCuts.ring_sufficient_iff_complete
#check CornerArbitraryCuts.cut_eq_matching_edge
#check CornerArbitraryCuts.sufficient_card_ge_four
#check CornerArbitraryCuts.detected_card_zero_or_two
#check CornerArbitraryCuts.nine_designs_complete

#print CornerArbitraryCuts.Complete
#print CornerArbitraryCuts.detected
#print CubeTransversals.Sufficient
#print CoverAware.SufficientAt

example (S : Finset (Finset Vertex)) : CubeTransversals.Sufficient S ↔
    ∀ j : Fin 8, ∃ A ∈ S, j ∈ detected A := sufficient_iff_complete S

example (q : Fin 4) (S : Finset (Finset Vertex)) :
    CoverAware.SufficientAt (CoverAware.ring q) S ↔
      ∀ b : Bool, ∃ A ∈ S, CoverAware.index q b ∈ detected A :=
  ring_sufficient_iff_complete q S

private def corner (n : Nat) : Vertex := fun i => n.testBit (2 - i.val)

/-- The four cube edges differing in the last binary coordinate. -/
def parallelEdges : Finset (Finset Vertex) :=
  {{corner 0, corner 1}, {corner 2, corner 3},
   {corner 4, corner 5}, {corner 6, corner 7}}

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem parallelEdges_optimal : parallelEdges.card = 4 ∧
    CubeTransversals.Sufficient parallelEdges ∧
    ∀ S : Finset (Finset Vertex), CubeTransversals.Sufficient S → parallelEdges.card ≤ S.card := by
  have four : parallelEdges.card = 4 := by decide
  have hits : Complete parallelEdges := by
    unfold Complete
    decide
  refine ⟨four, (sufficient_iff_complete _).mpr hits, ?_⟩
  intro S sufficient
  simpa only [four] using sufficient_card_ge_four S sufficient

#check parallelEdges_optimal
#print axioms CornerArbitraryCuts.sufficient_iff_complete
#print axioms CornerArbitraryCuts.ring_sufficient_iff_complete
#print axioms CornerArbitraryCuts.cut_eq_matching_edge
#print axioms CornerArbitraryCuts.sufficient_card_ge_four
#print axioms CornerArbitraryCuts.detected_card_zero_or_two
#print axioms CornerArbitraryCuts.nine_designs_complete
#print axioms ManuscriptSectionThreeProbe.parallelEdges_optimal

end ManuscriptSectionThreeProbe
