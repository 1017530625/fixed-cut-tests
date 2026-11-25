import ProofBench.PROBLEMS.P118.GeneralGraphCuts
import ProofBench.Research.CubicalExamples
import ProofBench.Research.LargeCornersP118

namespace ManuscriptGraphCheck

#check ConnectedCornerTests.star_obstruction
#check ConnectedCornerTests.centre_weight
#check CornerArbitraryCuts.star_test_iff
#check CornerArbitraryCuts.on_star_iff_complete
#check CornerArbitraryCuts.connected_iff_complete
#check CornerArbitraryCuts.graph_iff_complete
#check GraphCornerTests.iff_weighted
#print ConnectedCornerTests.host
#print ConnectedCornerTests.SufficientOn

#check CubicalDiagrams.exists_face_walk
#check CubicalDiagrams.mem_crossingFaces_iff
#check CubicalDiagrams.inFace_iff
#check CubicalDiagrams.mem_aggregate_iff
#check CubicalDiagrams.lift
#check CubicalDiagrams.order_lift
#check CubicalDiagrams.aggregate_coordinateSide
#check CubicalDiagrams.lift_coordinate
#check CubicalDiagrams.coordinate_order
#check CubicalDiagrams.exists_edgeless_realization
#check CubicalDiagrams.cutValue_of_isEmpty
#check CubicalDiagrams.P118.weight_eq
#check CubicalDiagrams.P118.aggregate_eq
#check CubicalDiagrams.P118.lift_eq
#check CubicalDiagrams.P118.cutValue_eq
#check CubicalDiagrams.P118.flower_of_order_bounds
#check CubicalDiagrams.large_corner_cut
#check CubicalDiagrams.P118.flower_of_large_corner_cover

open CornerArbitraryCuts ConnectedCornerTests

theorem star_iff_all_graphs (S : Finset (Finset CornerLemma.Vertex)) :
    SufficientOn host S ↔ GraphCornerTests.Sufficient S :=
  (on_star_iff_complete S).trans (graph_iff_complete S).symm

theorem missed_matching_on_star (j : Fin 8) (S : Finset (Finset CornerLemma.Vertex))
    (missed : ∀ A ∈ S, j ∉ detected A) :
    (∀ A ∈ S, (∃ r ∈ cover j, r ∈ A) → (∃ r ∈ cover j, r ∉ A) →
      2 ≤ (SeparationDiagrams.lift (diagram j) A).order) ∧
    ¬ CornerLemma.IsFlower (SeparationDiagrams.weight (diagram j)) 2 := by
  obtain ⟨_, _, _, _, _, _, bad⟩ := star_obstruction j
  exact ⟨fun A hA => (star_test_iff j A).mpr (missed A hA), bad⟩

/-- Selecting three indices is enough to apply the released order identity to that triple. -/
theorem order_selected_triple {I X : Type*} [Fintype X] [DecidableEq X]
    {G : SimpleGraph X} (D : I → G.Separation) (select : Fin 3 → I) (A : Finset CornerLemma.Vertex) :
    (CubicalDiagrams.lift (D ∘ select) A).order =
      CornerLemma.cutValue (CubicalDiagrams.weight (D ∘ select)) A :=
  (CubicalDiagrams.order_lift (D ∘ select) A).trans (CubicalDiagrams.P118.cutValue_eq _ A)

#check star_iff_all_graphs
#check missed_matching_on_star
#check order_selected_triple

#print axioms ConnectedCornerTests.star_obstruction
#print axioms ConnectedCornerTests.centre_weight
#print axioms CornerArbitraryCuts.star_test_iff
#print axioms CornerArbitraryCuts.on_star_iff_complete
#print axioms CornerArbitraryCuts.connected_iff_complete
#print axioms CornerArbitraryCuts.graph_iff_complete
#print axioms GraphCornerTests.iff_weighted
#print axioms CubicalDiagrams.exists_face_walk
#print axioms CubicalDiagrams.mem_crossingFaces_iff
#print axioms CubicalDiagrams.inFace_iff
#print axioms CubicalDiagrams.mem_aggregate_iff
#print axioms CubicalDiagrams.lift
#print axioms CubicalDiagrams.order_lift
#print axioms CubicalDiagrams.aggregate_coordinateSide
#print axioms CubicalDiagrams.lift_coordinate
#print axioms CubicalDiagrams.coordinate_order
#print axioms CubicalDiagrams.exists_edgeless_realization
#print axioms CubicalDiagrams.cutValue_of_isEmpty
#print axioms CubicalDiagrams.P118.weight_eq
#print axioms CubicalDiagrams.P118.aggregate_eq
#print axioms CubicalDiagrams.P118.lift_eq
#print axioms CubicalDiagrams.P118.cutValue_eq
#print axioms CubicalDiagrams.P118.flower_of_order_bounds
#print axioms CubicalDiagrams.large_corner_cut
#print axioms CubicalDiagrams.P118.flower_of_large_corner_cover
#print axioms ManuscriptGraphCheck.star_iff_all_graphs
#print axioms ManuscriptGraphCheck.missed_matching_on_star
#print axioms ManuscriptGraphCheck.order_selected_triple

end ManuscriptGraphCheck
