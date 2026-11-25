import ProofBench.PROBLEMS.P118.CutRequirements
import ProofBench.PROBLEMS.P118.ConnectedTests

/-! The fixed four-vertex tree detects the exact failure of arbitrary corner cuts. -/
namespace CornerArbitraryCuts

open Finset CornerLemma CornerCutLowerBound SeparationDiagrams

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

/-- A failure at threshold two on the prescribed star diagram is exactly a
rejected witness. Cuts which do not separate the cover carry no requirement. -/
theorem star_test_iff : ∀ (j : Fin 8) (A : Finset Vertex),
    ((∃ r ∈ ConnectedCornerTests.cover j, r ∈ A) →
     (∃ r ∈ ConnectedCornerTests.cover j, r ∉ A) →
     2 ≤ (lift (ConnectedCornerTests.diagram j) A).order) ↔
    j ∉ detected A := by
  decide

/-- Every universally sufficient test family on this one specified tree
rejects all eight matching witnesses, even when the tests have arbitrary sides. -/
theorem complete_of_on_star (S : Finset (Finset Vertex))
    (works : ConnectedCornerTests.SufficientOn ConnectedCornerTests.host S) :
    Complete S := by
  classical
  intro j
  by_contra! missed
  obtain ⟨_, _, coords, cover, singles, _, obstruction⟩ := ConnectedCornerTests.star_obstruction j
  apply obstruction (works (ConnectedCornerTests.diagram j) (ConnectedCornerTests.cover j) 2
    coords cover (fun r hr => (singles r hr).ge) ?_)
  intro A hA
  exact (star_test_iff j A).mpr (missed A hA)

end CornerArbitraryCuts
