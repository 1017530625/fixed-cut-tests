import ProofBench.PROBLEMS.P118.ArbitraryCuts
import ProofBench.PROBLEMS.P118.StarCutCertificate
import ProofBench.PROBLEMS.P118.ArbitraryCutCensus

/-! Unrestricted cut tests on finite graph separations, and one balanced optimal design. -/
namespace CornerArbitraryCuts

open Finset CornerLemma ConnectedCornerTests

theorem graph_iff_complete (S : Finset (Finset Vertex)) :
    GraphCornerTests.Sufficient S ↔ Complete S :=
  (GraphCornerTests.iff_weighted S).trans (sufficient_iff_complete S)

/-- Universal validity on the one four-vertex star characterizes validity on all finite graphs. -/
theorem on_star_iff_complete (S : Finset (Finset Vertex)) :
    SufficientOn host S ↔ Complete S :=
  ⟨complete_of_on_star S, fun complete => (graph_iff_complete S).mpr complete (Fin 4) host⟩

theorem connected_iff_complete (S : Finset (Finset Vertex)) :
    ConnectedSufficient S ↔ Complete S := by
  constructor
  · intro works
    exact (on_star_iff_complete S).mp (works (Fin 4) host (SimpleGraph.connected_starGraph _))
  · intro complete X _ _ G _
    exact (graph_iff_complete S).mpr complete X G

/-- A counted family is exactly a sufficient family of four canonical unordered cuts. -/
theorem mem_minimumFamilies_iff_sufficient {S : Finset (Finset Vertex)} :
    S ∈ minimumFamilies ↔ S ⊆ canonicalSides ∧ S.card = 4 ∧ CubeTransversals.Sufficient S := by
  rw [mem_minimumFamilies, sufficient_iff_complete]

theorem sufficient_card_ge_four (S : Finset (Finset Vertex)) (h : CubeTransversals.Sufficient S) :
    4 ≤ S.card :=
  complete_card_ge_four S ((sufficient_iff_complete S).mp h)

/-- In a given ring the 144 counted families are precisely its minimum sufficient families. -/
theorem mem_ringMinimumFamilies_iff_sufficient {q : Fin 4} {S : Finset (Finset Vertex)} :
    S ∈ ringMinimumFamilies q ↔
      S ⊆ canonicalSides ∧ S.card = 2 ∧ CoverAware.SufficientAt (CoverAware.ring q) S := by
  rw [mem_ringMinimumFamilies, ring_sufficient_iff_complete]
  rfl

theorem ring_sufficient_card_ge_two (q : Fin 4) (S : Finset (Finset Vertex))
    (h : CoverAware.SufficientAt (CoverAware.ring q) S) : 2 ≤ S.card :=
  completeAt_card_ge_two q S ((ring_sufficient_iff_complete q S).mp h)

set_option maxRecDepth 10000

private def corner (n : ℕ) : Vertex := fun i => n.testBit (2 - i.val)

/-- Vertex numbers are binary. All four bipartitions split the eight corners evenly. -/
def balancedDesign : Finset (Finset Vertex) :=
  {{corner 1, corner 2, corner 3, corner 5},
   {corner 1, corner 3, corner 4, corner 5},
   {corner 2, corner 3, corner 5, corner 7},
   {corner 3, corner 4, corner 5, corner 7}}

theorem balanced_sufficient :
    balancedDesign.card = 4 ∧ (∀ A ∈ balancedDesign, A.card = 4) ∧
      CubeTransversals.Sufficient balancedDesign := by
  refine ⟨by decide, by decide, (sufficient_iff_complete _).mpr ?_⟩
  unfold Complete
  decide

end CornerArbitraryCuts
