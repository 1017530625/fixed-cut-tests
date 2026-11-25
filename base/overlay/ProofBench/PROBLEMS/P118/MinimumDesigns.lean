import ProofBench.PROBLEMS.P118.CubeTransversals
import Mathlib.Data.Finset.Powerset

namespace CubeMinimumDesigns
open CornerLemma CornerCutLowerBound CubeTransversals Finset

/-- Vertex numbers use the most-significant bit for coordinate zero. -/
private def vertex (u : Nat) : Vertex := fun i => u.testBit (2 - i.val)
private def edge (u v : Nat) : Finset Vertex := {vertex u, vertex v}

private def allEdges : Finset (Finset Vertex) :=
  {edge 0 1, edge 0 2, edge 0 4, edge 1 3, edge 1 5, edge 2 3,
   edge 2 6, edge 3 7, edge 4 5, edge 4 6, edge 5 7, edge 6 7}

/-- Three parallel edge classes followed by the boundaries of the six square faces. -/
def nineDesigns : Finset (Finset (Finset Vertex)) :=
  {{edge 0 4, edge 1 5, edge 2 6, edge 3 7},
   {edge 0 2, edge 1 3, edge 4 6, edge 5 7},
   {edge 0 1, edge 2 3, edge 4 5, edge 6 7},
   {edge 0 1, edge 0 2, edge 1 3, edge 2 3},
   {edge 4 5, edge 4 6, edge 5 7, edge 6 7},
   {edge 0 1, edge 0 4, edge 1 5, edge 4 5},
   {edge 2 3, edge 2 6, edge 3 7, edge 6 7},
   {edge 0 2, edge 0 4, edge 2 6, edge 4 6},
   {edge 1 3, edge 1 5, edge 3 7, edge 5 7}}

private theorem everyEdge : ∀ u v : Vertex, Adj u v → {u, v} ∈ allEdges := by decide

private instance hitsDecidable (S : Finset (Finset Vertex)) : Decidable (HitsAll S) := by
  unfold HitsAll
  infer_instance

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private theorem fourTable :
    ((allEdges.powersetCard 4).filter HitsAll) = nineDesigns := by decide

/-- The classification uses the same vertex-pair sides and meaning of sufficient
as the two directions of the matching-transversal theorem. -/
theorem sufficient_four_iff (S : Finset (Finset Vertex)) (card : S.card = 4)
    (pairs : ∀ A ∈ S, AdjacentSide A) : Sufficient S ↔ S ∈ nineDesigns := by
  rw [sufficient_iff_hitsAll S pairs, ← fourTable, mem_filter]
  have subset : S ⊆ allEdges := by
    intro A hA
    obtain ⟨u, v, huv, rfl⟩ := pairs A hA
    exact everyEdge u v huv
  exact ⟨fun hit => ⟨mem_powersetCard.mpr ⟨subset, card⟩, hit⟩, And.right⟩

theorem listed_design_is_sufficient (S : Finset (Finset Vertex)) (listed : S ∈ nineDesigns) :
    S.card = 4 ∧ Sufficient S := by
  rw [← fourTable, mem_filter] at listed
  exact ⟨(mem_powersetCard.mp listed.1).2, sufficient_of_hitsAll S listed.2⟩

theorem at_least_four_tests (S : Finset (Finset Vertex))
    (pairs : ∀ A ∈ S, AdjacentSide A) (sufficient : Sufficient S) : 4 ≤ S.card := by
  by_contra! small
  obtain ⟨lam, R, coords, cov, singles, checks, bad⟩ :=
    three_tests_insufficient S (by omega) pairs
  exact bad (sufficient lam 1 R coords cov singles (fun A hA _ _ => checks A hA))

theorem count_minimum_designs : nineDesigns.card = 9 := by decide

end CubeMinimumDesigns
