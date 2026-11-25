import ProofBench.PROBLEMS.P118.CoverAware

/-! Which of the eight integral witnesses are rejected by a corner cut? -/
namespace CornerArbitraryCuts

open Finset CornerLemma CornerCutLowerBound

/-- The pair of sides of the cut must separate the six matching vertices,
and every matched edge must lie entirely on one side. -/
def detected (A : Finset Vertex) : Finset (Fin 8) :=
  univ.filter fun j =>
    let M := AlternatingMatching j
    let R := M.biUnion id
    (R ∩ A).Nonempty ∧ (R \ A).Nonempty ∧
      ∀ e ∈ M, e ⊆ A ∨ Disjoint e A

/-- Every one of the eight witnesses is rejected by some selected cut. -/
def Complete (S : Finset (Finset Vertex)) : Prop :=
  ∀ j : Fin 8, ∃ A ∈ S, j ∈ detected A

end CornerArbitraryCuts
