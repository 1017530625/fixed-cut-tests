import ProofBench.PROBLEMS.P118.StarCutCertificate

namespace ManuscriptGraphCheck

open CornerLemma CornerCutLowerBound ConnectedCornerTests SeparationDiagrams Finset

set_option maxRecDepth 40000 in
set_option maxHeartbeats 25000000 in
/-- A nontrivial side counts the star centre once and each split matching edge once. -/
theorem star_order_nontrivial : ∀ (j : Fin 8) (A : Finset Vertex),
    A.Nonempty → (univ \ A).Nonempty →
    (lift (diagram j) A).order =
      1 + ((AlternatingMatching j).filter fun e => (e ∩ A).Nonempty ∧ (e \ A).Nonempty).card := by
  decide

theorem star_order_trivial : ∀ j : Fin 8,
    (lift (diagram j) (∅ : Finset Vertex)).order = 0 ∧
    (lift (diagram j) (univ : Finset Vertex)).order = 0 := by decide

#check star_order_nontrivial
#check star_order_trivial
#print axioms ManuscriptGraphCheck.star_order_nontrivial
#print axioms ManuscriptGraphCheck.star_order_trivial

end ManuscriptGraphCheck
