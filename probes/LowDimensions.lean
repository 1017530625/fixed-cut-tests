import ProofBench.Research.CubicalExamples
import ProofBench.Research.LargeCornerCuts

namespace ManuscriptGraphCheck

#check CubicalDiagrams.cutValue_of_isEmpty
#check CubicalDiagrams.Square.corner_sides
#check CubicalDiagrams.Square.opposite_order_sum
#check CubicalDiagrams.Square.opposite_corner_card_eq
#check CubicalDiagrams.large_corner_cut
#print CubicalDiagrams.Unbreakable
#print CubicalDiagrams.region
#print CubicalDiagrams.largeCorners

theorem zero_threshold {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    {G : SimpleGraph X} (D : I → G.Separation) (A : Finset (CubicalDiagrams.Corner I)) :
    0 ≤ CubicalDiagrams.cutValue (CubicalDiagrams.weight D) A := Nat.zero_le _

#check zero_threshold
#print axioms CubicalDiagrams.cutValue_of_isEmpty
#print axioms CubicalDiagrams.Square.corner_sides
#print axioms CubicalDiagrams.Square.opposite_order_sum
#print axioms CubicalDiagrams.Square.opposite_corner_card_eq
#print axioms CubicalDiagrams.large_corner_cut
#print axioms ManuscriptGraphCheck.zero_threshold

end ManuscriptGraphCheck
